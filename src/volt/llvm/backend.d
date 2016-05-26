// Copyright © 2012, Jakob Bornecrantz.  All rights reserved.
// See copyright notice in src/volt/license.d (BOOST ver. 1.0).
module volt.llvm.backend;

import io = watt.io.std;
import watt.conv : toStringz;

import volt.errors;
import volt.interfaces;
import ir = volt.ir.ir;
import volt.ir.util;
import volt.lowerer.llvmlowerer;
import volt.token.location;

import lib.llvm.core;
import lib.llvm.analysis;
import lib.llvm.bitreader;
import lib.llvm.bitwriter;
import lib.llvm.targetmachine;
import lib.llvm.executionengine;
import lib.llvm.c.Target;
import lib.llvm.c.Linker;
import lib.llvm.c.Initialization;

import volt.llvm.state;
import volt.llvm.toplevel;


/**
 * Main interface for the @link volt.interfaces.Driver
 * Driver@endlink to the llvm backend.
 */
class LlvmBackend : Backend
{
protected:
	class CompiledFunctionStore
	{
		ir.Module m;
		LanguagePass lp;
		ir.Function func;

		this(LanguagePass lp, ir.Module m, ir.Function func)
		{
			this.lp = lp;
			this.m = m;
			this.func = func;
		}

		ir.Constant getConstant(ir.Constant[] args)
		{
			auto state = new VoltState(lp, m);
			scope (exit) {
				state.close();
			}
			try {
				state.compile(m);
			} catch (object.Throwable t) {
				throw t;
			}

			// Initialise the JIT engine.
			LLVMExecutionEngineRef ee = null;
			string error;
			if (LLVMCreateMCJITCompilerForModule(&ee, state.mod, null, 0, error)) {
				assert(false, "JIT CREATION FAILED: " ~ error); // TODO: Real error.
			}
			LLVMValueRef llvmfunc;
			if (LLVMFindFunction(ee, toStringz(func.mangledName), &llvmfunc) != 0) {
				assert(false, "FIND FUNCTION FAILED"); // TODO: Real error.
			}

			// Turn the arguments into something LLVM understands.
			LLVMGenericValueRef[] genargs;
			if (args.length > 0) {
				genargs = new LLVMGenericValueRef[](args.length);
			}
			auto t = LLVMInt32TypeInContext(state.context);
			foreach (i, arg; args) {
				genargs[i] = LLVMCreateGenericValueOfInt(t, arg.u._ulong, true);
			}

			// Run the function using LLVM.
			auto genv = LLVMRunFunction(ee, llvmfunc, cast(uint)genargs.length, genargs.ptr);
			scope (exit) LLVMDisposeGenericValue(genv);

			// Dispose of the LLVM arguments.
			foreach (genarg; genargs) {
				LLVMDisposeGenericValue(genarg);
			}

			return llvmGenericToConstant(func.location, genv, func.type.ret);
		}
	}
	ir.Constant llvmGenericToConstant(Location loc, LLVMGenericValueRef genv, ir.Type type)
	{
		auto ptype = cast(ir.PrimitiveType)type;
		if (ptype is null) {
			assert(false, "NON PRIMITIVE RETURN");  // TODO: Real error.
		}
		switch (ptype.type) with (ir.PrimitiveType.Kind) {
		case Byte:
			auto val = cast(byte)LLVMGenericValueToInt(genv, true);
			return buildConstantByte(loc, val);
		case Ubyte:
			auto val = cast(ubyte)LLVMGenericValueToInt(genv, false);
			return buildConstantUbyte(loc, val);
		case Short:
			auto val = cast(short)LLVMGenericValueToInt(genv, true);
			return buildConstantShort(loc, val);
		case Ushort:
			auto val = cast(ushort)LLVMGenericValueToInt(genv, false);
			return buildConstantUshort(loc, val);
		case Int:
			auto val = cast(int)LLVMGenericValueToInt(genv, true);
			return buildConstantInt(loc, val);
		case Uint:
			auto val = cast(uint)LLVMGenericValueToInt(genv, false);
			return buildConstantUint(loc, val);
		case Long:
			auto val = cast(long)LLVMGenericValueToInt(genv, true);
			return buildConstantLong(loc, val);
		case Ulong:
			auto val = cast(ulong)LLVMGenericValueToInt(genv, false);
			return buildConstantUlong(loc, val);
		default:
			assert(false, "UNHANDLED PRIMITIVE TYPE");  // TODO: Real error.
		}
	}

protected:
	LanguagePass lp;

	TargetType mTargetType;
	string mFilename;
	bool mDump;
	CompiledFunctionStore[ir.NodeID] mCompiledFunctions;

public:
	this(LanguagePass lp)
	{
		this.lp = lp;
		this.mDump = lp.settings.internalDebug;

		auto passRegistry = LLVMGetGlobalPassRegistry();

		LLVMInitializeCore(passRegistry);
		LLVMInitializeAnalysis(passRegistry);
		LLVMInitializeTarget(passRegistry);

		if (lp.settings.arch == Arch.X86 ||
		    lp.settings.arch == Arch.X86_64) {
			LLVMInitializeX86TargetInfo();
			LLVMInitializeX86Target();
			LLVMInitializeX86TargetMC();
			LLVMInitializeX86AsmPrinter();
		}

		LLVMLinkInMCJIT();
	}

	override void close()
	{
		mFilename = null;
		// XXX: Shutdown LLVM.
	}

	override TargetType[] supported()
	{
		return [TargetType.LlvmBitcode];
	}

	override void setTarget(string filename, TargetType type)
	{
		mFilename = filename;
		mTargetType = type;
	}

	override void compile(ir.Module m)
	in {
		assert(mFilename !is null);
	}
	body {
		scope (exit) {
			mFilename = null;
		}

		auto state = new VoltState(lp, m);
		auto mod = state.mod;
		scope (exit) {
			state.close();
			mFilename = null;
		}

		if (mDump) {
			io.output.writefln("Compiling module");
		}

		llvmModuleCompile(state, m);

		if (mDump) {
			io.output.writefln("Dumping module");
			LLVMDumpModule(mod);
		}

		string result;
		auto failed = LLVMVerifyModule(mod, result);
		if (failed) {
			LLVMDumpModule(mod);
			io.error.writefln("%s", result);
			throw panic("Module verification failed.");
		}

		LLVMWriteBitcodeToFile(mod, mFilename);
	}

	override Driver.CompiledDg hostCompile(ir.Module m, ir.Function func)
	{
		auto lowerer = new LlvmLowerer(lp);
		lowerer.transform(m);
		auto p = func.uniqueId in mCompiledFunctions;
		if (p !is null) {
			version (Volt) {
				return p.getConstant;
			} else {
				return &p.getConstant;
			}
		}

		auto cfstore = new CompiledFunctionStore(lp, m, func);
		mCompiledFunctions[func.uniqueId] = cfstore;

		version (Volt) {
			return cfstore.getConstant;
		} else {
			return &cfstore.getConstant;
		}
	}

protected:
	void llvmModuleCompile(VoltState state, ir.Module m)
	{
		try {
			state.compile(m);
		} catch (object.Throwable t) {
			if (mDump) {
				version (Volt) {
					io.output.writefln("Caught \"???\" dumping module:");
				} else {
					io.output.writefln("Caught \"%s\" dumping module:", t.classinfo.name);
				}
				LLVMDumpModule(state.mod);
			}
			throw t;
		}
	}
}

LLVMModuleRef loadModule(LLVMContextRef ctx, string filename)
{
	string msg;

	auto mod = LLVMModuleFromFileInContext(ctx, filename, msg);
	if (msg !is null && mod !is null) {
		io.error.writefln("%s", msg); // Warnings
	}
	if (mod is null) {
		throw makeNoLoadBitcodeFile(filename, msg);
	}

	return mod;
}

/**
 * Helper function to link several LLVM modules together.
 */
void linkModules(string output, string[] inputs...)
{
	assert(inputs.length > 0);

	LLVMModuleRef dst, src;
	LLVMContextRef ctx;
	string msg;

	if (inputs.length == 1 &&
	    output == inputs[0]) {
		return;
	}

	ctx = LLVMContextCreate();
	scope (exit) {
		LLVMContextDispose(ctx);
	}

	dst = loadModule(ctx, inputs[0]);
	scope (exit) {
		LLVMDisposeModule(dst);
	}

	foreach (filename; inputs[1 .. $]) {
		src = loadModule(ctx, filename);

		auto ret = LLVMLinkModules2(dst, src);
		if (ret) {
			throw makeNoLinkModule(filename, msg);
		}
	}

	auto ret = LLVMWriteBitcodeToFile(dst, output);
	if (ret) {
		throw makeNoWriteBitcodeFile(output, msg);
	}
}

void writeObjectFile(Settings settings, string output, string input)
{
	auto arch = archList[settings.arch];
	auto triple = tripleList[settings.platform][settings.arch];
	auto layout = layoutList[settings.platform][settings.arch];
	if (arch is null || triple is null || layout is null) {
		throw makeArchNotSupported();
	}

	// Need a context to load the module into.
	auto ctx = LLVMContextCreate();
	scope (exit) {
		LLVMContextDispose(ctx);
	}


	// Load the module from file.
	auto mod = loadModule(ctx, input);
	scope (exit) {
		LLVMDisposeModule(mod);
	}


	// Load the target mc/assmbler.
	// Doesn't need to disposed.
	LLVMTargetRef target = LLVMGetTargetFromName(arch);


	// Create target machine used to hold all of the settings.
	auto machine = LLVMCreateTargetMachine(
		target, triple, "", "",
		LLVMCodeGenOptLevel.Default,
		LLVMRelocMode.Default,
		LLVMCodeModel.Default);
	scope (exit) {
		LLVMDisposeTargetMachine(machine);
	}


	// Write the module to the file
	string msg;
	auto ret = LLVMTargetMachineEmitToFile(
		machine, mod, output,
		LLVMCodeGenFileType.Object, msg) != 0;

	if (msg !is null && !ret) {
		io.error.writefln("%s", msg); // Warnings
	}
	if (ret) {
		throw makeNoWriteObjectFile(output, msg);
	}
}
