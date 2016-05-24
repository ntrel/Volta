// Copyright © 2016, Jakob Bornecrantz.  All rights reserved.
// See copyright notice in src/volt/license.d (BOOST ver. 1.0).
module volt.semantic.lifter;

import ir = volt.ir.ir;
import ircopy = volt.ir.copy;
import volt.ir.util;

import volt.interfaces;
import volt.errors;


/**
 * IR Lifter, aka Liftertron3000, copies and does transformations on IR.
 *
 * This is the base class providing utility functions and a common interface
 * for users. One reason for lifting is that the target we are compiling for
 * is not the same as for the compiler is running on, and as such different
 * backend transformations needs to be done on the IR. Extra validation can
 * also be done while copying.
 *
 * Dost thou even lyft brother.
 */
abstract class Lifter
{
public:
	LanguagePass lp;

private:
	ir.Function[ir.NodeID] mStore;
	ir.Module mMod;
	ir.Module[] mMods;

public:
	this(LanguagePass lp)
	{
		this.lp = lp;
	}

	/**
	 * Resets the lifter and clears all cached functions and modules.
	 */
	void reset()
	{
		version (Volt) {
			mStore = [];
		} else {
			mStore = null;
		}
		mMod = null;
		mMods = null;
	}

	/**
	 * Create a new module to store functions in.
	 *
	 * Does not clear the function cache, so functions can refer
	 * to functions in earlier modules.
	 */
	ir.Module newModule()
	{
		mMod = new ir.Module();
		mMod.name = buildQualifiedName(mMod.location, "CTFETESTMODULE");
		mMod.children = new ir.TopLevelBlock();
		mMod.children.location = mMod.location;
		mMods ~= mMod;

		return mMod;
	}

	/**
	 * Lift or returns a cached copy of the given function.
	 */
	ir.Function lift(ir.Function func)
	{
		assert(mMod !is null);

		ir.Function ret;
		if (mStore.get(func.uniqueId, ret)) {
			return ret;
		}

		return doLift(func);
	}

protected:
	/**
	 * Copies the function declration and adds it to the store.
	 *
	 * The body, in and out contracts are left null and will need to be
	 * copied by the caller. Intended to be used as a helper function.
	 */
	ir.Function copyFunction(ir.Function old)
	{
		assert((old.uniqueId in mStore) is null);

		// TODO Need actualize as insted.
		//lp.actualize(old);
		assert(old.isActualized);

		auto func = new ir.Function();
		func.location = old.location;
		func.isResolved = old.isResolved;
		func.isActualized = old.isActualized;
		func.access = old.access;
		func.myScope = copyScope(old.myScope, mMod.myScope, func);
		func.kind = old.kind;
		func.type = new ir.FunctionType(old.type);
		version (Volt) {
			func.params = new old.params[0 .. $];
			func.nestedFunctions = new old.nestedFunctions[0 .. $];
			func.scopeSuccesses = new old.scopeSuccesses[0 .. $];
			func.scopeExits = new old.scopeExits[0 .. $];
			func.scopeFailures = new old.scopeFailures[0 .. $];
		} else {
			func.params = old.params.dup;
			func.nestedFunctions = old.nestedFunctions.dup;
			func.scopeSuccesses = old.scopeSuccesses.dup;
			func.scopeExits = old.scopeExits.dup;
			func.scopeFailures = old.scopeFailures.dup;
		}
		foreach (i, param; old.params) {
			func.params[i] = copyFunctionParam(param, func);
		}
		foreach (i, nfunc; old.nestedFunctions) {
			func.nestedFunctions[i] = copyFunction(nfunc);
		}
		foreach (i, scopeFunc; old.scopeSuccesses) {
			func.scopeSuccesses[i] = copyFunction(scopeFunc);
		}
		foreach (i, scopeFunc; old.scopeExits) {
			func.scopeExits[i] = copyFunction(scopeFunc);
		}
		foreach (i, scopeFunc; old.scopeFailures) {
			func.scopeExits[i] = copyFunction(scopeFunc);
		}
		func.name = old.name;
		func.mangledName = old.mangledName;  // TODO: Prefix
		func.suffix = old.suffix;
		func.outParameter = old.outParameter;
		if (old.inContract !is null) {
			func.inContract = copyBlock(func.myScope, old.inContract);
		}
		if (old.outContract !is null) {
			func.outContract = copyBlock(func.myScope, old.outContract);
		}
		if (old._body !is null) {
			func._body = copyBlock(func.myScope, old._body);
		}
		if (old.thisHiddenParameter !is null) {
			func.thisHiddenParameter = copyVariable(old.thisHiddenParameter);
		}
		if (old.nestedHiddenParameter !is null) {
			func.nestedHiddenParameter = copyVariable(old.nestedHiddenParameter);
		}
		if (old.nestedVariable !is null) {
			func.nestedVariable = copyVariable(old.nestedVariable);
		}
		if (func.nestStruct !is null) {
			throw makeNotAvailableInCTFE(func, "nested functions");
		}
		func.isWeakLink = old.isWeakLink;
		func.vtableIndex = old.vtableIndex;
		func.loadDynamic = old.loadDynamic;
		func.isMarkedOverride = old.isMarkedOverride;
		func.isOverridingInterface = old.isOverridingInterface;
		func.isAbstract = old.isAbstract;
		func.isAutoReturn = old.isAutoReturn;
		func.isLoweredScopeExit = old.isLoweredScopeExit;
		func.isLoweredScopeFailure = old.isLoweredScopeFailure;
		func.isLoweredScopeSuccess = old.isLoweredScopeSuccess;
		mStore[old.uniqueId] = func;
		mMod.children.nodes ~= func;
		return func;
	}

	ir.Node copyNode(ir.Scope parent, ir.Node n)
	{
		switch (n.nodeType) with (ir.NodeType) {
		case BlockStatement: assert(false);
		case IfStatement: return copyIfStatement(parent, cast(ir.IfStatement)n);
		case WhileStatement: return copyWhileStatement(parent, cast(ir.WhileStatement)n);
		case ForStatement: return copyForStatement(parent, cast(ir.ForStatement)n);
		case DoStatement: return copyDoStatement(parent, cast(ir.DoStatement)n);
		case Alias: return copyAlias(cast(ir.Alias)n);
		case FunctionParam: panicAssert(n, false); break;
		case Variable: return copyVariable(cast(ir.Variable)n);
		case ExpStatement: return copyExpStatement(cast(ir.ExpStatement)n);
		default: return ircopy.copyNode(n);  // TODO: Above nodes nested in these nodes.
		}
		assert(false);
	}

	ir.BlockStatement copyBlock(ir.Scope parent, ref ir.BlockStatement old)
	{
		assert(old !is null);
		auto bs = new ir.BlockStatement();
		version (Volt) {
			bs.statements = new old.statements[0 .. $];
		} else if (old.statements.length > 0) {
			bs.statements = old.statements.dup;
		}
		bs.myScope = new ir.Scope();

		foreach (ref n; bs.statements) {
			copyNode(bs.myScope, n);
		}

		foreach (k, v; old.myScope.symbols) {
			bs.myScope.symbols[k] = copyStore(parent, v);
		}

		return bs;
	}

	ir.ExpStatement copyExpStatement(ir.ExpStatement old)
	{
		auto es = new ir.ExpStatement();
		es.location = old.location;
		es.exp = ircopy.copyExp(old.exp);
		return es;
	}

	ir.IfStatement copyIfStatement(ir.Scope parent, ir.IfStatement old)
	{
		auto ifs = new ir.IfStatement();
		ifs.location = old.location;
		ifs.exp = ircopy.copyExp(old.exp);
		ifs.thenState = copyBlock(parent, old.thenState);
		if (old.elseState !is null) {
			old.elseState = copyBlock(parent, old.elseState);
		}
		ifs.autoName = old.autoName;
		return ifs;
	}

	ir.WhileStatement copyWhileStatement(ir.Scope parent, ir.WhileStatement old)
	{
		auto ws = new ir.WhileStatement();
		ws.location = old.location;
		ws.condition = ircopy.copyExp(old.condition);
		ws.block = copyBlock(parent, old.block);
		return ws;
	}

	ir.DoStatement copyDoStatement(ir.Scope parent, ir.DoStatement old)
	{
		auto ws = new ir.DoStatement();
		ws.location = old.location;
		ws.condition = ircopy.copyExp(old.condition);
		ws.block = copyBlock(parent, old.block);
		return ws;
	}

	ir.ForStatement copyForStatement(ir.Scope parent, ir.ForStatement old)
	{
		auto fs = new ir.ForStatement();
		fs.location = old.location;
		if (old.initVars.length > 0) {
			fs.initVars = new ir.Variable[](old.initVars.length);
			foreach (i; 0 .. old.initVars.length) {
				fs.initVars[i] = copyVariable(old.initVars[i]);
			}
		}
		if (old.initExps.length > 0) {
			fs.initExps = new ir.Exp[](old.initExps.length);
			foreach (i; 0 .. old.initExps.length) {
				fs.initExps[i] = ircopy.copyExp(old.initExps[i]);
			}
		}
		if (old.test !is null) {
			fs.test = ircopy.copyExp(old.test);
		}
		if (old.increments.length > 0) {
			fs.increments = new ir.Exp[](old.increments.length);
			foreach (i; 0 .. fs.increments.length) {
				fs.increments[i] = ircopy.copyExp(old.increments[i]);
			}
		}
		fs.block = copyBlock(parent, old.block);
		return fs;
	}

	/**
	 * Copy a scope. The owner is the _new_ Node that holds this scope.
	 */
	ir.Scope copyScope(ir.Scope old, ir.Scope parent, ir.Node owner)
	{
		auto _scope = new ir.Scope(mMod, old.name);  // TODO: CTFE prefix?
		_scope.anon = old.anon;
		_scope.node = owner;
		if (old.parent !is null) {
			auto oldMod = cast(ir.Module)old.parent.node;
			if (oldMod !is null) {
				_scope.parent = mMod.myScope;
			} else {
				assert(parent !is null);
				_scope.parent = parent;
			}
		}
		foreach (k, v; old.symbols) {
			_scope.symbols[k] = copyStore(_scope, v);
		}
		panicAssert(owner, old.importedModules.length == 0);
		panicAssert(owner, old.importedAccess.length == 0);
		_scope.nestedDepth = old.nestedDepth;
		return _scope;
	}

	ir.Store copyStore(ir.Scope parent, ir.Store old)
	{
		auto store = new ir.Store();
		store.name = old.name;  // TODO: CTFE prefix?
		store.parent = parent;
		store.kind = old.kind;
		store.node = copyNode(parent, old.node);
		if (old.myScope !is null) {
			//store.myScope = copyScope(old.myScope, parent, copyNode(old.myScope.node));
			assert(false);
		}
		if (old.lookScope !is null) {
			//store.lookScope = copyScope(old.lookScope, parent, copyNode(old.lookScope.node));
			assert(false);
		}
		version (Volt) {
			store.functions = new old.functions[0 .. $];
			store.aliases = new old.aliases[0 .. $];
		} else {
			store.functions = old.functions.dup;
			store.aliases = old.aliases.dup;
		}
		foreach (i, func; old.functions) {
			store.functions[i] = copyFunction(func);
		}
		foreach (i, _alias; old.aliases) {
			store.aliases[i] = copyAlias(_alias);
		}
		panicAssert(old.node, old.myAlias is null);
		store.access = old.access;
		return store;
	}

	ir.Alias copyAlias(ir.Alias old)
	{
		auto _alias = new ir.Alias();
		_alias.location = old.location;
		_alias.access = old.access;
		_alias.name = old.name;
		panicAssert(old, old.externAttr is null);
		_alias.type = ircopy.copyType(old.type);
		_alias.id = ircopy.copy(old.id);
		if (old.store !is null) {
			assert(false);
		}
//		_alias.store = copyStore(old.store, null);
		panicAssert(old, old.templateInstance is null);
		return _alias;
	}

	ir.FunctionParam copyFunctionParam(ir.FunctionParam old, ir.Function newFunction)
	{
		auto fparam = new ir.FunctionParam();
		fparam.location = old.location;
		fparam.func = newFunction;
		fparam.index = old.index;
		if (old.assign !is null) {
			fparam.assign = ircopy.copyExp(old.assign);
		}
		fparam.name = old.name;
		fparam.hasBeenNested = old.hasBeenNested;
		return fparam;
	}

	ir.Variable copyVariable(ir.Variable old)
	{
		auto var = new ir.Variable();
		var.location = old.location;
		var.isResolved = old.isResolved;
		var.access = old.access;
		var.type = ircopy.copyType(old.type);
		var.name = old.name;
		var.mangledName = old.mangledName;  // TODO: Remangle?
		if (old.assign !is null) {
			var.assign = ircopy.copyExp(old.assign);
		}
		var.storage = old.storage;
		var.linkage = old.linkage;
		var.isWeakLink = old.isWeakLink;
		var.isExtern = old.isExtern;
		var.isOut = old.isOut;
		var.hasBeenDeclared = old.hasBeenDeclared;
		var.useBaseStorage = old.useBaseStorage;
		var.specialInitValue = old.specialInitValue;
		return var;
	}

	/**
	 * Implemented by child classes, copies the Function into the
	 * current module mMod and applies error checking and transformation
	 * needed for that specific lifter.
	 */
	abstract ir.Function doLift(ir.Function);
}

class CTFELifter : Lifter
{
public:
	this(LanguagePass lp)
	{
		super(lp);
	}


protected:
	override ir.Function doLift(ir.Function old)
	{
		// Copy declaration and add function to store.
		auto func = copyFunction(old);

		// TODO copy in, out and body.

		return func;
	}

	override ir.Function copyFunction(ir.Function old)
	{
		if (old.kind != ir.Function.Kind.Function) {
			throw makeNotAvailableInCTFE(old, "non toplevel functions");
		}
		auto func = super.copyFunction(old);
		func.mangledName = "__CTFE_" ~ func.mangledName;
		return func;
	}
}

/+
void runExp(ref ir.Exp exp)
{
	rexp := cast(ir.RunExp) exp;
	pfix := cast(ir.Postfix) rexp.value;
	func := getFunctionFromPostfix(pfix);
	dlgt := lp.liftFunction(func);
	static is (typeof(dlgt) == ir.Constant delegate(ir.Constant[] args));

	args : ir.Constant[];
	foreach (exp; pfix.arguments) {
		args ~= evaluate(exp);
	}

	dlgt(args);
}
+/
