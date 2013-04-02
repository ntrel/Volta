// Copyright © 2012-2013, Bernard Helyer.  All rights reserved.
// See copyright notice in src/volt/license.d (BOOST ver. 1.0).
module volt.semantic.newreplacer;

import ir = volt.ir.ir;
import volt.ir.util;

import volt.interfaces;
import volt.exceptions;
import volt.token.location;
import volt.visitor.visitor;
import volt.semantic.classify;
import volt.semantic.lookup;
import volt.semantic.mangle;


ir.Function createArrayAllocFunction(Location location, LanguagePass lp, ir.Scope baseScope, ir.ArrayType atype)
{
	auto arrayMangledName = mangle(atype);

	auto ftype = new ir.FunctionType();
	ftype.location = location;
	ftype.ret = copyTypeSmart(location, atype);

	/// @todo Change this sucker to buildFunction
	auto fn = new ir.Function();
	fn.location = location;
	fn.type = ftype;
	fn.name = "__arrayAlloc" ~ arrayMangledName;
	fn.mangledName = fn.name;
	fn.kind = ir.Function.Kind.Function;
	fn.isWeakLink = true;
	fn._body = new ir.BlockStatement();
	fn._body.myScope = new ir.Scope(baseScope, fn._body, fn.name);
	fn._body.location = location;

	auto countVar = addParam(location, fn, buildSizeT(location, lp), "count");

	auto arrayStruct = retrieveArrayStruct(lp, baseScope, location);
	auto allocDgVar = retrieveAllocDg(lp, baseScope, location);

	auto arrayStructVar = buildVarStatSmart(location, fn._body, fn._body.myScope, arrayStruct, "from");

	auto ptrPfix = new ir.Postfix();
	ptrPfix.location = location;
	ptrPfix.op = ir.Postfix.Op.Identifier;
	ptrPfix.child = buildExpReference(location, arrayStructVar, "from");
	ptrPfix.identifier = new ir.Identifier();
	ptrPfix.identifier.location = location;
	ptrPfix.identifier.value = "ptr";

	auto lengthPfix = new ir.Postfix();
	lengthPfix.location = location;
	lengthPfix.op = ir.Postfix.Op.Identifier;
	lengthPfix.child = buildExpReference(location, arrayStructVar, "from");
	lengthPfix.identifier = new ir.Identifier();
	lengthPfix.identifier.location = location;
	lengthPfix.identifier.value = "length";

	auto ptrAssign = new ir.BinOp();
	ptrAssign.location = location;
	ptrAssign.op = ir.BinOp.Type.Assign;
	ptrAssign.left = ptrPfix;
	ptrAssign.right = createAllocDgCall(
		allocDgVar, lp, location, atype.base,
		buildExpReference(location, countVar, "count"), true);

	auto expStatement = new ir.ExpStatement();
	expStatement.location = location;
	expStatement.exp = ptrAssign;

	fn._body.statements ~= expStatement;

	auto lengthAssign = new ir.BinOp();
	lengthAssign.location = location;
	lengthAssign.op = ir.BinOp.Type.Assign;
	lengthAssign.left = lengthPfix;
	lengthAssign.right = buildExpReference(location, countVar, "count");

	expStatement = new ir.ExpStatement();
	expStatement.location = location;
	expStatement.exp = lengthAssign;

	fn._body.statements ~= expStatement;

	auto addrOf = new ir.Unary();
	addrOf.location = location;
	addrOf.op = ir.Unary.Op.AddrOf;
	addrOf.value = buildExpReference(location, arrayStructVar, "from");

	auto arrayPointer = new ir.PointerType(copyTypeSmart(location, atype));
	arrayPointer.location = location;

	auto _cast = new ir.Unary(arrayPointer, addrOf);
	_cast.location = location;

	auto deref = new ir.Unary();
	deref.location = location;
	deref.op = ir.Unary.Op.Dereference;
	deref.value = _cast;

	auto returnStatement = new ir.ReturnStatement();
	returnStatement.exp = deref;
	returnStatement.location = location;

	fn._body.statements ~= returnStatement;

	return fn;
}


ir.Exp createAllocDgCall(ir.Variable allocDgVar, LanguagePass lp, Location location, ir.Type type, ir.Exp countArg = null, bool suppressCast = false)
{
	auto adRef = new ir.ExpReference();
	adRef.location = location;
	adRef.idents ~= "allocDg";
	adRef.decl = allocDgVar;

	auto tidExp = new ir.Typeid();
	tidExp.location = location;
	tidExp.type = copyTypeSmart(location, type);

	auto countConst = new ir.Constant();
	countConst.location = location;
	countConst._ulong = 0;
	countConst.type = lp.settings.getSizeT(location);

	auto pfixCall = new ir.Postfix();
	pfixCall.location = location;
	pfixCall.op = ir.Postfix.Op.Call;
	pfixCall.child = adRef;
	pfixCall.arguments ~= tidExp;
	if (countArg is null) {
		pfixCall.arguments ~= countConst;
	} else {
		pfixCall.arguments ~= buildCast(location, lp.settings.getSizeT(location), countArg);
	}

	if (!suppressCast) {
		auto asTR = cast(ir.TypeReference) type;
		if (asTR !is null) {
			suppressCast = asTR.type.nodeType == ir.NodeType.Class;
		}
	}

	if (!suppressCast) {
		auto result = new ir.PointerType(copyTypeSmart(location, type));
		result.location = location;
		auto resultCast = new ir.Unary(result, pfixCall);
		resultCast.location = location;
		return resultCast;
	} else {
		return pfixCall;
	}
}
	
class NewReplacer : NullVisitor, Pass
{
public:
	ir.Variable allocDgVar;
	LanguagePass lp;
	ir.Module thisModule;

public:
	this(LanguagePass lp)
	{
		this.lp = lp;
	}
	
	override void transform(ir.Module m)
	{
		thisModule = m;
		allocDgVar = retrieveAllocDg(lp, m.myScope, m.location);
		accept(m, this);
	}

	override void close()
	{	
	}

	void createWrapperConstructorIfNeeded(Location location, ir.Class _class, ir.Unary unary)
	{
		if (_class.constructor !is null) {
			return;
		}
		auto _module = getModuleFromScope(_class.myScope);

		auto _function = buildFunction(location, _class.members, _class.myScope, "magicConstructor");
		_function.type.ret = copyTypeSmart(location, _class);
		_function.type.params = copyVariablesSmart(location, _class.userConstructors[0].type.params);

		// auto thisVar = allocDg(Class, -1)
		auto thisVar = buildVarStatSmart(location, _function._body, _function._body.myScope, _class, "thisVar");
		thisVar.assign = createAllocDgCall(allocDgVar, lp, unary.location, _class, buildConstantInt(unary.location, -1), true);
		thisVar.assign = buildCastSmart(location, _class, thisVar.assign);

		// thisVar.this(cast(void*) thisVar)
		assert(_class.userConstructors.length == 1);
		auto eref = buildExpReference(unary.location, _class.userConstructors[0], "this");
		auto exp = buildCall(location, eref, null);
		exp.arguments ~= getExpRefs(location, _function.type.params) ~ buildCast(location, buildVoidPtr(location), buildExpReference(location, thisVar, "thisVar"));
		buildExpStat(location, _function._body, exp);

		// return thisVar
		buildReturnStat(location, _function._body, buildExpReference(location, thisVar, "thisVar"));

		_class.constructor = _function;
	}

	override Status enter(ref ir.Exp exp, ir.Unary unary)
	{
		if (unary.op != ir.Unary.Op.New) {
			return Continue;
		}

		if (unary.type.nodeType == ir.NodeType.ArrayType && unary.argumentList.length > 0) {
			if (unary.argumentList.length != 1) {
				throw CompilerPanic(unary.location, "multidimensional arrays unsupported at the moment.");
			}
			// WIP, doesn't consider multiple outputs of the same function.
			auto asArray = cast(ir.ArrayType) unary.type;
			assert(asArray !is null);
			auto allocFn = createArrayAllocFunction(unary.location, lp, thisModule.myScope, asArray);
			thisModule.children.nodes = allocFn ~ thisModule.children.nodes;
			thisModule.myScope.addFunction(allocFn, allocFn.name);

			auto _ref = new ir.ExpReference();
			_ref.location = unary.location;
			_ref.idents ~= allocFn.name;
			_ref.decl = allocFn;

			auto call = new ir.Postfix();
			call.location = unary.location;
			call.op = ir.Postfix.Op.Call;
			call.arguments ~= buildCast(unary.location, lp.settings.getSizeT(unary.location), unary.argumentList[0]);
			call.child = _ref;

			exp = call;

			return Continue;
		} else if (unary.hasArgumentList) {
			auto tr = cast(ir.TypeReference) unary.type;
			assert(tr !is null);
			auto _class = cast(ir.Class) tr.type;

			createWrapperConstructorIfNeeded(unary.location, _class, unary);
			auto eref = buildExpReference(unary.location, _class.constructor, "magicConstructor");
			exp = buildCall(unary.location, eref, unary.argumentList);

			return Continue;
		}

		exp = createAllocDgCall(allocDgVar, lp, unary.location, unary.type);

		return Continue;
	}
}

