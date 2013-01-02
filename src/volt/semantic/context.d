// Copyright © 2012, Jakob Bornecrantz.  All rights reserved.
// See copyright notice in src/volt/license.d (BOOST ver. 1.0).
module volt.semantic.context;

import ir = volt.ir.ir;

import volt.exceptions;
import volt.interfaces;
import volt.visitor.visitor;
import volt.semantic.languagepass;

/**
 * Builds populates ir.volt.context.Scopes on
 * Modules, Classes, Structs and the like.
 *
 * @ingroup passes passLang
 */
class ContextBuilder : NullVisitor, Pass
{
public:
	ir.Scope current;
	ir.Struct[] structStack;

public:
	void close()
	{
	}

	void transform(ir.Module m)
	{
		if (m.myScope !is null) {
			return;
		}

		accept(m, this);
	}

	ir.Scope newContext(ir.Node n, string name)
	{
		auto newCtx = new ir.Scope(current, n, name);
		return current = newCtx;
	}

	void pop()
	{
		current = current.parent;
	}


	/*
	 * New Scopes.
	 */


	override Status enter(ir.Module m)
	{
		assert(m !is null);
		assert(m.myScope is null);
		assert(current is null);
		// Name
		string name = m.name.identifiers[$-1].value;
		m.myScope = current = new ir.Scope(m, name);
		m.internalScope = new ir.Scope(m, "_" ~ name);

		return Continue;
	}

	override Status leave(ir.Module m)
	{
		assert(current !is null);
		current = null;
		return Continue;
	}

	override Status enter(ir.Class c)
	{
		current.addType(c, c.name);
		c.myScope = newContext(c, c.name);

		return Continue;
	}

	override Status enter(ir._Interface i)
	{
		current.addType(i, i.name);
		i.myScope = newContext(i, i.name);

		return Continue;
	}

	override Status enter(ir.Struct s)
	{
		current.addType(s, s.name);
		s.myScope = newContext(s, s.name);

		structStack ~= s;		

		return Continue;
	}

	override Status enter(ir.Function fn)
	{
		current.addFunction(fn, fn.name);
		fn.myScope = newContext(fn, fn.name);
		foreach (var; fn.type.params) {
			fn.myScope.addValue(var, var.name);
		}

		if (structStack.length == 0) {
			return Continue;
		}

		/// @todo not when the function is static

		auto tr = new ir.TypeReference();
		tr.location = structStack[$-1].location;
		tr.names ~= structStack[$-1].name;
		tr.type = structStack[$-1];

		auto thisVar = new ir.Variable();
		thisVar.location = structStack[$-1].location;
		thisVar.type = new ir.PointerType(tr);
		thisVar.name = "this";
		thisVar.mangledName = "this";

		fn.myScope.addValue(thisVar, thisVar.name);
		fn.type.params ~= thisVar;
		fn.type.hiddenParameter = true;

		return Continue;
	}

	override Status leave(ir.Class c) { pop(); return Continue; }
	override Status leave(ir._Interface i) { pop(); return Continue; }

	override Status leave(ir.Struct s) 
	{ 
		pop();
		assert(structStack.length > 0); 
		structStack = structStack[0 .. $-1];
		return Continue;
	}

	override Status leave(ir.Function fn) { pop(); return Continue; }
}
