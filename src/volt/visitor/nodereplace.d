module volt.visitor.nodereplace;

import volt.visitor.visitor;

import volt.ir.copy;
import ir = volt.ir.ir;

class ExpReferenceReplacer : NullVisitor
{
public:
	this(ir.Declaration decl, ir.Exp exp)
	in {
		assert(decl !is null);
		assert(exp !is null);
	}
	body {
		this.fromDecl = decl;
		this.toExp = exp;
	}

	this()
	{
	}

public:
	ir.Declaration fromDecl;
	ir.Exp toExp;

public:
	override Status visit(ref ir.Exp exp, ir.ExpReference eref)
	{
		assert(fromDecl !is null && toExp !is null);
		if (eref.decl is fromDecl) {
			exp = copyExp(toExp);
		}
		return Continue;
	}
}
