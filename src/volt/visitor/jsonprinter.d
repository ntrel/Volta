// Copyright © 2014, Bernard Helyer.  All rights reserved.
// Copyright © 2015, Jakob Bornecrantz.  All rights reserved.
// See copyright notice in src/volt/license.d (BOOST ver. 1.0).
module volt.visitor.jsonprinter;

import watt.io.streams : OutputFileStream;
import watt.text.utf : encode;

import ir = volt.ir.ir;

import volt.errors;
import volt.interfaces;
import volt.visitor.visitor;


private struct Entry
{
	string name;
	string comment;
}

class JsonPrinter : NullVisitor
{
public:
	Entry[] functions, variables, enums, structs, classes;
	ir.Module currentModule;


private:
	string mFilename;
	OutputFileStream mFile;


public:
	this(string filename)
	{
		this.mFilename = filename;
	}

	void transform(ir.Module[] modules...)
	{
		foreach (mod; modules) {
			currentModule = mod;
			accept(mod, this);
		}
		mFile = new OutputFileStream(mFilename);
		w("{\n");
		writeArray("functions", functions, ",\n");
		writeArray("variables", variables, ",\n");
		writeArray("enums", enums, ",\n");
		writeArray("structs", structs, ",\n");
		writeArray("classes", classes, "\n");
		w("}\n");
		mFile.flush();
		mFile.close();
	}

	override Status enter(ir.Function func)
	{
		if (func.docComment.length > 0) {
			Entry e;
			e.name = currentModule.name.toString() ~ "." ~ func.name;
			e.comment = func.docComment;
			functions ~= e;
		}
		return Continue;
	}

	override Status enter(ir.Variable v)
	{
		if (v.docComment.length > 0) {
			Entry e;
			e.name = currentModule.name.toString() ~ "." ~ v.name;
			e.comment = v.docComment;
			variables ~= e;
		}
		return Continue;
	}

	override Status enter(ir.Enum en)
	{
		if (en.docComment.length > 0) {
			Entry e;
			e.name = currentModule.name.toString() ~ "." ~ en.name;
			e.comment = en.docComment;
			enums ~= e;
		}
		return Continue;
	}

	override Status enter(ir.Struct s)
	{
		if (s.docComment.length > 0) {
			Entry e;
			e.name = currentModule.name.toString() ~ "." ~ s.name;
			e.comment = s.docComment;
			structs ~= e;
		}
		return Continue;
	}

	override Status enter(ir.Class c)
	{
		if (c.docComment.length > 0) {
			Entry e;
			e.name = currentModule.name.toString() ~ "." ~ c.name;
			e.comment = c.docComment;
			classes ~= e;
		}
		return Continue;
	}

private:
	void writeArray(string entryName, Entry[] entries, string end)
	{
		wq(entryName);
		w(": [");
		foreach (i, n; entries) {
			w("[");
			wq(n.name);
			w(", ");
			wq(n.comment);
			w("]");
			w((i == entries.length - 1) ? "" : ",");
		}
		w("]" ~ end);
	}

	void w(string s)
	{
		mFile.writef(`%s`, s);
	}

	/// Add quotes to s and make it a JSON string (w/ escaping etc).
	void wq(string s)
	{
		char[] outString;
		foreach (dchar c; s) {
			switch (c) {
			case '"': outString ~= `\"`; break;
			case '\n': outString ~= `\n`; break;
			case '\r': outString ~= `\r`; break;
			case '\t': outString ~= `\t`; break;
			case '\f': outString ~= `\f`; break;
			case '\b': outString ~= `\b`; break;
			case '\\': outString ~= `\\` ; break;
			default: encode(outString, c); break;
			}
		}
		mFile.writef(`"%s"`, outString);
	}
}
