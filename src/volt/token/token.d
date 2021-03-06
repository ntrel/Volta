// Copyright © 2010-2011, Bernard Helyer.  All rights reserved.
// Copyright © 2012, Jakob Bornecrantz.  All rights reserved.
// See copyright notice in src/volt/license.d (BOOST ver. 1.0).
module volt.token.token;

import volt.token.location;

/* If you're adding a new token, be sure to update:
 *   - the _tokenToString array. Keep it alphabetical, and update its length.
 *   - the TokenType enum, again keep it alphabetical. It's _vital_ that the order
 *     is the same in the TokenType enum and the tokenToString array.
 *   - if you're adding a keyword, add it to identifierType.
 *
 * Removing is the same thing in reverse. When modifying tokenToString, be sure
 * to keep commas between elements -- two string literals straight after one
 * another are implicitly concatenated. I warn you of this out of experience.
 */
enum immutable(string)[] _tokenToString = [
"none", "BEGIN", "END", "DocComment",
"identifier", "string literal", "character literal",
"integer literal", "float literal", "abstract", "alias", "align",
"asm", "assert", "auto", "body", "bool", "break", "byte", "case",
"cast", "catch", "cdouble", "cent", "cfloat", "char", "class",
"const", "continue", "creal", "dchar", "debug", "default",
"delegate", "delete", "deprecated", "do", "double", "else", "enum",
"export", "extern", "f32", "f64",
"false", "final", "finally", "float", "for",
"foreach", "foreach_reverse", "fn", "function", "global", "goto",
"i8", "i16", "i32", "i64", "idouble",
"if", "ifloat", "immutable", "import", "in", "inout", "int", "interface",
"invariant", "ireal", "is", "lazy", "local", "long", "macro", "mixin",
"module", "new", "nothrow", "null", "out", "override", "package", "pragma",
"private", "protected", "public", "pure", "real", "ref", "return",
"scope", "shared", "short", "static", "struct", "super",
"switch", "synchronized", "template", "this", "throw", "true",
"try", "typedef", "typeid", "typeof",
"u8", "u16", "u32", "u64", "ubyte", "ucent", "uint",
"ulong", "union", "unittest", "ushort", "va_arg", "version", "void",
"volatile", "wchar", "while", "with", "__FILE__", "__FUNCTION__", "__LINE__",
"__LOCATION__", "__PRETTY_FUNCTION__", "__thread", "__traits", "#run",
"/", "/=", ".", "..", "...", "&", "&=", "&&", "|", "|=", "||",
"-", "-=", "--", "+", "+=", "++", "<", "<=", "<<", "<<=", "<>", "<>=",
">", ">=", ">>=", ">>>=", ">>", ">>>", "!", "!=", "!<>", "!<>=", "!<",
"!<=", "!>", "!>=", "(", ")", "[", "]", "{", "}", "?", ",", ";",
":", ":=", "$", "=", "==", "*", "*=", "%", "%=", "^", "^=", "^^", "^^=", "~", "~=",
"@",
];

/**
 * Ensure that the above list and following enum stay in sync,
 * and that the enum starts at zero and increases sequentially
 * (i.e. adding a member increases TokenType.max).
 */
version (Volt) {
	// @todo static assert
} else {
	static assert(TokenType.min == 0);
	static assert(_tokenToString.length == TokenType.max + 1, "the tokenToString array and TokenType enum are out of sync.");
}

enum TokenType
{
	None = 0,

	// Special
	Begin,
	End,
	DocComment,

	// Literals
	Identifier,
	StringLiteral,
	CharacterLiteral,
	IntegerLiteral,
	FloatLiteral,

	// Keywords
	Abstract, Alias, Align, Asm, Assert, Auto,
	Body, Bool, Break, Byte,
	Case, Cast, Catch, Cdouble, Cent, Cfloat, Char,
	Class, Const, Continue, Creal,
	Dchar, Debug, Default, Delegate, Delete,
	Deprecated, Do, Double,
	Else, Enum, Export, Extern,
	F32, F64,
	False, Final, Finally, Float, For, Foreach,
	ForeachReverse, Fn, Function,
	Global, Goto,
	I8, I16, I32, I64,
	Idouble, If, Ifloat, Immutable, Import, In,
	Inout, Int, Interface, Invariant, Ireal, Is,
	Lazy, Local, Long,
	Macro, Mixin, Module,
	New, Nothrow, Null,
	Out, Override,
	Package, Pragma, Private, Protected, Public, Pure,
	Real, Ref, Return,
	Scope, Shared, Short, Static, Struct, Super,
	Switch, Synchronized,
	Template, This, Throw, True, Try, Typedef,
	Typeid, Typeof,
	U8, U16, U32, U64,
	Ubyte, Ucent, Uint, Ulong, Union, Unittest, Ushort,
	VaArg, Version, Void, Volatile,
	Wchar, While, With,
	__File__, __Function__, __Line__, __Location__,
	__Pretty_Function__, __Thread, __Traits,
	HashRun,

	/// Symbols.
	Slash,                  // /
	SlashAssign,            // /=
	Dot,                    // .
	DoubleDot,              // ..
	TripleDot,              // ...
	Ampersand,              // &
	AmpersandAssign,        // &=
	DoubleAmpersand,        // &&
	Pipe,                   // |
	PipeAssign,             // |=
	DoublePipe,             // ||
	Dash,                   // -
	DashAssign,             // -=
	DoubleDash,             // --
	Plus,                   // +
	PlusAssign,             // +=
	DoublePlus,             // ++
	Less,                   // <
	LessAssign,             // <=
	DoubleLess,             // <<
	DoubleLessAssign,       // <<=
	LessGreater,            // <>
	LessGreaterAssign,      // <>=
	Greater,                // >
	GreaterAssign,          // >=
	DoubleGreaterAssign,    // >>=
	TripleGreaterAssign,    // >>>=
	DoubleGreater,          // >>
	TripleGreater,          // >>>
	Bang,                   // !
	BangAssign,             // !=
	BangLessGreater,        // !<>
	BangLessGreaterAssign,  // !<>=
	BangLess,               // !<
	BangLessAssign,         // !<=
	BangGreater,            // !>
	BangGreaterAssign,      // !>=
	OpenParen,              // (
	CloseParen,             // )
	OpenBracket,            // [
	CloseBracket,           // ]
	OpenBrace,              // {
	CloseBrace,             // }
	QuestionMark,           // ?
	Comma,                  // ,
	Semicolon,              // ;
	Colon,                  // :
	ColonAssign,            // :=
	Dollar,                 // $
	Assign,                 // =
	DoubleAssign,           // ==
	Asterix,                // *
	AsterixAssign,          // *=
	Percent,                // %
	PercentAssign,          // %=
	Caret,                  // ^
	CaretAssign,            // ^=
	DoubleCaret,            // ^^
	DoubleCaretAssign,      // ^^=
	Tilde,                  // ~
	TildeAssign,            // ~=
	At,                     // @
}

string tokenToString(TokenType token)
{
	return _tokenToString[token];
}

/**
 * Holds the type, the actual string and location within the source file.
 */
final class Token
{
	TokenType type;
	string value;
	Location location;
	bool isBackwardsComment;
}

/**
 * Go from a string identifier to a TokenType.
 *
 * Side-effects:
 *   None.
 *
 * Returns:
 *   Always a TokenType, for unknown ones TokenType.Identifier.
 */
TokenType identifierType(string ident)
{
	switch(ident) with (TokenType) {
	case "abstract":            return Abstract;
	case "alias":               return Alias;
	case "align":               return Align;
	case "asm":                 return Asm;
	case "assert":              return Assert;
	case "auto":                return Auto;
	case "body":                return Body;
	case "bool":                return Bool;
	case "break":               return Break;
	case "byte":                return Byte;
	case "case":                return Case;
	case "cast":                return Cast;
	case "catch":               return Catch;
	case "cdouble":             return Cdouble;
	case "cent":                return Cent;
	case "cfloat":              return Cfloat;
	case "char":                return Char;
	case "class":               return Class;
	case "const":               return Const;
	case "continue":            return Continue;
	case "creal":               return Creal;
	case "dchar":               return Dchar;
	case "debug":               return Debug;
	case "default":             return Default;
	case "delegate":            return Delegate;
	case "delete":              return Delete;
	case "deprecated":          return Deprecated;
	case "do":                  return Do;
	case "double":              return Double;
	case "else":                return Else;
	case "enum":                return Enum;
	case "export":              return Export;
	case "extern":              return Extern;
	case "f32":                 return F32;
	case "f64":                 return F64;
	case "false":               return False;
	case "final":               return Final;
	case "finally":             return Finally;
	case "float":               return Float;
	case "for":                 return For;
	case "foreach":             return Foreach;
	case "foreach_reverse":     return ForeachReverse;
	case "fn":                  return Fn;
	case "function":            return Function;
	case "global":              return Global;
	case "goto":                return Goto;
	case "i8":                  return I8;
	case "i16":                 return I16;
	case "i32":                 return I32;
	case "i64":                 return I64;
	case "idouble":             return Idouble;
	case "if":                  return If;
	case "ifloat":              return Ifloat;
	case "immutable":           return Immutable;
	case "import":              return Import;
	case "in":                  return In;
	case "inout":               return Inout;
	case "int":                 return Int;
	case "interface":           return Interface;
	case "invariant":           return Invariant;
	case "ireal":               return Ireal;
	case "is":                  return Is;
	case "lazy":                return Lazy;
	case "local":               return Local;
	case "long":                return Long;
	case "macro":               return Macro;
	case "mixin":               return Mixin;
	case "module":              return Module;
	case "new":                 return New;
	case "nothrow":             return Nothrow;
	case "null":                return Null;
	case "out":                 return Out;
	case "override":            return Override;
	case "package":             return Package;
	case "pragma":              return Pragma;
	case "private":             return Private;
	case "protected":           return Protected;
	case "public":              return Public;
	case "pure":                return Pure;
	case "real":                return Real;
	case "ref":                 return Ref;
	case "return":              return Return;
	case "scope":               return Scope;
	case "shared":              return Shared;
	case "short":               return Short;
	case "static":              return Static;
	case "struct":              return Struct;
	case "super":               return Super;
	case "switch":              return Switch;
	case "synchronized":        return Synchronized;
	case "template":            return Template;
	case "this":                return This;
	case "throw":               return Throw;
	case "true":                return True;
	case "try":                 return Try;
	case "typedef":             return Typedef;
	case "typeid":              return Typeid;
	case "typeof":              return Typeof;
	case "u8":                  return U8;
	case "u16":                 return U16;
	case "u32":                 return U32;
	case "u64":                 return U64;
	case "ubyte":               return Ubyte;
	case "ucent":               return Ucent;
	case "uint":                return Uint;
	case "ulong":               return Ulong;
	case "union":               return Union;
	case "unittest":            return Unittest;
	case "ushort":              return Ushort;
	case "va_arg":              return VaArg;
	case "version":             return Version;
	case "void":                return Void;
	case "volatile":            return Volatile;
	case "wchar":               return Wchar;
	case "while":               return While;
	case "with":                return With;
	case "__FILE__":            return __File__;
	case "__FUNCTION__":        return __Function__;
	case "__LINE__":            return __Line__;
	case "__LOCATION__":        return __Location__;
	case "__PRETTY_FUNCTION__": return __Pretty_Function__;
	case "__thread":            return __Thread;
	case "__traits":            return __Traits;
	case "isize":               assert(false, "reserved");
	case "usize":               assert(false, "reserved");
	default:                    return Identifier;
	}
}
