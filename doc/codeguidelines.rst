Volt / Watt Code Guidelines
###########################
So you want to contribute to the Volt compiler or its standard library, Watt, but you don't want people yelling at you for using the wrong indentation settings or putting a brace where it shouldn't go? You've come to the right place.

These guidelines go for related tools like Tesla too.

Indentation
===========
Set your editor to emit real tabs, and display them with a size of four spaces when editing the Volt or Watt code.
It's left to your better judgement whether or not you need to wrap your code or not (consider it after 80-100 columns or so). When wrapping, use tabs to indent to the level of the last line, then uses spaces to align to after the first open paren (or first character otherwise). The \TTT represent tabs, the . characters represent spaces.::

    \TTTaFunction(aLongParameter,
    \TTT..........bLongParameter);
    \TTTif ((foo ||
    \TTT.....bar) && baz) {

Braces
======
For functions, structs, classes, and the like, the opening brace goes on a line of it's own, as does the closing brace.::

    void add(i32 a, i32 b)
    {
        return a + b;
    }

    struct Person
    {
        string name;
        i32 age;
    }

For statements with an opening brace, the brace is on the same line as the statement itself. Unlike functions, there is a space between the keyword and the opening paren.::

    while (i < 10) {
        writefln("%s", i++);
    }

There is no space for asserts, typeids, etc.::

    assert(typeid(i32).size == 4);

Expressions
===========
When casting, there should be no space between the cast and the cast expression.::

    auto asInt = cast(i32)someVal;

There are spaces between operators and operands.::

    auto c = b + a;

And no spaces between opening and closing parens and expressions.::

    transmit(importantData);

Classes And Friends
===================
Classes should be laid out in a particular order. Most of this applies to structs etc, just skip over what doesn't apply (no fields for an interface, etc).
Instead of attaching the access (``public``, ``private``, ``protected``, etc) directly to the declaration, use ``public:`` or ``private:`` etc blocks and put all like declarations in that block. Of course, not every class will have every block.::

    class AClass
    {
    public:
        // Public type definitions.
    protected:
        // Protected type definitions.
    private:
        // Private type definitions.
    public:
        // Public fields.
    protected:
        // Protected fields.
    private:
        // Private fields.
    public:
        // Public methods/constructors.
    protected:
        // Protected methods.
    private:
        // Private methods.
    }

Naming
======
Modules and packages are all lower case. Types start with an upper case, and each word is distinguished with an upper case letter. Functions and variables are the same, but they start with a lower case letter.::

    module test;

    struct Thing
    {
        i32 doThing(i32 aParameter)
        {
            return aParameter;
        }
    }

Names should be descriptive, but not overly long.

Other
=====
Undoubtedly, there are countless little things that we've missed here. If you're not sure about something, check for an example in existing source files, or just ask somebody. Thank you for reading this *dynamic* and *exciting* document.
