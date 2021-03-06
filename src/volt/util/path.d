// Copyright © 2011, Bernard Helyer.  All rights reserved.
// Copyright © 2012, Jakob Bornecrantz.  All rights reserved.
// See copyright notice in src/volt/license.d (BOOST ver. 1.0).
module volt.util.path;

import watt.conv : toString;
import watt.path : mkdir, exists, dirName, dirSeparator;

version (Posix) {
	version (Volt) import core.posix.unistd : getuid;
	else import core.sys.posix.unistd : getuid;
}


/**
 * Does the same as unix's "mkdir -p" command.
 */
void mkdirP(string name)
{
	if (name == "" || name is null) {
		return;
	}

	auto str = dirName(name);
	if (str != ".") {
		mkdirP(str);
	}

	if (!exists(name)) {
		mkdir(name);
	}
}

/**
 * Turns a qualified module name into a list of possible file paths.
 */
string[] genPossibleFilenames(string dir, string[] names, string suffix)
{
	string[] paths;
	auto ret = dir;

	foreach (name; names) {
		ret ~= dirSeparator ~ name;
	}
	paths ~= ret ~ suffix;
	paths ~= ret ~ dirSeparator ~ "package" ~  suffix;

	return paths;
}

/**
 * Get the temporary subdirectory name for this run of the compiler.
 */
string getTemporarySubdirectoryName()
{
	string name = "volta-";
	version (Posix) {
		name ~= toString(getuid());
	}
	return name;
}
