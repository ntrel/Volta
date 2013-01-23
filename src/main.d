// Copyright © 2012, Jakob Bornecrantz.  All rights reserved.
// See copyright notice in src/volt/license.d (BOOST ver. 1.0).
module main;

import std.stdio : writefln;

import volt.license;
import volt.interfaces;
import volt.controller;


int main(string[] args)
{
	auto settings = new Settings();

	setDefault(settings);
	if (!filterArgs(args, settings))
		return 0;

	if (args.length <= 1) {
		writefln("%s: no input files", args[0]);
		return 0;
	}

	auto vc = new VoltController(settings);
	vc.addFiles(args[1 .. $]);
	int ret = vc.compile();
	vc.close();

	return ret;
}

bool filterArgs(ref string[] args, Settings settings)
{
	void delegate(string) argHandler;
	string[] ret;
	int i;
	ret.length = args.length;

	// Handlers.
	void outputFile(string file) {
		settings.outputFile = file;
	}

	void includePath(string path) {
		settings.includePaths ~= path;
	}

	// Skip the first argument.
	ret[i++] = args[0];

	foreach(arg; args[1 .. $])  {
		if (argHandler !is null) {
			argHandler(arg);
			argHandler = null;
			continue;
		}

		switch (arg) {
		case "-license", "--license":
			return printLicense();
		case "-o":
			argHandler = &outputFile;
			continue;
		case "-I":
			argHandler = &includePath;
			continue;
		case "-w":
			settings.warningsEnabled = true;
			continue;
		case "-d":
			settings.debugEnabled = true;
			continue;
		case "-c":
			settings.noLink = true;
			continue;
		case "--emit-bitcode":
			settings.emitBitCode = true;
			continue;
		case "--no-backend":
		case "-S":
			settings.noBackend = true;
			continue;
		case "--no-catch":
			settings.noCatch = true;
			continue;
		case "--no-stdlib":
			settings.noStdLib = true;
			continue;
		case "--internal-dbg":
			settings.internalDebug = true;
			continue;
		case "--help", "-h":
			return printUsage();
		default:
		}

		ret[i++] = arg;
	}

	settings.setVersionsFromOptions();

	ret.length = i;
	args = ret;
	return true;
}

void setDefault(Settings settings)
{
	// Only MinGW is supported.
	version (Windows) {
		settings.platform = Platform.MinGW;
	} else version (linux) {
		settings.platform = Platform.Linux;
	} else version (OSX) {
		settings.platform = Platform.OSX;
	} else {
		static assert(false);
	}

	version (X86) {
		settings.arch = Arch.X86;
	} else version (X86_64) {
		settings.arch = Arch.X86_64;
	} else {
		static assert(false);
	}
}

bool printUsage()
{
	writefln("usage: volt [options] [source files]");
	writefln("\t--license       Print license information and quit.");
	writefln("\t-o outputname   Set output to outputname.");
	writefln("\t-I path         Add a include path.");
	writefln("\t-w              Enable warnings.");
	writefln("\t-d              Compile in debug mode.");
	writefln("\t-c              Compile only, do not link.");
	writefln("\t--emit-bitcode  Emit LLVM bitcode (implies -c).");
	writefln("\t-S,--no-backend Stop compilation before the backend.");
	writefln("\t--no-catch      For compiler debugging purposes.");
	writefln("\t--internal-dbg  Enables internal debug printing.");
	writefln("\t-h,--help       Print this message and quit.");
	return false;
}

bool printLicense()
{
	foreach(license; licenseArray)
		writefln(license);
	return false;
}

