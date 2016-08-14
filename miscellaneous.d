/* -------------------------------------------------------------------------- */

import Std_;

import Lang_ = language;

/* -------------------------------------------------------------------------- */

enum StrZ(alias S) = S~'\0';
alias Cdeclº(Rº, Pº...) = extern(C) Rº function(Pº);

auto bytes_of(Tº)(Tº X) {
	return *(cast(ubyte[Tº.sizeof]*) &X);
};

auto bptr_of(Tº)(Tº* X) {
	return cast(ubyte[Tº.sizeof]*) X;
};

auto bslic_of(Tº)(Tº* X) {
	return (cast(ubyte*) X)[0 .. Tº.sizeof];
};

bool is_aligned(uint Alignment)(void* Ptr) @nogc nothrow pure {
	return cast(size_t) Ptr % Alignment == 0;
};

void* align_up(uint Alignment)(void* Ptr) @nogc nothrow pure {
	auto X = cast(size_t) Ptr;
	auto Offset = X % Alignment;
	return cast(void*) (Offset ? X + (Alignment - (X % Alignment)) : X);
};

auto arr_tuple(Aº : Tº[Len], Tº, size_t Len)(Aº Arr) {
	return mixin(
		`tuple_(`~iota_(Len).map_!(I => `Arr[`~I.to_!string~`],`).join_~`)`
	);
};

unittest {
	ushort[6] Xs = [0,1,2,3,4,5];
	auto R = only_(Xs.arr_tuple.expand);
	assert(R.equal_(Xs[]));
};

/* --- auto-importing ffi --- */

auto cinvoke(wstring LibName, string FuncName, Rº = void, Pº...)(Pº Params) {
	alias Ptr = LibSymPtr!(LibName, FuncName);
	assert(Ptr !is null);
	return (cast(Cdeclº!(Rº, Pº)) Ptr)(Params);
};

template LibSymPtr(wstring LibName, string SymName) {
	alias LibSymPtr = S.SymPtr;
	struct S {
		static __gshared void* SymPtr;
		shared static this() {
			SymPtr = import_sym(StrZ!LibName.ptr, StrZ!SymName.ptr);
		};
	};
};

version (Windows) void* import_sym(in wchar* LibName, in char* SymName) {
	import W32_ = core.sys.windows.windows;
	auto Lib = W32_.GetModuleHandleW(LibName);
	if (!Lib) {
		Lib = W32_.LoadLibraryW(LibName);
	};
	void* Ptr =  W32_.GetProcAddress(Lib, SymName);
	enforce_(Ptr !is null, `failed to import symbol `~SymName.fromStringz_);
	return Ptr;
};

/* --- libmpdec --- */

/+
NOTE: for some stupid reason libmpdec uses global variables internally, so
you can only ever create one context and none of the signalling functions are
thread-safe.
+/
struct MpDec {
	/* global context (immutable; do not pass to signalling API functions!) */
	static immutable Contextº Ctx;
	shared static this() {
		auto Init = import_sym(StrZ!LibName.ptr, StrZ!`mpd_init`.ptr);
		(cast(Cdeclº!(void, const void*, size_t)) Init)(&Ctx, Precision);
		auto SetTraps = import_sym(StrZ!LibName.ptr, StrZ!`mpd_qsettraps`.ptr);
		(cast(Cdeclº!(void, const void*, uint)) SetTraps)(&Ctx, 0);
	};

	enum LibName = `libmpdec`w;
	enum Precision = Lang_.DecimalPrecision;
	enum Version = `2.4.2`;
	static void assert_version() {
		auto LoadedVersion = typeof(this)._version!(const(char)*)();
		assert(LoadedVersion && LoadedVersion[0 .. Version.length] == Version,
			`unsupported libmpdec version detected (v`~Version~` expected)`
		);
	};

	static template opDispatch(string Name) {
		static auto opDispatch(Rº = void, Pº...)(Pº Params) {
			static assert(Name != ``);
			enum N = Name[0] == '_' ? Name[1 .. $] : Name;
			return cinvoke!(LibName, `mpd_`~N, Rº, Pº)(Params);
		};
	};

	static void free(void* Ptr) {
		auto F = LibSymPtr!(LibName, `mpd_free`);
		(* cast(Cdeclº!(void, void*)*) F)(Ptr);
	};

	static @property size_t MinAlloc() {
		return *(cast(size_t*) LibSymPtr!(LibName, `MPD_MINALLOC`));
	};
	enum MinAllocMin = 2;
	enum MinAllocMax = 64;

	enum Flagº : ubyte {
		Pos = 0,
		Neg = 1,
		Inf = 2,
		NaN = 4,
		SNaN = 8,
		Static = 16,
		StaticData = 32,
		SharedData = 64,
		ConstData = 128,
	};
	enum SpecialFlags = BitFlags_!Flagº(Flagº.Inf, Flagº.NaN, Flagº.SNaN);
	enum DataFlags = BitFlags_!Flagº(
		Flagº.StaticData, Flagº.SharedData, Flagº.ConstData
	);

	struct Decº {
		BitFlags_!Flagº Flags;
		size_t Exp;
		size_t Digits;
		size_t Len;
		size_t Alloc;
		uint* Data;
	};

	enum Statusº : uint {
		Clamped = 0x00000001,
		ConversionSyntax = 0x00000002,
		DivisionByZero = 0x00000004,
		DivisionImpossible = 0x00000008,
		DivisionUndefined = 0x00000010,
		FpuError = 0x00000020,
		Inexact = 0x00000040,
		InvalidContext = 0x00000080,
		InvalidOperation = 0x00000100,
		MallocError = 0x00000200,
		NotImplemented = 0x00000400,
		Overflow = 0x00000800,
		Rounded = 0x00001000,
		Subnormal = 0x00002000,
		Underflow = 0x00004000,
	};

	struct Contextº {
		uint Prec; /* precision */
		uint Emax; /* max positive exp */
		uint Emin; /* min negative exp */
		BitFlags_!Statusº Traps; /* status events that should be trapped */
		BitFlags_!Statusº Status; /* status flags */
		uint NewTrap; /* set by mpd_addstatus_raise() */
		int Round; /* rounding mode */
		int Clamp; /* clamp mode */
		int AllCr; /* all functions correctly rounded */
	};

	struct Specº {
		uint MinWidth; /* minimum field width */
		uint Prec; /* fraction digits or significant digits */
		ubyte Type; /* conversion specifier */
		ubyte Alignment; /* alignment */
		ubyte Sign; /* sign printing/alignment */
		char[5] Fill; /* fill character */
		const(char)* Dot; /* decimal point */
		const(char)* Sep; /* thousands separator */
		const(char)* Grouping; /* grouping of digits */
	};

	@disable this();
};

unittest {
	MpDec.assert_version();
};

/* -------------------------------------------------------------------------- */

/+
















































+/

/* -------------------------------------------------------------------------- */