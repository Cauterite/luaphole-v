/* -------------------------------------------------------------------------- */

import std.conv : to_ = to;
import std.exception : enforce_ = enforce;
import StdIo_ = std.stdio : print_ = writeln;
import std.typecons : Nullableº_ = Nullable;

import W32_ = win32.windows;

/* -------------------------------------------------------------------------- */

void main(string[] Params) {
	patch(to_!wstring(Params[1]));
};

void patch(in wchar[] SrcName) {
	/* statically inject a DLL by moving+extending the imports table */

	auto FileHdl = enforce_(pinvoke!(`kernel32`, `CreateFileW`, size_t)(
		SrcName.ptr,
		W32_.GENERIC_WRITE|W32_.GENERIC_READ,
		0, /* dwShareMode */
		null,
		W32_.OPEN_EXISTING,
		0,
		null
	));
	scope(exit) {pinvoke!(`kernel32`, `CloseHandle`)(FileHdl);};

	auto MapHdl = enforce_(pinvoke!(`kernel32`, `CreateFileMappingW`, size_t)(
		FileHdl,
		null,
		W32_.PAGE_READWRITE,
		ulong(0),
		null
	));
	scope(exit) {pinvoke!(`kernel32`, `CloseHandle`)(MapHdl);};

	void* FileData = enforce_(pinvoke!(`kernel32`, `MapViewOfFile`, void*)(
		MapHdl,
		W32_.FILE_MAP_WRITE,
		ulong(0),
		size_t(0)
	));

	auto Head = cast(PeHeaderº*) (FileData + *(cast(ushort*) (FileData+0x3c)));
	enforce_(is_x32(Head) || is_x64(Head));

	/* apply modifications */
	print_(`Characteristics |= IMAGE_FILE_LARGE_ADDRESS_AWARE`);
	Head.Characteristics |= 0x20; /* IMAGE_FILE_LARGE_ADDRESS_AWARE */
	Head.SizeOfStackCommit32 = 0x20000;
	print_(`StackCommit = `, Head.SizeOfStackCommit32);

	/* save changes */
	enforce_(pinvoke!(`kernel32`, `UnmapViewOfFile`, int)(FileData));
};

bool is_x32(PeHeaderº* X) {return X.Machine == W32_.IMAGE_FILE_MACHINE_I386;};
bool is_x64(PeHeaderº* X) {return X.Machine == W32_.IMAGE_FILE_MACHINE_AMD64;};

struct PeHeaderº {align(1) {
	char[4] Signature;
	ushort Machine;
	ushort NumberOfSections;
	uint TimeDateStamp;
	uint PointerToSymbolTable;
	uint NumberOfSymbols;
	ushort SizeOfOptionalHeader;
	ushort Characteristics;
	ushort MagicNumber;
	ubyte MajorLinkerVersion;
	ubyte MinorLinkerVersion;
	uint SizeOfCode;
	uint SizeOfInitializedData;
	uint SizeOfUninitializedData;
	uint EntrypointRva;
	uint BaseOfCode;
	union {
		ulong ImageBase64;
		struct {
			uint BaseOfData32;
			uint ImageBase32;
		};
	};
	uint SectionAlignment;
	uint FileAlignment;
	ushort MajorOSVersion;
	ushort MinorOSVersion;
	ushort MajorImageVersion;
	ushort MinorImageVersion;
	ushort MajorSubsystemVersion;
	ushort MinorSubsystemVersion;
	uint Win32VersionValue;
	uint SizeOfImage;
	uint SizeOfHeaders;
	uint Checksum;
	ushort Subsystem;
	ushort DLLCharacteristics;
	union {
		struct {
			uint SizeOfStackReserve32;
			uint SizeOfStackCommit32;
			uint SizeOfHeapReserve32;
			uint SizeOfHeapCommit32;
			uint LoaderFlags32;
			uint NumberOfRvaAndSizes32;
		};
		struct {
			ulong SizeOfStackReserve64;
			ulong SizeOfStackCommit64;
			ulong SizeOfHeapReserve64;
			ulong SizeOfHeapCommit64;
			uint LoaderFlags64;
			uint NumberOfRvaAndSizes64;
		};
	};
};};

struct PeDataDirº {
	struct Dº {uint Rva; uint Size;};
	Dº ExportTbl;
	Dº ImportTbl;
	Dº ResourceTbl;
	Dº ExceptionTbl;
	Dº CertificateTbl;
	Dº RelocationTbl;
	Dº DebugTbl;
	Dº ØA; /* reserved */
	Dº GlobalPtr;
	Dº TlsTbl;
	Dº LoadConfigTbl;
	Dº BoundImportTbl;
	Dº ImportAddressTbl;
	Dº DelayImportDesc;
	Dº ClrHeader;
	Dº ØB; /* reserved */
};

struct SectDescº {align(1) {
	char[8] Name;
	uint VirtualSize;
	uint Rva;
	uint SourceSize;
	uint SourceOffset;
	uint PointerToRealocations; /* unused */
	uint PointerToLinenumbers; /* unused */
	ushort NumberOfRealocations; /* unused */
	ushort NumberOfLinenumbers; /* unused */
	uint Characteristics;
};};

struct LibImportDescº {
	uint OriginalImportsRva;
	uint TimeDateStamp;
	uint ForwarderChain;
	uint NameRva;
	uint ImportsRva;
};

/* --- --- */

alias Stdcallº(Rº, Pº...) = extern(Windows) Rº function(Pº);

template pinvoke(wstring LibName, string FuncName, Rº = void, Pº...) {
	auto pinvoke(Pº Params) {
		auto Lib = W32_.GetModuleHandleW((LibName~'\0').ptr);
		if (!Lib) {
			Lib = W32_.LoadLibraryW((LibName~'\0').ptr);
		};
		auto Func = cast(Stdcallº!(Rº, Pº)) (
			W32_.GetProcAddress(Lib, (FuncName~'\0').ptr)
		);
		assert(Func, `GetProcAddress failed for `~FuncName);
		return Func(Params);
	};
};

/* -------------------------------------------------------------------------- */

/+

















































+/

/* -------------------------------------------------------------------------- */