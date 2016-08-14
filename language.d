/* -------------------------------------------------------------------------- */

import Std_;

/* -------------------------------------------------------------------------- */

enum DecimalPrecision = 28;

enum Linebreaks = [10, 11, 12, 13, 133, 8232, 8233];
enum Whitespaces = Linebreaks~[
	9, 32, 160, 5760, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200,
	8201, 8202, 8239, 8287, 12288
];

enum SyntaxTbl : dchar {
	TextDel = '`',
	Subscript = '.',
	ListOpen = '(',
	ListClose = ')',
	ListMultiWrap = '\\',
	CommDel = ';',
	CommOpen = '\\',
	CommClose = '\\',
	NumPlus = '+',
	NumMinus = '-',
	NumRadixDel = '/',
	NumPoint = ',',
	NumSpace = '_',
	AtomDel = ':',
};

enum KeywordTbl : string {
	Nil = `.n`,
	If = `.if_`,
	Func = `.fn_`,
	Let = `.let_`,
	/* pseudo-keywords */
	Varargs = `.`,
	Unquote = `.uq`,
	SpliceUnquote = `.uq*`,
};

enum CoreNameTbl : string {
	Quote = `.q`,
	EnvNs = `.env`,
	Apply = `.apply`,

	AtomToSym = `.atom->sym`,
	StrToAtom = `.str->atom`,

	EmptyArray = `.empty-arr_`,
	EmptyDict = `.empty-aa_`,

	ParseSrc = `.str->forms`,
	CompileForm = `.form->chunk`,

	/* used by unquote */
	SplicingInvocation = `.q-voke*_`,
	Array1 = `.ar1_`,
};

/* -------------------------------------------------------------------------- */

/+











































+/

/* -------------------------------------------------------------------------- */