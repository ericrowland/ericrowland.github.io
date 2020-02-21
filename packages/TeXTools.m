(* :Title: TeX Tools *)

(* :Context: TeXTools` *)

(* :Author: Eric Rowland *)

(* :Date: {2017, 3, 24} *)

(* :Package Version: 1.24 *)

(* :Mathematica Version: 11 *)

(* :Discussion:
	TeXTools automates some common tasks involved in writing papers in LaTeX.
	Documentation can be found at  http://people.hofstra.edu/Eric_Rowland/packages.html .
*)


BeginPackage["TeXTools`"]

TeXTools`Private`$SymbolList = {
	CommandArguments,
	DuplicateWords,
	ExportFigure,
	IgnoreComments,
	MisspelledWords,
	SymbolReplace,
	TeXCompile,
	TeXOpen,
	TeXPublish,
	TeXTableForm,
	$TeXFiguresDirectory,
	$TeXPublicationDirectory,
	$TeXSourceDirectory
}


Unprotect["TeXTools`*"]

Begin["`Private`"]


(* code for formatting usage messages *)

SetAttributes[box, HoldAll]
box[expressions__] :=
Module[{heldexpression, stringvariables, positions},
	heldexpression = Hold[expressions];
	stringvariables = Cases[heldexpression, String[string_String] :> string, Infinity];
	heldexpression = heldexpression /. {
		String[string_String] :> string,
		SubscriptList[arguments__] :> {SubscriptSequence[arguments]}
	};
	(* When you replace part of a held expression, the replacement isn't evaluated, so we have to evaluate before replacing. *)
	(* Replace each SubscriptList and SubscriptSequence expression with the expanded list.
	   This code doesn't support such expressions nested inside each other; but sorting the list of rules and using Fold[],
	   rather than passing it to ReplacePart directly, avoids  ReplacePart[f[x][y], {{{0, 1}} -> X, {{}} -> f[x][Y]}]  only performing one replacement
	   and allows these expressions to appear in a head and argument simultaneously. *)
	positions = Position[heldexpression, _[_SubscriptSequence]];
	heldexpression = Fold[
		ReplacePart,
		heldexpression,
		Sort[MapThread[
			Rule,
			{
				(* This extra list is required for the replacement to happen when the expression is Hold[SubscriptSequence[ ]]. *)
				List /@ positions,
				Replace[
					(* Arguments of SubscriptSequence (and SubscriptList) get evaluated here. *)
					Extract[heldexpression, positions],
					head_[SubscriptSequence[expr_, list_]] :>
						head @@ Replace[
							(Subscript[expr, #] &) /@ list,
							{
								Subscript[_, "..."] :> "\[Ellipsis]",
								Subscript[variable_, Null] :> variable
							},
							{1}
						],
					{1}
				]
			}
		]]
	];
	StringJoin[
		"\!\(\*",
		StringReplace[
			(* StringTake removes the outer Hold[ ]. *)
			StringTake[
				(* FullForm is needed to get quotes in the result, but it also writes { } as List[ ], which we don't necessarily need. *)
				ToString[FullForm[ToBoxes[heldexpression]]],
				{26, -8}
			],
			Join[
				("\"" <> IntegerString[#] <> "\"" -> "StyleBox[\"" <> IntegerString[#] <> "\", \"TR\"]" &) /@
					DeleteDuplicates[Cases[heldexpression, _Integer?NonNegative, Infinity, Heads -> True]],
				{
					"\"\\\"\\[CenterEllipsis]\\\"\"" -> "StyleBox[\"\\[CenterEllipsis]\", \"TR\"]",
					"\"\\\"\\[Ellipsis]\\\"\"" -> "StyleBox[\"\\[Ellipsis]\", \"TR\"]"
				},
				("\"\\\"" <> # <> "\\\"\"" -> "StyleBox[\"\\\"\\!\\(\\*StyleBox[\\\"" <> # <> "\\\",\\\"TI\\\"]\\)\\\"\", ShowStringCharacters->True]" &) /@
					stringvariables,
				(* This doesn't seem to apply to Greek letter variables. *)
				("\"\\\"" <> # <> "\\\"\"" -> "StyleBox[\"" <> # <> "\", \"TI\"]" &) /@
					DeleteDuplicates[Cases[heldexpression, Except[Alternatives @@ stringvariables, _String], Infinity, Heads -> True]]
			]
		],
		"\)"
	]
]


CommandArguments::usage =
box[CommandArguments[String["file"], String["command"]]] <> " gives a list of all arguments given to a command in a file.\n" <>
box[CommandArguments[String["command"]]] <> " finds arguments in \"paper.tex\"."

DuplicateWords::usage =
box[DuplicateWords[String["file"]]] <> " gives a list of duplicate words, along with the corresponding line numbers, in a file.\n" <>
box[DuplicateWords[]] <> " finds duplicate words in \"paper.tex\"."

ExportFigure::usage =
box[ExportFigure[String["file"], "graphics"]] <> " exports " <> box["graphics"] <> " as both \"" <> box["file"] <> ".eps\" and \"" <> box["file"] <> ".pdf\" to the directory given by $TeXFiguresDirectory."

IgnoreComments::usage =
"IgnoreComments is an option that specifies whether to ignore input on a line following %."

MisspelledWords::usage =
box[MisspelledWords[String["file"]]] <> " gives the words in a file that do not appear in one of the dictionaries, along with the corresponding line numbers.\n" <>
box[MisspelledWords[]] <> " finds misspelled words in \"paper.tex\"."

SymbolReplace::usage =
box[SymbolReplace[String["file"], String["newfile"], String["symbol"] -> String["newsymbol"]]] <> " renames a variable in all math environments in a TeX source file, and exports the result to a new file.\n" <>
box[SymbolReplace[String["file"], String["symbol"] -> String["newsymbol"]]] <> " exports the result to the original file after making a copy."

TeXCompile::usage =
box[TeXCompile[String["file"], String["ext"]]] <> " compiles the source file \"" <> box["file"] <> ".tex\" to \"" <> box["file"] <> "." <> box["ext"] <> "\".\n" <>
box[TeXCompile[String["file"]]] <> " compiles \"" <> box["file"] <> ".tex\" to \"" <> box["file"] <> ".dvi\".\n" <>
box[TeXCompile[]] <> " compiles \"paper.tex\" to \"paper.dvi\"."

TeXOpen::usage =
box[TeXOpen[String["file"]]] <> " opens the files \"" <> box["file"] <> ".tex\" and \"" <> box["file"] <> ".dvi\", as well as a command prompt for compiling the source.\n" <>
box[TeXOpen[]] <> " opens \"paper.tex\" and \"paper.dvi\"."

TeXPublish::usage =
box[TeXPublish[String["file"], String["newfile"], String["ext"]]] <> " compiles \"" <> box["file"] <> ".tex\" to \"" <> box["file"] <> "." <> box["ext"] <> "\" and copies it to the directory given by $TeXPublicationDirectory as \"" <> box["newfile"] <> "." <> box["ext"] <> "\".\n" <>
box[TeXPublish[String["file"], String["newfile"]]] <> " publishes \"" <> box["file"] <> ".tex\" as both \"" <> box["newfile"] <> ".pdf\" and \"" <> box["newfile"] <> ".ps\".\n" <>
box[TeXPublish[String["newfile"]]] <> " publishes \"paper.tex\".\n" <>
box[TeXPublish[]] <> " publishes \"paper.tex\" with a file name generated from the title of the paper."

TeXTableForm::usage =
box[TeXTableForm["array"]] <> " gives the TeX format of a two\[Hyphen]dimensional table " <> box["array"] <> ".
The options Alignment and TableHeadings can be given."

$TeXFiguresDirectory::usage =
"$TeXFiguresDirectory gives the directory where graphics files are exported."

$TeXPublicationDirectory::usage =
"$TeXPublicationDirectory gives the directory where finished papers are copied."

$TeXSourceDirectory::usage =
"$TeXSourceDirectory gives the directory where LaTeX source files are read."


$AbbreviationDictionary = {
	(* entities *)
	"AMS",
	"CNRS",
	"COFUND",
	"DMS",
	"FNRS",
	"IEEE",
	"LaCIM",
	"LIAFA",
	"MAA",
	"MSRI",
	"NSERC",
	"NSF",
	"OEIS",
	"UCSC",
	(* programs *)
	"REU",
	"VIGRE",
	(* technology *)
	"GPS",
	(* mathematical objects *)
	"DFA",
	"NFA",
	"PDA",
	"RSA"
}

$GeneralDictionary = {
	"advisor",
	"assistantship",
	"blog",
	"ethnicities",
	"instructorship",
	"preprint",
	"self-similar",
	"well-known"
}

$LatinDictionary = {
	"etc",
	"mutandis",
	"priori",
	"versa"
}

$MathDictionary = {
	"abelian",
	"additivity",
	"adic",
	"adically",
	"adjoint",
	"algebraicity",
	"ansatz",
	"ansatzes",
	"antiderivative",
	"antiderivatives",
	"aperiodicity",
	"associahedron",
	"autocorrelation",
	"autocorrelations",
	"automata",
	"automaticity",
	"automorphic",
	"bijection",
	"bijections",
	"bijective",
	"bijectively",
	"bijectivity",
	"bivariate",
	"breadth-first",
	"colorable",
	"combinatorially",
	"combinatorics",
	"componentwise",
	"conjecturally",
	"constant-recursive",
	"constructible",
	"context-free",
	"contrapositive",
	"coprime",
	"depth-first",
	"diagonalizable",
	"eigenspace",
	"eigenspaces",
	"eigenvector",
	"eigenvectors",
	"enumerative",
	"equinumerous",
	"finite-state",
	"floating-point",
	"foci",
	"formulae",
	"four-dimensional",
	"holonomic",
	"homotopic",
	"hypergeometric",
	"incongruent",
	"indecomposable",
	"indegree",
	"indegrees",
	"infimum",
	"injection",
	"injections",
	"injective",
	"modulo",
	"monic",
	"morphic",
	"multinomial",
	"multiplicatively",
	"multiset",
	"multisets",
	"multivariable",
	"nestedness",
	"non-decreasing",
	"non-increasing",
	"non-negative",
	"noncommutative",
	"noncommuting",
	"nondecreasing",
	"nondegenerate",
	"nonincreasing",
	"nonnegative",
	"nonperiodic",
	"nontrivially",
	"one-dimensional",
	"one-to-one",
	"outdegree",
	"outdegrees",
	"parameterized",
	"polynomial-recursive",
	"polynomial-time",
	"polytope",
	"poset",
	"posets",
	"prepend",
	"programmatically",
	"proven",
	"pushdown",
	"quasi-polynomial",
	"quasi-polynomials",
	"run-length",
	"self-dual",
	"self-similarity",
	"semilinear",
	"solvability",
	"subgraph",
	"subgraphs",
	"subinterval",
	"subintervals",
	"subpatterns",
	"subposet",
	"subposets",
	"subproduct",
	"subring",
	"subrings",
	"subsequence",
	"subsequences",
	"substring",
	"substrings",
	"subword",
	"subwords",
	"summand",
	"summands",
	"superfactorial",
	"supremum",
	"surjection",
	"surjections",
	"surjective",
	"termwise",
	"three-dimensional",
	"totient",
	"trinomial",
	"tuple",
	"tuples",
	"two-dimensional",
	"unary",
	"univariate",
	"vertices",
	"well-defined"
}

$PeopleDictionary = {
	"Adamczewski",
	"Allouche",
	"Amdeberhan",
	"Appel",
	"Baire",
	"Benoit",
	"Bergeron",
	"Beukers",
	"Bobbe",
	"Borel",
	"Borwein",
	"Brlek",
	"Bruijn",
	"Brummitt",
	"Bumby",
	"Callan",
	"Carlitz",
	"Cayley",
	"Charlier",
	"Chowla",
	"Christol",
	"Christoph",
	"Cloitre",
	"Cobham",
	"Collatz",
	"Currie",
	"Dejean",
	"Delannoy",
	"Deligne",
	"Denef",
	"Deutsch",
	"Doron",
	"Dyck",
	"Eilenberg",
	"Ekhad",		(* honorary person *)
	"Elkies",
	"Emeric",
	"Flajolet",
	"Foata",
	"Frobenius",
	"Furstenberg",
	"Garity",
	"Gessel",
	"Glaisher",
	"Golomb",
	"Goulden",
	"Granville",
	"Guay-Paquet",
	"Haar",
	"Hadamard",
	"Haken",
	"Harary",
	"Hensel",
	"Hofstra",
	"Holub",
	"Hurwitz",
	"Jacobsthal",
	"Jean-Paul",
	"Kakutani",
	"Kauers",
	"Kimberling",
	"Koblitz",
	"Kolakoski",
	"Kolmogorov",
	"Koutschan",
	"Krattenthaler",
	"Kummer",
	"Kupin",
	"Lehmer",
	"Lengyel",
	"Liouville",
	"Lipschitz",
	"Lipshitz",
	"Lothaire",
	"Loxton",
	"MacMahon",
	"Mangoldt",
	"Mathieu",
	"Matiyasevich",
	"Mazur",
	"Mersenne",
	"Mordell",
	"Motzkin",
	"Neumann",
	"Noonan",
	"Odlyzko",
	"Ostrowski",
	"Parikh",
	"Perron",
	"Phillipe",
	"Pitman",
	"Plouffe",
	"Pochhammer",
	"Poorten",
	"Prins",
	"Pudwell",
	"Rampersad",
	"Rauzy",
	"Reem",
	"Reutenauer",
	"Ribenboim",
	"Rigo",
	"Riordan",
	"Risch",
	"Rowland",
	"Schaeffer",
	"Sedgewick",
	"Shallit",
	"Shalosh",		(* honorary person *)
	"Silverman",
	"Srecko",
	"Stickelberger",
	"Stoll",
	"Tewodros",
	"Thue",
	"Tutte",
	"Vandermonde",
	"Wieferich",
	"Wilf",
	"Wolstenholme",
	"Yassawi",
	"Zaphod",
	"Zeilberger"
}

$PlaceDictionary = {
	"Banff",
	"Bloomington",
	"Champaign",
	"Hempstead",
	"Las",
	"Marseille",
	"Oberwolfach",
	"Obispo",
	"Peterborough",
	"Piscataway",
	"Puerto"
}


$commandprefix =
	Switch[$OperatingSystem,
		"MacOSX",
			"/usr/texbin/",
		_,
			""
	]

filename[file_, extension_ : "tex", OptionsPattern[]] :=
If[FileNameDepth[file] > 1,
	file,
	FileNameJoin[{
		If[TrueQ[OptionValue[Graphics]], $TeXFiguresDirectory, $TeXSourceDirectory],
		If[FileExtension[file] != "",
			file,
			file <> "." <> extension
		]
	}]
]
Options[filename] = {Graphics -> False}

MatchPairs[string_String, openpattern_, closepattern_] :=
Module[{openpositions, closepositions, positions = {}, stack = {}},
	openpositions = StringPosition[string, openpattern];
	closepositions = StringPosition[string, closepattern];
	Function[p,
		If[stack == {},
			If[MemberQ[openpositions, p],
				AppendTo[stack, p],
				AppendTo[positions, {Null, p}]
			],
			If[MemberQ[closepositions, p],
				AppendTo[positions, {Last[stack], p}];
				stack = Most[stack]
				,
				AppendTo[stack, p]
			]
		]
	] /@ Union[openpositions, closepositions];
	Join[
		positions,
		{#, Null} & /@ stack
	]
]

StringReplaceRepeated[
	s_String,
	rules : _Rule | _RuleDelayed | {(_Rule | _RuleDelayed) ...}
] := FixedPoint[StringReplace[#, rules] &, s]


CommandArguments[file_String : "paper", commandpattern_, OptionsPattern[]] :=
Module[{text = Import[filename[file], "Text"], pairs, failed},
	failed = Catch[
		If[text === $Failed, Throw[True]];
		If[OptionValue[IgnoreComments], text = StringReplace[text, "%" ~~ Except["\n"] ... ~~ "\n" -> ""]];
		(* DeleteCases gets rid of unmatched brackets, which can legitimately arise for example in  \phantom{\Big\{} . *)
		pairs = {#[[1, 1]], #[[2, 2]]} & /@ DeleteCases[
			MatchPairs[text, "{", "}"],
			{_, Null}
		];
		pairs = Function[endposition,
			StringTake[text, {2, -1} + #] & /@
				Partition[
					First /@ Most[NestWhileList[
						Cases[pairs, {First[#] + 1, end_} :> end] &,
						{Last[endposition]},
						# != {} &
					]],
					2,
					1
				]
		] /@ StringPosition[text, commandpattern];
		False
	];
	pairs /; !failed
]
Options[CommandArguments] = {IgnoreComments -> True}
SyntaxInformation[CommandArguments] = {"ArgumentsPattern" -> {_, _., OptionsPattern[]}}

(* TODO This doesn't detect duplicate words separated by a line break. *)
DuplicateWords[file_String : "paper", OptionsPattern[]] :=
Module[{text = Import[filename[file], "Text"], phrases, duplicatewords, failed},
	failed = Catch[
		If[text === $Failed, Throw[True]];
		If[OptionValue[IgnoreComments], text = StringReplace[text, "%" ~~ Except["\n"] ... ~~ "\n" -> "\n"]];
		text = StringReplace[text, "~" -> " "];
		phrases = StringSplit[text, "," | ";" | "."];
		duplicatewords = Join @@ (Cases[Partition[StringSplit[#], 2, 1], {word_, word_} :> word] &) /@ phrases;
		duplicatewords = DeleteDuplicates[duplicatewords];
		duplicatewords = {#[[1, 1]], Last /@ #} & /@
			GatherBy[Flatten[Thread /@ DeleteCases[
				MapIndexed[
					Function[{line, index}, {
						StringCases[
							line,
							StringExpression[
								StartOfString | Except[LetterCharacter],
								word : Alternatives @@ duplicatewords ~~ Whitespace ~~ word_,
								EndOfString | Except[LetterCharacter]
							] :> word,
							Overlaps -> True
						],
						First[index]
					}],
					StringSplit[text, "\n", All]
				],
				{{}, _}
			], 1], First];
		False
	];
	duplicatewords /; !failed
]
Options[DuplicateWords] = {IgnoreComments -> True}
SyntaxInformation[DuplicateWords] = {"ArgumentsPattern" -> {_., OptionsPattern[]}}

ExportFigure[file_String, graphics_] :=
With[{directory = DirectoryName[filename[file, "eps", Graphics -> True]]},
	If[!DirectoryQ[directory],
		Message[ExportFigure::crdir, directory]; CreateDirectory[directory]
	];
	{
		Export[filename[file, "eps", Graphics -> True], graphics],
		Export[filename[file, "pdf", Graphics -> True], graphics]
	}
]
SyntaxInformation[ExportFigure] = {"ArgumentsPattern" -> {_, _}}
ExportFigure::crdir = "The directory `1` was created."

MisspelledWords[file_String : "paper", OptionsPattern[]] :=
Module[{text = Import[filename[file], "Text"], misspelledwords, lettercharacter = LetterCharacter | "-" | "'", failed},
	failed = Catch[
		If[text === $Failed, Throw[True]];
		If[OptionValue[IgnoreComments], text = StringReplace[text, "%" ~~ Except["\n"] ... ~~ "\n" -> "\n"]];
		text = StringReplace[text, "~" -> " "];
		(* Get rid of punctuation, and prevent LaTeX commands from being spell-checked. *)
		misspelledwords = StringReplace[#,
			{
				StringExpression[
					StartOfString,
					prefix : (Except[lettercharacter] ...),
					word : (lettercharacter ..),
					suffix : (Except[lettercharacter] ...),
					EndOfString
				] :>
					If[StringMatchQ[prefix, ___ ~~ "\\"],
						"",
						word
					],
				StringExpression[
					StartOfString,
					word : (lettercharacter ..),
					"\\",
					suffix__,
					EndOfString
				] :> word
			}
		] & /@ StringSplit[text, Whitespace | "{" | "}" | "--" | "---" | "''"];
		(* Don't report "-regular" from "$2$-regular" or "well'" from "`very well'". *)
		(* TODO Don't report "$k$-regular". *)
		misspelledwords = StringReplace[#,
			{
				StringExpression[
					StartOfString,
					"-",
					word : (lettercharacter ..),
					EndOfString
				] :> word,
				StringExpression[
					StartOfString,
					word : (lettercharacter ..),
					"-" | "'",
					EndOfString
				] :> word
			}
		] & /@ misspelledwords;
		misspelledwords = Select[
			misspelledwords,
			StringMatchQ[#, lettercharacter ..] &
		];
		misspelledwords = Select[
			DeleteDuplicates[misspelledwords],
			StringLength[#] > 2 &&
				DictionaryLookup[#, IgnoreCase -> True] == {} &&
				!MemberQ[Join[$GeneralDictionary, $MathDictionary], ToLowerCase[#]] &&
				!MemberQ[Join[$AbbreviationDictionary, $LatinDictionary, $PeopleDictionary, $PlaceDictionary], #] &
		];
		misspelledwords = {#[[1, 1]], Last /@ #} & /@
			GatherBy[Flatten[Thread /@ DeleteCases[
				MapIndexed[
					Function[{line, index}, {
						StringCases[
							line,
							StringExpression[
								StartOfString | Except[LetterCharacter],
								word : Alternatives @@ misspelledwords,
								EndOfString | Except[LetterCharacter]
							] :> word,
							Overlaps -> True
						],
						First[index]
					}],
					StringSplit[text, "\n", All]
				],
				{{}, _}
			], 1], First];
		misspelledwords = {
			"Capitalized" -> Select[misspelledwords, UpperCaseQ[StringTake[First[#], 1]] &],
			"Hyphenated" -> Select[misspelledwords, StringMatchQ[First[#], __ ~~ "-" ~~ __] &],
			"Other" -> Select[misspelledwords, !(UpperCaseQ[StringTake[First[#], 1]] || StringMatchQ[First[#], __ ~~ "-" ~~ __] || StringMatchQ[First[#], __ ~~ "'s"]) &],
			"Possessive" -> Select[misspelledwords, StringMatchQ[First[#], __ ~~ "'s"] &]
		};
		misspelledwords = DeleteCases[misspelledwords, _ -> {}];
		False
	];
	misspelledwords /; !failed
]
Options[MisspelledWords] = {IgnoreComments -> True}
SyntaxInformation[MisspelledWords] = {"ArgumentsPattern" -> {_., OptionsPattern[]}}

SymbolReplace[f_String, rule : (_String -> _String)] :=
With[{file = filename[f]},
	Quiet[DeleteFile[file <> "~"], DeleteFile::nffil];
	CopyFile[file, file <> "~"];
	SymbolReplace[file, file, rule]
]
SymbolReplace[file_String, newfile_String, symbol_String -> newsymbol_String] :=
Module[{text = Import[filename[file], "Text"], pairs},
	(* We could find all pairs at once, except that $$ gets picked up as two $s. *)
(* TODO Although as it is nested environments break things because StringReplacePart doesn't replace overlapping strings. *)
	pairs = Join[
		MatchPairs[
			(* Replace double dollar signs and text dollar signs with symbols that won't match the delimiter patterns. *)
			StringReplace[text, "$$" | "\\$" -> "  "],
			"\\begin{math}" | "\\(" | "$",
			"\\end{math}" | "\\)" | "$"
		],
		MatchPairs[
			(* Replace text dollar signs with symbols that won't match the delimiter patterns. *)
			StringReplace[text, "\\$" -> "  "]
			,
(* TODO add multline, multline*, flalign, alignat, etc. *)
			"\\begin{displaymath}" | "\\[" | "$$" |
			"\\begin{equation}" | (*"\\begin{equation*}" |*) "\\begin{align}" | "\\begin{align*}" |
			"\\begin{eqnarray}" (*| "\\begin{eqnarray*}"*)
			,
			"\\end{displaymath}" | "\\]" | "$$" |
			"\\end{equation}" | (*"\\end{equation*}" |*) "\\end{align}" | "\\end{align*}" |
			"\\end{eqnarray}" (*| "\\end{eqnarray*}"*)
		]
	];
	If[!FreeQ[pairs, Null], Return[$Failed]];
	pairs = {#[[1, 1]], #[[2, 2]]} & /@ pairs;
	Export[
		filename[newfile],
		StringReplacePart[
			text,
			StringReplaceRepeated[
				StringTake[text, #],
				a : Except[LetterCharacter] ~~ symbol ~~ z : Except[LetterCharacter] :> a <> newsymbol <> z
			] & /@ pairs,
			pairs
		],
		"Text"
	]
]
SyntaxInformation[SymbolReplace] = {"ArgumentsPattern" -> {_, _, _.}}

TeXCompile[file_String : "paper"] :=
	TeXCompile[file, "pdf"]
TeXCompile[file_String, "dvi"] :=
	Run[
		"cd", "\"" <> $TeXSourceDirectory <> "\"",
		"&&",
		$commandprefix <> "latex", "\"" <> filename[file] <> "\""
	]
TeXCompile[file_String, "pdf"] :=
	Run[
		"cd", "\"" <> $TeXSourceDirectory <> "\"",
		"&&",
		$commandprefix <> "pdflatex", "\"" <> filename[file] <> "\""
	]
TeXCompile[file_String, "ps"] := (
	TeXCompile[file, "dvi"];
	Run[
		"cd", "\"" <> $TeXSourceDirectory <> "\"",
		"&&",
		$commandprefix <> "dvips", "\"" <> filename[file, "dvi"] <> "\""
	];
)
SyntaxInformation[TeXCompile] = {"ArgumentsPattern" -> {_., _.}}

TeXOpen[file_String : "paper"] := (
	SystemOpen[filename[file]];
	Pause[.5];
	Switch[$OperatingSystem,
		"MacOSX",
			Run[
				"open -a Terminal",
				"\"" <> $TeXSourceDirectory <> "\""
			];
			SystemOpen[filename[file, "pdf"]],
		_,
			Run[
				"start cmd /k",
(* This doesn't cause files on external drives to open as I hoped it would.
				If[StringLength[$TeXSourceDirectory] >= 3 && StringMatchQ[$TeXSourceDirectory, Except["C"] ~~ ":\\" ~~ ___],
					"",
					"cd"
				],
*)
				"cd",
				$TeXSourceDirectory
			];
			SystemOpen[filename[file, "dvi"]]
	];
)
SyntaxInformation[TeXOpen] = {"ArgumentsPattern" -> {_.}}

TeXPublish[file_String, newfile_String, ext_String] :=
	TeXPublish[file, newfile, {ext}]
TeXPublish[file_String : "paper", newfile_String, extensions : {("dvi" | "pdf" | "ps") ...} : {"pdf", "ps"}] :=
(
	If[MemberQ[extensions, "pdf"],
		TeXCompile[file, "pdf"];
		TeXCompile[file, "pdf"]
	];
	If[MemberQ[extensions, "dvi" | "ps"],
		TeXCompile[file, "dvi"];
		TeXCompile[file, "dvi"]
	];
	If[MemberQ[extensions, "ps"],
		TeXCompile[file, "ps"]
	];
	Function[ext,
		Quiet[DeleteFile[FileNameJoin[{$TeXPublicationDirectory, newfile <> "." <> ext}]], DeleteFile::nffil];
		CopyFile[filename[file, ext], FileNameJoin[{$TeXPublicationDirectory, newfile <> "." <> ext}]]
	] /@ extensions
)
TeXPublish[] :=
Module[{arguments, title, failed},
	failed = Catch[
		arguments = CommandArguments["\\title"];
		If[!MatchQ[arguments, {{_String}, ___List}],
			Message[TeXPublish::title]; Throw[True]
		];
		If[Length[arguments] >= 2,
			Message[TeXPublish::titles]
		];
		title = arguments[[1, 1]];
		title = StringReplace[title, {"$" -> "", "\\" -> ""}];
		title = StringReplaceRepeated[title, "  " -> " "];
		title = StringReplace[title, " " -> "_"];
		False
	];
	TeXPublish[title] /; !failed
]
SyntaxInformation[TeXPublish] = {"ArgumentsPattern" -> {_., _., _.}}
TeXPublish::title = "No title identified in the source file."
TeXPublish::titles = "Multiple titles found in the source file; using the first."

TeXTableForm[list : {___List}, OptionsPattern[]] :=
Module[{table = list, columnalignments, rowheadings, columnheadings, columncount},
	{rowheadings, columnheadings} = Replace[
		OptionValue[TableHeadings],
		{labels : {_, _} :> labels, {r_} :> {r, None}, _ -> {None, None}}
	];
	If[ListQ[rowheadings],
		table = Join @@@ Transpose[{List /@ PadRight[rowheadings, Length[table], Null], table}]
	];
	columncount = Max[Length /@ table];
	If[ListQ[columnheadings],
		PrependTo[table, PadRight[Join[If[ListQ[rowheadings], {Null}, {}], columnheadings], columncount, Null]]
	];
	columnalignments = StringJoin[Replace[
		Replace[
			OptionValue[Alignment],
			{
				{h_List, ___} :> PadRight[Join[If[ListQ[rowheadings], {Center}, {}], h], columncount, Center],
				h : Except[_List] :> ConstantArray[h, columncount],
				_ :> ConstantArray[Center, columncount]
			}
		],
		{Left -> "l", Right -> "r", _ -> "c"},
		{1}
	]];
	If[ListQ[rowheadings], columnalignments = StringInsert[columnalignments, "|", 2]];
	table = Riffle[
		StringJoin[Riffle[#, " & "]] & /@
			Map[ToString[Replace[#, Null -> ""], TeXForm] &, table, {2}],
		" \\\\\n"
	];
	If[ListQ[columnheadings], table = ReplacePart[table, 2 -> " \\\\ \\hline\n"]];
	StringJoin[
		"\<",
		"\\[\n\\begin{array}{",
		columnalignments,
		"}\n",
		table,
		"\n\\end{array}\n\\]",
		"\>"
	]
]
Options[TeXTableForm] = {Alignment -> Center, TableHeadings -> None}
SyntaxInformation[TeXTableForm] = {"ArgumentsPattern" -> {{__}, OptionsPattern[]}}

If[!ValueQ[$TeXFiguresDirectory], $TeXFiguresDirectory := FileNameJoin[{$TeXSourceDirectory, "figures"}]]
If[!ValueQ[$TeXPublicationDirectory], $TeXPublicationDirectory = $InitialDirectory]
If[!ValueQ[$TeXSourceDirectory],
	$TeXSourceDirectory =
		Quiet[NotebookDirectory[], NotebookDirectory::nosv] /. $Failed -> $InitialDirectory
]


End[]

Protect["TeXTools`*"]
Unprotect[$TeXFiguresDirectory, $TeXPublicationDirectory, $TeXSourceDirectory]

EndPackage[]
