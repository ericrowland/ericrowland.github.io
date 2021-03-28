(* :Title: Equivalent Words *)

(* :Context: EquivalentWords` *)

(* :Author: Eric Rowland *)
(* First version written jointly with Bobbe Cooper in July--August 2002. *)

(* :Date: {2014, 6, 1} *)

(* :Package Version: 1.12 *)

(* :Mathematica Version: 9 *)

(* :Discussion:
	EquivalentWords is a package for studying automorphic conjugacy in the free group F_2.
	Documentation can be found at  https://ericrowland.github.io/packages.html .
*)

(* :Acknowledgement:
	A small portion of this code was originally adapted from a Maple program by Michael Lau:
	"A Computer Implementation of Whitehead's Algorithm", Oregon State University REU, 1997.
*)


BeginPackage["EquivalentWords`"]

EquivalentWords`Private`$SymbolList = {
	AlternatingWordQ,
	ApplyAutomorphism,
	CancelInverses,
	CanonicalPermutation,
	Children,
	ClassifyWords,
	CountAndClassifyWords,
	CountWords,
	EquivalenceClass,
	EquivalentWords,
	EquivalentWordsQ,
	ExtendWord,
	GatherByInvariant,
	InverseGenerator,
	MinimalWordQ,
	OneLetterAutomorphismEquivalentWords,
	ProvablyIsolatedWordQ,
	RCPCandidates,
	RCPRepresentative,
	RCPWords,
	RootWordClasses,
	RootWordQ,
	RootWords,
	SortWords,
	SyllableCount,
	WordEquivalenceClasses,
	$AllAutomorphisms,
	$Automorphisms
}


Unprotect["EquivalentWords`*"]

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


AlternatingWordQ::usage =
box[AlternatingWordQ["word"]] <> " yields True if " <> box["word"] <> " has no adjacent identical letters, and False otherwise."

ApplyAutomorphism::usage =
box[ApplyAutomorphism[{"A", "x"}, "word"]] <> " applies to the cyclic word " <> box["word"] <> " the Whitehead type II automorphism " <> box[{"A", "x"}] <> ", where " <> box["A"] <> " is a list of generators and " <> box["x"] <> " is a generator."

CancelInverses::usage =
box[CancelInverses["word"]] <> " cancels all adjacent inverses in the cyclic word " <> box["word"] <> "."

CanonicalPermutation::usage =
box[CanonicalPermutation["word"]] <> " returns the lexicographically least word in the orbit of " <> box["word"] <> " under permutations of the generators."

Children::usage =
box[Children["word"]] <> " gives the RCP words that immediately descend from (by prepending \"a\" to a cycled permutation of) the RCP word " <> box["word"] <> ".\n" <>
box[Children["list"]] <> " gives the RCP words that immediately descend from any word in " <> box["list"] <> "."

ClassifyWords::usage =
box[ClassifyWords["word"]] <> " breaks up a list of RCP words of the same length by the weights of the generators and partitions the list into equivalence classes."

CountAndClassifyWords::usage =
box[CountAndClassifyWords["n"]] <> " classifies words of length " <> box["n"] <> " by equivalence class, counts the classes of each size, establishes the root word classes, and counts the root word classes of each size, as well as giving in the first entry statistics about the number of objects considered at each step."

CountWords::usage =
box[CountWords["n"]] <> " counts the classes of length\[Hyphen]" <> box["n"] <> " words of each size and counts the root word classes of each size, as well as giving in the first entry statistics about the number of objects considered at each step."

EquivalenceClass::usage =
box[EquivalenceClass["word"]] <> " gives a list of all minimal RCP words equivalent to " <> box["word"] <> "."

EquivalentWords::usage =
box[EquivalentWords["word"]] <> " gives a list of cyclically\[Hyphen]reduced words that are equivalent to " <> box["word"] <> ", among which are all the minimal RCP words that are equivalent to " <> box["word"] <> "."

EquivalentWordsQ::usage =
box[EquivalentWordsQ[SubscriptSequence["word", {1, 2}]]] <> " yields True if " <> box[Subscript["word", 1]] <> " and " <> box[Subscript["word", 2]] <> " are equivalent, and False otherwise."

ExtendWord::usage =
box[ExtendWord["word", "n"]] <> " gives a list of 1\[Hyphen]letter extensions of " <> box["word"] <> " toward RCP\[Hyphen]candidate " <> box["n"] <> "\[Hyphen]letter extensions."

GatherByInvariant::usage =
"GatherByInvariant is an option for ClassifyWords that specifies whether a list of words should first be classified by minimum generator weight before being classified by equivalence class."

InverseGenerator::usage =
box[InverseGenerator["generator"]] <> " gives the inverses of the generators \"a\", \"b\", \"A\", and \"B\"."

MinimalWordQ::usage =
box[MinimalWordQ["word"]] <> " yields True if " <> box["word"] <> " is of minimal length in its equivalence class, and False otherwise."

OneLetterAutomorphismEquivalentWords::usage =
box[OneLetterAutomorphismEquivalentWords["word"]] <> " gives a list of all words equivalent to " <> box["word"] <> " under a cycle or under a single Whitehead type II automorphism that does not increase its length."

ProvablyIsolatedWordQ::usage =
box[ProvablyIsolatedWordQ["word"]] <> " yields True if " <> box["word"] <> " can be proved to be isolated by counting syllables, and False otherwise.
(A value of False therefore does not necessarily imply that the word is not isolated.)"

RCPCandidates::usage =
box[RCPCandidates["n"]] <> " gives a list of (not necessarily minimal) RCP\[Hyphen]candidate words of length " <> box["n"] <> ".\n" <>
box[RCPCandidates["word", "n"]] <> " gives a list of (not necessarily minimal) RCP\[Hyphen]candidate " <> box["n"] <> "\[Hyphen]letter extensions of " <> box["word"] <> ".\n" <>
box[RCPCandidates["list", "n"]] <> " extends a list of words."

RCPRepresentative::usage =
box[RCPRepresentative["word"]] <> " returns the first in a lexicographic ordering of all cycled permutations of " <> box["word"] <> "."

RCPWords::usage =
box[RCPWords["n"]] <> " gives a list of all minimal RCP words of length " <> box["n"] <> "."

RootWordClasses::usage =
box[RootWordClasses["n"]] <> " gives the equivalence classes of all RCP root words of length " <> box["n"] <> "."

RootWordQ::usage =
box[RootWordQ["word"]] <> " yields True if " <> box["word"] <> " is a root word, and False otherwise."

RootWords::usage =
box[RootWords["n"]] <> " gives a list of all RCP root words of length " <> box["n"] <> "."

SortWords::usage =
box[SortWords["list"]] <> " sorts a list of words according to the ordering \"a\", \"b\", \"A\", \"B\"."

SyllableCount::usage =
box[SyllableCount["word", "syllable"]] <> " gives the number of occurrences of the subword " <> box["syllable"] <> " and its inverse in a cyclic word " <> box["word"] <> "."

WordEquivalenceClasses::usage =
box[WordEquivalenceClasses["n"]] <> " gives the equivalence classes of all RCP words of length " <> box["n"] <> ".\n" <>
box[WordEquivalenceClasses["n", "i"]] <> " gives the equivalence classes of all RCP words of length " <> box["n"] <> " whose minimal generator weight is " <> box["i"] <> "."

$AllAutomorphisms::usage =
"$AllAutomorphisms is a list of the eight one\[Hyphen]letter automorphisms on " <> box[Subscript["F", 2]] <> "."

$Automorphisms::usage =
"$Automorphisms is a list of four one\[Hyphen]letter automorphisms on " <> box[Subscript["F", 2]] <> " that are distinct modulo Inn " <> box[Subscript["F", 2]] <> "."


If[$VersionNumber < 6,
	Accumulate[list_List] := Rest[FoldList[Plus, 0, list]];
	Divisible[n_, m_] := Mod[n, m] == 0;
	Tally[list_] := {#[[1]], Length[#]} & /@ Split[Sort[list]]
]

If[$VersionNumber < 9,
	StringRotateRight[string_String, n_Integer] :=
		StringTake[string, {Mod[-n + 1, StringLength[string], 1], -1}] <> StringTake[string, Mod[-n, StringLength[string]]]
]


RunLengths[word_String] := Length /@ Split[Characters[word]]


InverseGenerator["a"] = "A"
InverseGenerator["b"] = "B"
InverseGenerator["A"] = "a"
InverseGenerator["B"] = "b"
SyntaxInformation[InverseGenerator] = {"ArgumentsPattern" -> {_}}

AlternatingWordQ[word_String] := Max[RunLengths[word]] <= 1
SyntaxInformation[AlternatingWordQ] = {"ArgumentsPattern" -> {_}}

SortWords[words_List] :=
StringReplace[
	Sort[StringReplace[words, {"A" -> "y", "B" -> "z"}]],
	{"y" -> "A", "z" -> "B"}
]
SyntaxInformation[SortWords] = {"ArgumentsPattern" -> {_}}

SyllableCount[word_String, syllable_String] /; StringLength[word] < StringLength[syllable] := 0
SyllableCount[word_String, syllable : Except["", _String]] :=
StringCount[
	word <> StringTake[word, StringLength[syllable] - 1],
	syllable | StringJoin[InverseGenerator /@ Reverse[Characters[syllable]]],
	Overlaps -> True
]
SyntaxInformation[SyllableCount] = {"ArgumentsPattern" -> {_, _}}

CancelInverses[word_String] :=
FixedPoint[
	StringReplace[#, {
		StartOfString ~~ "a" ~~ x___ ~~ "A" ~~ EndOfString :> x,
		StartOfString ~~ "b" ~~ x___ ~~ "B" ~~ EndOfString :> x,
		StartOfString ~~ "A" ~~ x___ ~~ "a" ~~ EndOfString :> x,
		StartOfString ~~ "B" ~~ x___ ~~ "b" ~~ EndOfString :> x
	}] &,
	FixedPoint[
		StringReplace[#,
			{"aA" -> "", "bB" -> "", "Aa" -> "", "Bb" -> ""}
		] &,
		word
	]
]
SyntaxInformation[CancelInverses] = {"ArgumentsPattern" -> {_}}

CanonicalPermutation[""] = ""
CanonicalPermutation[word_String] :=
With[{position = First /@ StringPosition[word, Except[StringTake[word, {1}]], 1]},
	If[position != {},
		StringReplace[word, {
			StringTake[word, {1}] -> "a",
			InverseGenerator[StringTake[word, {1}]] -> "A",
			StringTake[word, {First[position]}] -> "b",
			InverseGenerator[StringTake[word, {First[position]}]] -> "B"
		}],
		StringJoin[ConstantArray["a", StringLength[word]]]
	]
]
SyntaxInformation[CanonicalPermutation] = {"ArgumentsPattern" -> {_}}

RCPRepresentative[""] = ""
RCPRepresentative[word_String] :=
Module[{runlengths = RunLengths[word], w},
	If[StringTake[word, {1}] == StringTake[word, {-1}] && Length[runlengths] > 1,
		w = StringRotateRight[word, Last[runlengths]];
		runlengths = Prepend[Take[runlengths, {2, -2}], First[runlengths] + Last[runlengths]],
		w = word
	];
	First[SortWords[
		CanonicalPermutation[StringRotateRight[w, -#]] & /@
			Accumulate[runlengths][[
				(Flatten[Position[runlengths, Max[runlengths]]] - 1) /. 0 -> -1
			]]
	]]
]
SyntaxInformation[RCPRepresentative] = {"ArgumentsPattern" -> {_}}

ExtendWord[word_String, n_Integer?Positive] :=
Module[{letters},
	If[StringCount[word, "b"] == 0,
		letters = {"a", "b"},
		letters = DeleteCases[{"a", "b", "A", "B"}, InverseGenerator[StringTake[word, {-1}]]];
		If[(First[#] == Last[#] &) @ RunLengths[word],
			letters = DeleteCases[letters, StringTake[word, {-1}]]];
		If[n == 1, letters = DeleteCases[letters, "a" | "A"]]
	];
	(word <> # &) /@ letters
]
SyntaxInformation[ExtendWord] = {"ArgumentsPattern" -> {_, _}}

RCPCandidates[n_Integer?NonNegative] :=
Which[
	n == 0, {""},
	n == 1 || Divisible[n, 4], RCPCandidates[{"a"}, n - 1],
	True, RCPCandidates[{"aa"}, n - 2]
]
RCPCandidates[word_String, n_Integer?NonNegative] := RCPCandidates[{word}, n]
RCPCandidates[words_List, 0] := words
RCPCandidates[words_List, n_Integer?Positive] :=
	RCPCandidates[Flatten[ExtendWord[#, n] & /@ words], n - 1]
SyntaxInformation[RCPCandidates] = {"ArgumentsPattern" -> {_, _.}}

ApplyAutomorphism[{{y_String}, x_String}, word_String] :=
CancelInverses[StringReplace[word, {
	y -> y <> x,
	InverseGenerator[y] -> InverseGenerator[x] <> InverseGenerator[y]
}]]
ApplyAutomorphism[{A_List, x_String}, word_String] :=
CancelInverses[StringReplace[
	word,
	# -> If[MemberQ[A, InverseGenerator[#]], InverseGenerator[x], ""] <> # <> If[MemberQ[A, #], x, ""] & /@
		{"a", "b", "A", "B"}
]]
SyntaxInformation[ApplyAutomorphism] = {"ArgumentsPattern" -> {_, _}}

OneLetterAutomorphismEquivalentWords[word_String] :=
Union[
	StringRotateRight[word, #] & /@ Range[StringLength[word] - 1],
	Select[
		ApplyAutomorphism[#, word] & /@ $Automorphisms,
		StringLength[#] <= StringLength[word] &
	]
]
SyntaxInformation[OneLetterAutomorphismEquivalentWords] = {"ArgumentsPattern" -> {_}}

EquivalentWords[word_String] :=
Module[{words = {word}, oldwords, newwords = {word}},
	While[newwords != {},
		oldwords = words;
		words = Union[words, Sequence @@ OneLetterAutomorphismEquivalentWords /@ newwords];
		newwords = Complement[words, oldwords]
	];
	Union[CanonicalPermutation /@ words]
]
SyntaxInformation[EquivalentWords] = {"ArgumentsPattern" -> {_}}

(* This is usually being used to classify words with the same minimum generator weight. *)
classifySameLengthWords[list_List] :=
Module[{classes = {}, words = list, class},
	While[words != {},
		class = Intersection[words, EquivalentWords[First[words]]];
		AppendTo[classes, class];
		words = Complement[words, class]
	];
	classes
]

ClassifyWords[list_List /; Equal @@ StringLength /@ list, OptionsPattern[]] :=
Module[{isolated},
	isolated = Select[list, ProvablyIsolatedWordQ];
	StringReplace[#, {"y" -> "A", "z" -> "B"}] & /@ Sort[Join[
		List /@ isolated,
		Sort[StringReplace[#, {"A" -> "y", "B" -> "z"}]] & /@
			If[TrueQ[OptionValue[GatherByInvariant]],
				Flatten[classifySameLengthWords /@ Map[
					Last,
					Split[
						Sort[
							{Min[SyllableCount[#, "a"], SyllableCount[#, "b"]], #} & /@
								Complement[list, isolated]
						],
						Equal @@ First /@ {##} &
					],
					{2}
				], 1],
				classifySameLengthWords[Complement[list, isolated]]
			]
	]]
]
Options[ClassifyWords] = {GatherByInvariant -> True}
SyntaxInformation[ClassifyWords] = {"ArgumentsPattern" -> {_, OptionsPattern[]}}

(* TODO I don't need to fully execute CancelInverses in the following functions;
   I just need to check that there are no adjacent inverses. *)

ProvablyIsolatedWordQ[word_String] := CancelInverses[word] == word &&
Abs[SyllableCount[word, "ab"] - SyllableCount[word, "aB"]] <
	Min[SyllableCount[word, "aa"], SyllableCount[word, "bb"]]
SyntaxInformation[ProvablyIsolatedWordQ] = {"ArgumentsPattern" -> {_}}

MinimalWordQ[word_String] := CancelInverses[word] == word &&
Abs[SyllableCount[word, "ab"] - SyllableCount[word, "aB"]] <=
	Min[SyllableCount[word, "aa"], SyllableCount[word, "bb"]]
SyntaxInformation[MinimalWordQ] = {"ArgumentsPattern" -> {_}}

RootWordQ[word_String] := CancelInverses[word] == word &&
Abs[SyllableCount[word, "ab"] - SyllableCount[word, "aB"]] ==
	SyllableCount[word, "aa"] == SyllableCount[word, "bb"]
SyntaxInformation[RootWordQ] = {"ArgumentsPattern" -> {_}}

RCPWords[n_Integer?NonNegative] :=
Union[RCPRepresentative /@ Select[RCPCandidates[n], MinimalWordQ]]
SyntaxInformation[RCPWords] = {"ArgumentsPattern" -> {_}}

WordEquivalenceClasses[n_Integer?NonNegative] := ClassifyWords[RCPWords[n]]
WordEquivalenceClasses[n_Integer?NonNegative, i_Integer?NonNegative] :=
ClassifyWords[
	Select[RCPWords[n], Min[SyllableCount[#, "a"], SyllableCount[#, "b"]] == i &],
	GatherByInvariant -> False
]
SyntaxInformation[WordEquivalenceClasses] = {"ArgumentsPattern" -> {_, _.}}

RootWords[n_Integer?NonNegative] :=
Union[RCPRepresentative /@ Select[RCPCandidates[n], RootWordQ]]
SyntaxInformation[RootWords] = {"ArgumentsPattern" -> {_}}

RootWordClasses[n_Integer?NonNegative] := ClassifyWords[RootWords[n]]
SyntaxInformation[RootWordClasses] = {"ArgumentsPattern" -> {_}}

CountWords[n_Integer?NonNegative] :=
Module[{originalwords, rcpwords, equivalenceclasses, rootwordclasses},
	originalwords = RCPCandidates[n];
	rcpwords = Union[RCPRepresentative /@ Select[originalwords, MinimalWordQ]];
	equivalenceclasses = ClassifyWords[rcpwords];
	rootwordclasses = Select[equivalenceclasses, RootWordQ[First[#]] &];
	{
		{
			Length[originalwords],
			Length[rcpwords],
			Length[equivalenceclasses],
			Length[Flatten[rootwordclasses]],
			Length[rootwordclasses]
		},
		Tally[Length /@ equivalenceclasses],
		Tally[Length /@ rootwordclasses]
	}
]
SyntaxInformation[CountWords] = {"ArgumentsPattern" -> {_}}

CountAndClassifyWords[n_Integer?NonNegative] :=
Module[{originalwords, rcpwords, equivalenceclasses, rootwordclasses},
	originalwords = RCPCandidates[n];
	rcpwords = Union[RCPRepresentative /@ Select[originalwords, MinimalWordQ]];
	equivalenceclasses = ClassifyWords[rcpwords];
	rootwordclasses = Select[equivalenceclasses, RootWordQ[First[#]] &];
	{
		{
			Length[originalwords],
			Length[rcpwords],
			Length[equivalenceclasses],
			Length[Flatten[rootwordclasses]],
			Length[rootwordclasses]
		},
		Tally[Length /@ equivalenceclasses],
		Tally[Length /@ rootwordclasses],
		equivalenceclasses,
		rootwordclasses
	}
]
SyntaxInformation[CountAndClassifyWords] = {"ArgumentsPattern" -> {_}}

EquivalenceClass[word_] :=
SortWords[Select[Union[RCPRepresentative /@ EquivalentWords[word]], MinimalWordQ]]
SyntaxInformation[EquivalenceClass] = {"ArgumentsPattern" -> {_}}

EquivalentWordsQ[word1_String, word2_String] := EquivalenceClass[word1] == EquivalenceClass[word2]
SyntaxInformation[EquivalentWordsQ] = {"ArgumentsPattern" -> {_, _}}

Children[word_String] := Children[{word}]
Children[words_List] :=
Union @@ Function[
	word,
	RCPRepresentative["a" <>
		CanonicalPermutation[StringRotateRight[word, #]]
	] & /@ Accumulate[Reverse[RunLengths[word]]]
] /@ words
SyntaxInformation[Children] = {"ArgumentsPattern" -> {_}}

$AllAutomorphisms =
{{{"a"}, "b"}, {{"a"}, "B"}, {{"b"}, "a"}, {{"b"}, "A"},
 {{"A"}, "b"}, {{"A"}, "B"}, {{"B"}, "a"}, {{"B"}, "A"}}

$Automorphisms =
{{{"a"}, "b"}, {{"a"}, "B"}, {{"b"}, "a"}, {{"b"}, "A"}}


End[]

Protect["EquivalentWords`*"]

EndPackage[]
