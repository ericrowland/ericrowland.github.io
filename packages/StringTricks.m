(* :Title: String Tricks *)

(* :Context: StringTricks` *)

(* :Author: Eric Rowland *)

(* :Date: {2015, 3, 28} *)

(* :Package Version: 1.29 *)

(* :Mathematica Version: 10.1 *)

(* :Discussion:
	StringTricks is a collection of string manipulation and analysis tools.
	Documentation can be found at  http://people.hofstra.edu/Eric_Rowland/packages.html .
*)


BeginPackage["StringTricks`"]

StringTricks`Private`$SymbolList = {
	MatchPairs,
	RunLengths,
	StringAgreementLength,
	StringExponent,
	StringPartitionAt,
	StringPeriodLength,
	StringPower,
	StringPowerQ,
	StringReplaceRepeated,
	StringTuples
}


Unprotect["StringTricks`*"]

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


MatchPairs::usage =
box[MatchPairs["string", {"openpattern", "closepattern"}]] <> " gives the positions of each matching pair of matchfix operators in " <> box["string"] <> ".\n" <>
box[MatchPairs["string", "delimeter"]] <> " uses " <> box["delimeter"] <> " for the opening and closing patterns."

RunLengths::usage =
box[RunLengths["string"]] <> " lists the lengths of runs of consecutive letters in " <> box["string"] <> "."

StringAgreementLength::usage =
box[StringAgreementLength[SubscriptSequence["string", {1, 2, "..."}]]] <> " gives the number of beginning entries for which several strings agree."

StringExponent::usage =
box[StringExponent["string"]] <> " gives the maximal exponent " <> box["a"] <> "/" <> box["b"] <> " such that " <> box["string"] <> " is an " <> box["a"] <> "/" <> box["b"] <> "\[Hyphen]power."

StringPartitionAt::usage =
box[StringPartitionAt["string", SubscriptList["n", {1, 2, "..."}]]] <> " partitions " <> box["string"] <> " by placing breaks after positions " <> box[SubscriptSequence["n", {1, 2, "..."}]] <> ".\n" <>
box[StringPartitionAt["string", "n"]] <> " places a break after position " <> box["n"] <> "."

StringPeriodLength::usage =
box[StringPeriodLength["string"]] <> " gives the period length of " <> box["string"] <> "."

StringPower::usage =
box[StringPower["string", "n"]] <> " generates a string of " <> box["n"] <> " copies of " <> box["string"] <> ".\n" <>
box[StringPower["string", "a" / "b"]] <> " generates a fractional power of a string whose length is divisible by " <> box["b"] <> "."

StringPowerQ::usage =
box[StringPowerQ["string"]] <> " yields True if " <> box["string"] <> " is a proper integral power of another string, and False otherwise.\n" <>
box[StringPowerQ["string", "a" / "b"]] <> " yields True if " <> box["string"] <> " is an " <> box["a"] <> "/" <> box["b"] <> "\[Hyphen]power of another string, and False otherwise."

StringReplaceRepeated::usage =
box[StringReplaceRepeated["string", "rules"]] <> " repeatedly performs replacements on " <> box["string"] <> " until the result no longer changes.\n" <>
box[StringReplaceRepeated["string", "rules", "n"]] <> " stops after at most " <> box["n"] <> " steps.\n" <>
box[StringReplaceRepeated["string", "rules", "n", "l"]] <> " truncates at length " <> box["l"] <> " at each step."

StringTuples::usage =
box[StringTuples[SubscriptList["s", {1, 2, "...", "k"}], "n"]] <> " generates a list of all possible words of length " <> box["n"] <> " on a given alphabet.\n" <>
box[StringTuples[SubscriptList["s", {1, 2, "...", "k"}], SubscriptList["n", {"min", "max"}]]] <> " gives all words containing between " <> box[Subscript["n", "min"]] <> " and " <> box[Subscript["n", "max"]] <> " elements."


(* currently allows a matched pair to have nonempty overlap *)
MatchPairs[string_String, delimeter : Except[_List]] := MatchPairs[string, {delimeter, delimeter}]
MatchPairs[string_String, {openpattern_, closepattern_}] :=
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
SyntaxInformation[MatchPairs] = {"ArgumentsPattern" -> {_, _}}

RunLengths[word_String] := Length /@ Split[Characters[word]]
SyntaxInformation[RunLengths] = {"ArgumentsPattern" -> {_}}

StringAgreementLength[strings__String] :=
LengthWhile[
	Transpose[PadRight[
		Characters /@ {strings},
		{Length[{strings}], Max[StringLength /@ {strings}]},
		Unique[]
	]],
	SameQ @@ # &
]
SyntaxInformation[StringAgreementLength] = {"ArgumentsPattern" -> {__}}

StringExponent[string_String /; string != ""] :=
	StringLength[string] / StringPeriodLength[string]
SyntaxInformation[StringExponent] = {"ArgumentsPattern" -> {_}}

StringPartitionAt[string_String, {}] :=
	{string}
StringPartitionAt[string_String, positions : {__Integer}] /;
	Max[Abs[positions]] <= StringLength[string] :=
StringTake[string, # + {1, 0}] & /@
	Partition[
		Sort[Join[
			{0, StringLength[string]},
			positions /. n_Integer?Negative :> StringLength[string] + n
		]],
		2,
		1
	]
StringPartitionAt[string_String, n_Integer] :=
	StringPartitionAt[string, {n}]
SyntaxInformation[StringPartitionAt] = {"ArgumentsPattern" -> {_, _}}

StringPeriodLength[""] = 0
StringPeriodLength[string_String] :=
Module[{length = 1},
	While[StringDrop[string, length] =!= StringDrop[string, -length],
		length++
	];
	length
]
SyntaxInformation[StringPeriodLength] = {"ArgumentsPattern" -> {_}}

SetAttributes[StringPower, Listable]
StringPower[s_String, n_Integer?NonNegative] :=
	StringJoin[ConstantArray[s, n]]
StringPower[s_String, r_Rational?NonNegative] /; Divisible[StringLength[s], Denominator[r]] :=
	StringJoin[ConstantArray[s, Floor[r]], StringTake[s, StringLength[s] FractionalPart[r]]]
SyntaxInformation[StringPower] = {"ArgumentsPattern" -> {_, _}}

StringPowerQ[""] = True
StringPowerQ[string_String] :=
With[{length = StringLength[string]},
	LengthWhile[
		Most[Divisors[length]],
		string != StringPower[StringTake[string, #], length/#] &
	] != DivisorSigma[0, length] - 1
]
StringPowerQ[string_String, 0] :=
	string == ""
StringPowerQ[string_String, power : _Integer | _Rational /; power > 0] :=
With[{length = StringLength[string]},
	And[
		Divisible[length, Numerator[power]],
		Or[
			length/power > length,
			string == StringPower[StringTake[string, length/power], power]
		]
	]
]
SyntaxInformation[StringPowerQ] = {"ArgumentsPattern" -> {_, _.}}

StringReplaceRepeated[
	s_String,
	rules : _Rule | _RuleDelayed | {(_Rule | _RuleDelayed) ...},
	n : (_Integer?NonNegative | Infinity) : Infinity,
	maxlength : (_Integer?NonNegative | Infinity) : Infinity
] :=
	FixedPoint[(StringTake[#, Min[StringLength[#], maxlength]] &)[StringReplace[#, rules]] &, s, n]
SyntaxInformation[StringReplaceRepeated] = {"ArgumentsPattern" -> {_, _, _., _.}}

StringTuples[list : {___String}, n_Integer?NonNegative] :=
	StringJoin /@ Tuples[list, n]
StringTuples[list : {___String}, {nmin_Integer, nmax_Integer} /; 0 <= nmin <= nmax] :=
	Join @@ Table[StringTuples[list, i], {i, nmin, nmax}]
SyntaxInformation[StringTuples] = {"ArgumentsPattern" -> {_, _}}


End[]

Protect["StringTricks`*"]

EndPackage[]
