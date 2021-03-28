(* :Title: Bijective Rules *)

(* :Context: BijectiveRules` *)

(* :Author: Eric Rowland *)

(* :Date: {2015, 7, 10} *)

(* :Package Version: 1.12 *)

(* :Mathematica Version: 10 *)

(* :Discussion:
	BijectiveRules is a package for studying right bijective and left bijective cellular automaton rules.
	Documentation can be found at  https://ericrowland.github.io/packages.html .
*)


BeginPackage["BijectiveRules`"]

BijectiveRules`Private`$SymbolList = {
	ApplyRightBijectiveRuleInverse,
	ApplyRule,
	BijectiveQ,
	BorderBlockLength,
	ColorCycle,
	ColorCycles,
	ColorEquivalentRules,
	ConvergenceSequence,
	DependenceStrengths,
	LeftBijectiveInverse,
	LeftBijectiveQ,
	LeftBijectiveRules,
	LeftfulPredecessor,
	LeftfulSuccessor,
	LeftOrRightBijectiveRules,
	LeftRightReflection,
	RandomLeftBijectiveRule,
	RandomRightBijectiveRule,
	ReverseRow,
	ReversibleCellularAutomaton,
	RightBijectiveInverse,
	RightBijectiveQ,
	RightBijectiveRules,
	RightfulPredecessor,
	RightfulSuccessor,
	Rule30ConvergenceData,
	RuleTable
}


Unprotect["BijectiveRules`*"]

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


ApplyRightBijectiveRuleInverse::usage =
box[ApplyRightBijectiveRuleInverse[{"n", "k", "r"}, "cells", "rightcell"]] <> " gives " <> box[Append[Rest["cells"], "c"]] <> ", where " <> box["c"] <> " is such that " <> box[Append["cells", "c"]] <> " yields " <> box["rightcell"] <> " under the specified rule."

ApplyRule::usage =
box[ApplyRule[{"n", "k", "r"}, "cells"]] <> " gives the color of the cell yielded by the sequence " <> box["cells"] <> " under the specified rule."

BijectiveQ::usage =
box[BijectiveQ["rule", "p"]] <> " yields True if " <> box["rule"] <> " is bijective in position " <> box["p"] <> ", and False otherwise."

(* \[Iota] *)
BorderBlockLength::usage =
box[BorderBlockLength["list", "backgroundcolor"]] <> " gives the length of the first single\[Hyphen]color block following the initial block of color " <> box["backgroundcolor"] <> " in " <> box["list"] <> ".\n" <>
box[BorderBlockLength["list"]] <> " uses background color 0."

ColorCycle::usage =
box[ColorCycle["rule", "c"]] <> " gives the eventual cycle of tail colors obtained from tail color " <> box["c"] <> " under " <> box["rule"] <> ".
If " <> box["c"] <> " is present in this cycle, " <> box["c"] <> " appears as the first entry in the cycle; otherwise the cycle is given in its sorted rotation."

ColorCycles::usage =
box[ColorCycles["rule"]] <> " lists the possible cycles of tail colors under " <> box["rule"] <> ".
Each cycle is given in its sorted rotation."

ColorEquivalentRules::usage =
box[ColorEquivalentRules[{"n", "k", "r"}]] <> " gives the rule numbers of all " <> box["k"] <> "\[Hyphen]color, radius " <> box["r"] <> " rules that are equivalent to the specified rule under some permutation of colors."

(* a *)
ConvergenceSequence::usage =
box[ConvergenceSequence["rule", "init", "power", "l"]] <> " gives the agreement lengths for rows offset by successive powers of " <> box["l"] <> " in the evolution of the cellular automaton with the specified rule from initial condition " <> box["init"] <> ".\n" <>
box[ConvergenceSequence["rule", "init", "power"]] <> " uses " <> box["l" = LCM[1, 2, "\[Ellipsis]", "k"]] <> "."

DependenceStrengths::usage =
box[DependenceStrengths["rule"]] <> " gives, for each position in the rule, the probability that changing the input in that position changes the output."

LeftBijectiveInverse::usage =
box[LeftBijectiveInverse["rule"]] <> " gives the radius 1/2 rule that computes the inverse of the specified left bijective rule."

LeftBijectiveQ::usage =
box[LeftBijectiveQ["rule"]] <> " yields True if " <> box["rule"] <> " is left bijective, and False otherwise."

LeftBijectiveRules::usage =
box[LeftBijectiveRules["k", "r"]] <> " lists the rule numbers of all left bijective " <> box["k"] <> "\[Hyphen]color, radius " <> box["r"] <> " rules."

LeftfulPredecessor::usage =
box[LeftfulPredecessor["rule", {"row", "tailcolor"}]] <> " gives the predecessor of a row with an infinite leftful history under the specified left bijective rule."

LeftfulSuccessor::usage =
box[LeftfulSuccessor["rule", {"row", "tailcolor"}]] <> " gives the successor of a row under the specified rule."

LeftOrRightBijectiveRules::usage =
box[LeftOrRightBijectiveRules["k", "r"]] <> " lists the rule numbers of all " <> box["k"] <> "\[Hyphen]color, radius " <> box["r"] <> " rules that are either left bijective or right bijective."

LeftRightReflection::usage =
box[LeftRightReflection["rule"]] <> " gives the left\[Dash]right reflection of the specified rule."

RandomLeftBijectiveRule::usage =
box[RandomLeftBijectiveRule["k", "r"]] <> " produces a pseudorandom left bijective " <> box["k"] <> "\[Hyphen]color, radius " <> box["r"] <> " rule."

RandomRightBijectiveRule::usage =
box[RandomRightBijectiveRule["k", "r"]] <> " produces a pseudorandom right bijective " <> box["k"] <> "\[Hyphen]color, radius " <> box["r"] <> " rule."

ReverseRow::usage =
box[ReverseRow["list"]] <> " gives the left\[Dash]right reflection of a row of the form " <> box[{"lefttailcolor", "row"}] <> " or " <> box[{"row", "righttailcolor"}] <> "."

ReversibleCellularAutomaton::usage =
box[ReversibleCellularAutomaton["rule", "init", "t"]] <> " generates a list representing the evolution of the reversible cellular automaton with the specified rule from initial condition " <> box["init"] <> " for " <> box["t"] <> " steps.\n" <>
box[ReversibleCellularAutomaton["rule", "init", {"tspec"}]] <> " gives only those parts of the evolution specified by " <> box["tspec"] <> "."

RightBijectiveInverse::usage =
box[RightBijectiveInverse["rule"]] <> " gives the radius 1/2 rule that computes the inverse of the specified right bijective rule."

RightBijectiveQ::usage =
box[RightBijectiveQ["rule"]] <> " yields True if " <> box["rule"] <> " is right bijective, and False otherwise."

RightBijectiveRules::usage =
box[RightBijectiveRules["k", "r"]] <> " lists the rule numbers of all right bijective " <> box["k"] <> "\[Hyphen]color, radius " <> box["r"] <> " rules."

RightfulPredecessor::usage =
box[RightfulPredecessor["rule", {"tailcolor", "row"}]] <> " gives the predecessor of a row with an infinite rightful history under the specified right bijective rule."

RightfulSuccessor::usage =
box[RightfulSuccessor["rule", {"tailcolor", "row"}]] <> " gives the successor of a row under the specified rule."

Rule30ConvergenceData::usage =
box[Rule30ConvergenceData["n"]] <> " gives the number of rightmost consecutive black cells on row " <> box[2^"n" - 1] <> " of rule 30 begun from a single black cell."

RuleTable::usage =
box[RuleTable["rule"]] <> " gives the local rules specified by rule."


(* \[Lambda] *)
AgreementLength[list1_List, list2_List] :=
Module[{p},
	LengthWhile[Transpose[PadRight[{list1, list2}, Automatic, p]], SameQ @@ # &]
]

FirstSortedElement[list : _[__]] :=
	list[[First[Ordering[list, 1]]]]

FirstSortedRotation[list_] :=
	FirstSortedElement[NestList[RotateLeft, list, Length[list] - 1]]

FixedPointPeriod[f_, expr_] :=
Module[{list = {expr}, val = expr, i = 0},
	While[!MemberQ[list, val = f[val], {1}],
		AppendTo[list, val];
		i++
	];
	Take[list, {Position[list, val, {1}, 1][[1,1]], -1}]
]

Shear[array_List, n_Integer : 1] := MapIndexed[RotateRight[#1, (#2[[1]] - 1) n] &, array, {1}]

ToArray[array_List, padding_] /; VectorQ[array[[1,1]]] :=
	Join[#[[1]], ConstantArray[#[[2]], padding]] & /@ array
ToArray[array_List, padding_] /; VectorQ[array[[1,2]]] :=
	Join[ConstantArray[#[[1]], padding], #[[2]]] & /@ array

ToRule[n_Integer?NonNegative /; n < 256] := {n, 2, 1}
ToRule[{n_Integer?NonNegative, k : (_Integer?Positive) : 2, r : (_?NonNegative) : 1} /; IntegerQ[2 r] && n < k^k^(2 r + 1)] := {n, k, r}

UnpadLeft[list_, p_] :=
Drop[list, Replace[
	Position[list, _?(! MatchQ[#, p]&), {1}, 1, Heads -> False],
	{{{position_}} :> position, _ -> All + 1}
] - 1]

ValidRuleQ[rule_] := MatchQ[ToRule[rule], {_, _, _}]


SetAttributes[Rule30ConvergenceData, Listable]
Rule30ConvergenceData[n_Integer /; 0 <= n <= 42] :=
{1, 3, 4, 6, 7, 9, 15, 16, 24, 25, 27, 29, 34, 36, 37, 39, 41, 43, 48, 49, 51,
	54, 55, 58, 60, 63, 64, 66, 69, 70, 72, 74, 77, 79, 80, 82, 84, 86, 90, 91,
	93, 100, 103}[[n + 1]]
Rule30ConvergenceData[n_Integer /; n > 42] := Missing["Unknown"]
SyntaxInformation[Rule30ConvergenceData] = {"ArgumentsPattern" -> {_}}


ApplyRightBijectiveRuleInverse[{n_, k_, r_}, cells_List, rcell_] :=
	ApplyRightBijectiveRuleInverse[{n, k, r}, cells, rcell] =
		Append[
			Rest[cells],
			First[Select[Range[0, k - 1], IntegerDigits[n, k, k^(2 r + 1)][[k^(2 r + 1) - FromDigits[Append[cells, #], k]]] == rcell &, 1]]
		]
SyntaxInformation[ApplyRightBijectiveRuleInverse] = {"ArgumentsPattern" -> {_, _, _}}

ApplyRule[{n_, k_, r_}, cells_List] :=
	IntegerDigits[n, k, k^(2 r + 1)][[k^(2 r + 1) - FromDigits[cells, k]]]
SyntaxInformation[ApplyRule] = {"ArgumentsPattern" -> {_, _}}

BijectiveQ[rule_?ValidRuleQ, position_Integer] :=
Module[{n, k, r},
	{n, k, r} = ToRule[rule];
	Length[Union[ReplacePart[#1, position -> #2] & @@@ RuleTable[rule]]] == k^(2 r + 1)
]
LeftBijectiveQ[rule_] := BijectiveQ[rule, 1]
RightBijectiveQ[rule_] := BijectiveQ[rule, -1]
SyntaxInformation[BijectiveQ] = {"ArgumentsPattern" -> {_, _}}
SyntaxInformation[LeftBijectiveQ] = {"ArgumentsPattern" -> {_}}
SyntaxInformation[RightBijectiveQ] = {"ArgumentsPattern" -> {_}}

BorderBlockLength[row_List, bgcolor_ : 0] :=
With[{unpaddedrow = UnpadLeft[row, bgcolor]},
	AgreementLength[unpaddedrow, ConstantArray[First[unpaddedrow], Length[unpaddedrow]]]
]
SyntaxInformation[BorderBlockLength] = {"ArgumentsPattern" -> {_, _.}}

ColorCycle[rule_?ValidRuleQ, c_] :=
Module[{n, k, r, graph},
	{n, k, r} = ToRule[rule];
	graph = IntegerDigits[n, k, k^(2 r + 1)][[k^(2 r + 1) - ((k^(2 r + 1) - 1) Range[0, k - 1])/(k - 1)]];
	(If[MemberQ[#, c], #, FirstSortedRotation[#]] &)[FixedPointPeriod[graph[[# + 1]] &, c]]
]
SyntaxInformation[ColorCycle] = {"ArgumentsPattern" -> {_, _}}

ColorCycles[rule_?ValidRuleQ] :=
Module[{n, k, r, graph},
	{n, k, r} = ToRule[rule];
	graph = IntegerDigits[n, k, k^(2 r + 1)][[k^(2 r + 1) - ((k^(2 r + 1) - 1) Range[0, k - 1])/(k - 1)]];
	Union[Table[FirstSortedRotation[FixedPointPeriod[graph[[# + 1]] &, i]], {i, 0, k - 1}]]
]
SyntaxInformation[ColorCycles] = {"ArgumentsPattern" -> {_}}

ColorEquivalentRules[rule_?ValidRuleQ] :=
Module[{n, k, r, ruletable},
	{n, k, r} = ToRule[rule];
	ruletable = RuleTable[rule];
	Union[Function[
		perm,
		FromDigits[Last /@ Reverse[Sort[ruletable /. Thread[Range[0, k - 1] -> perm]]], k]
	] /@ Permutations[Range[0, k - 1]]]
]
SyntaxInformation[ColorEquivalentRules] = {"ArgumentsPattern" -> {_}}

ConvergenceSequence[rule_?ValidRuleQ, init : {_, _}, power_Integer?NonNegative, l_Integer?NonNegative] :=
Module[{padding = 1, row},
	row = ReversibleCellularAutomaton[rule, init, {{{0}}}, Padding -> padding];
	AgreementLength[row, #] - padding & /@
		FoldList[
			ReversibleCellularAutomaton[rule, {First[#1], Drop[#1, padding]}, {{{#2}}}, Padding -> padding] &,
			ReversibleCellularAutomaton[rule, init, {{{1}}}, Padding -> padding],
			l^(Range[power] - 1) (l - 1)
		]
]
ConvergenceSequence[rule_?ValidRuleQ, init_List, power_Integer?NonNegative] :=
	ConvergenceSequence[rule, init, power, LCM @@ Range[ToRule[rule][[2]]]]
SyntaxInformation[ConvergenceSequence] = {"ArgumentsPattern" -> {_, _, _, _.}}

DependenceStrengths[rule_?ValidRuleQ] :=
Module[{n, k, r, ruletable},
	{n, k, r} = ToRule[rule];
	ruletable = RuleTable[rule];
	Function[
		position,
		Mean[(1 - Total[Binomial[Last /@ Tally[Last /@ #], 2]]/Binomial[k, 2] &) /@ GatherBy[ruletable, Delete[First[#], position] &]]
	] /@ Range[2 r + 1]
]
SyntaxInformation[DependenceStrengths] = {"ArgumentsPattern" -> {_}}

LeftBijectiveInverse[rule_?ValidRuleQ] /; LeftBijectiveQ[rule] :=
	LeftRightReflection[RightBijectiveInverse[LeftRightReflection[rule]]]
RightBijectiveInverse[rule_?ValidRuleQ] /; RightBijectiveQ[rule] := RightBijectiveInverse[rule] =
Module[{n, k, r},
	{n, k, r} = ToRule[rule];
	{FromDigits[
		FromDigits[#, k] & /@ Flatten[Table[
			Last /@ Rest[FoldList[
				ApplyRightBijectiveRuleInverse[{n, k, r}, ##] &,
				IntegerDigits[b1, k, 2 r],
				IntegerDigits[b2, k, 2 r]
			]],
			{b1, k^(2 r) - 1, 0, -1},
			{b2, k^(2 r) - 1, 0, -1}
		], 1],
		k^(2 r)
	], k^(2 r), 1/2}
]
SyntaxInformation[LeftBijectiveInverse] = {"ArgumentsPattern" -> {_}}
SyntaxInformation[RightBijectiveInverse] = {"ArgumentsPattern" -> {_}}

LeftBijectiveRules[k_, r_] /; ValidRuleQ[{0, k, r}] :=
	Sort[
		First[LeftRightReflection[{#, k, r}]] & /@ RightBijectiveRules[k, r]
	]
RightBijectiveRules[k_, r_] /; ValidRuleQ[{0, k, r}] :=
	FromDigits[Join @@ #, k] & /@
		Tuples[Permutations[Range[0, k - 1]], k^(2 r)]
LeftOrRightBijectiveRules[k_, r_] /; ValidRuleQ[{0, k, r}] :=
	Union[Flatten[
		{#, First[LeftRightReflection[{#, k, r}]]} & /@ RightBijectiveRules[k, r]
	]]
SyntaxInformation[LeftBijectiveRules] = {"ArgumentsPattern" -> {_, _}}
SyntaxInformation[RightBijectiveRules] = {"ArgumentsPattern" -> {_, _}}
SyntaxInformation[LeftOrRightBijectiveRules] = {"ArgumentsPattern" -> {_, _}}

LeftfulPredecessor[rule_?ValidRuleQ, {row_List, tail_Integer}] /;
		LeftBijectiveQ[rule] && MemberQ[ColorCycle[rule, tail], tail] :=
	ReverseRow[RightfulPredecessor[LeftRightReflection[rule], ReverseRow[{row, tail}]]]
(* "Last /@" here makes it inefficient for long lists; I should just Sow each cell *)
RightfulPredecessor[rule_?ValidRuleQ, {tail_Integer, row_List}] /;
		RightBijectiveQ[rule] && MemberQ[ColorCycle[rule, tail], tail] :=
Module[{n, k, r, newtail},
	{n, k, r} = ToRule[rule];
	newtail = Last[ColorCycle[rule, tail]];
	{newtail, Last /@ Rest[FoldList[
		ApplyRightBijectiveRuleInverse[{n, k, r}, ##] &,
		ConstantArray[newtail, 2 r],
		row
	]]}
]
SyntaxInformation[LeftfulPredecessor] = {"ArgumentsPattern" -> {_, _}}
SyntaxInformation[RightfulPredecessor] = {"ArgumentsPattern" -> {_, _}}

LeftfulSuccessor[rule_?ValidRuleQ, {row_List, tail_Integer}] :=
	ReverseRow[RightfulSuccessor[LeftRightReflection[rule], ReverseRow[{row, tail}]]]
RightfulSuccessor[rule_?ValidRuleQ, {tail_Integer, row_List}] :=
Module[{n, k, r},
	{n, k, r} = ToRule[rule];
	{
		ApplyRule[{n, k, r}, ConstantArray[tail, 2 r + 1]],
		ApplyRule[{n, k, r}, #] & /@ Partition[Join[ConstantArray[tail, 2 r], row], 2 r + 1, 1]
	}
]
SyntaxInformation[LeftfulSuccessor] = {"ArgumentsPattern" -> {_, _}}
SyntaxInformation[RightfulSuccessor] = {"ArgumentsPattern" -> {_, _}}

LeftRightReflection[rule_?ValidRuleQ] :=
Module[{n, k, r},
	{n, k, r} = ToRule[rule];
	{FromDigits[Reverse[Last /@ Sort[{Reverse[#1], #2} & @@@ RuleTable[rule]]], k], k, r}
]
SyntaxInformation[LeftRightReflection] = {"ArgumentsPattern" -> {_}}

RandomLeftBijectiveRule[k_, r_] := LeftRightReflection[RandomRightBijectiveRule[k, r]]
RandomRightBijectiveRule[k_, r_] /; ValidRuleQ[{0, k, r}] :=
	{FromDigits[Join @@ Table[RandomSample[Range[0, k - 1]], {k^(2 r)}], k], k, r}
SyntaxInformation[RandomLeftBijectiveRule] = {"ArgumentsPattern" -> {_, _}}
SyntaxInformation[RandomRightBijectiveRule] = {"ArgumentsPattern" -> {_, _}}

ReverseRow[{row_List, tail_Integer}] := {tail, Reverse[row]}
ReverseRow[{tail_Integer, row_List}] := {Reverse[row], tail}
SyntaxInformation[ReverseRow] = {"ArgumentsPattern" -> {_}}

evolveForward[{n_, k_, r_}, init : {row_List, _Integer}, tspec_] :=
	{Most[#], Last[#]} & /@
		CellularAutomaton[
			{n, k, List /@ Range[0, 2 r]},
			init,
			{tspec, {0, Length[row]}}
		]
evolveForward[{n_, k_, r_}, init : {_Integer, row_List}, tspec_] :=
	{First[#], Rest[#]} & /@
		CellularAutomaton[
			{n, k, List /@ Range[-2 r, 0]},
			Reverse[init],
			{tspec, {-1, Length[row] - 1}}
		]
evolveBackward[rule_?LeftBijectiveQ, init : {_List, _Integer}, tspec_] :=
	ReverseRow /@ evolveBackward[LeftRightReflection[rule], ReverseRow[init], tspec]
evolveBackward[rule : {n_, k_, r_}?RightBijectiveQ, init : {bg_Integer, row_List}, {t1_?Negative, t2_?NonPositive, dt_}] /;
		MemberQ[ColorCycle[rule, bg], bg] || Message[ReversibleCellularAutomaton::background, bg, rule] :=
With[{inversewidth = Ceiling[(Length[row] + 1)/(2 r)]},
	{First[#], Take[#, -Length[row]]} & /@ Flatten /@
		IntegerDigits[Take[Transpose[Shear[Transpose[Reverse[CellularAutomaton[
			Append[Most[RightBijectiveInverse[rule]], {{-1}, {0}}],
			{
				First[(Transpose[Shear[Transpose[((FromDigits[#, k] &) /@ Partition[#, 2 r] &) /@ #], -1]] &)[
					CellularAutomaton[
						{n, k, List /@ Range[-2 r, 0]},
						Reverse[init],
						{inversewidth - 1, {Length[row] - 2 r inversewidth, Length[row] - 1}}
					]
				]],
				((FromDigits[#, k] &) /@ Partition[Flatten[Table[#, {LCM[Length[#], 2 r]/Length[#]}]], 2 r] &)[
					Flatten[ConstantArray[#, 2 r] & /@ ColorCycle[rule, bg]]
				]
			},
			{inversewidth - 1 - t1, {0, inversewidth - 1}}
		]]]]], {t1 - 1, t2 - 1, dt}], k, 2 r]
]
(* all steps 0 through t *)
ReversibleCellularAutomaton[rule_?ValidRuleQ, init : {_List, _Integer} | {_Integer, _List}, t_Integer?Negative | {t_Integer?Negative}, OptionsPattern[]] :=
With[{history = evolveBackward[ToRule[rule], init, {t, 0, 1}]},
	ToArray[history, OptionValue[Padding]] /;
		!MatchQ[history, _evolveBackward]
]
ReversibleCellularAutomaton[rule_?ValidRuleQ, init : {_List, _Integer} | {_Integer, _List}, t_Integer?NonNegative | {t_Integer?NonNegative}, OptionsPattern[]] :=
	ToArray[evolveForward[ToRule[rule], init, t], OptionValue[Padding]]
(* a list containing only step t *)
ReversibleCellularAutomaton[rule_?ValidRuleQ, init : {_List, _Integer} | {_Integer, _List}, {{t_Integer?NonPositive}}, OptionsPattern[]] :=
With[{history = evolveBackward[ToRule[rule], init, {t, 0, -t}]},
	ToArray[history, OptionValue[Padding]] /;
		!MatchQ[history, _evolveBackward]
]
ReversibleCellularAutomaton[rule_?ValidRuleQ, init : {_List, _Integer} | {_Integer, _List}, {{t_Integer?Positive}}, OptionsPattern[]] :=
	ToArray[Rest[evolveForward[ToRule[rule], init, {0, t, t}]], OptionValue[Padding]]
(* step t alone *)
ReversibleCellularAutomaton[rule_?ValidRuleQ, init : {_List, _Integer} | {_Integer, _List}, {{{t_Integer?Negative}}}, OptionsPattern[]] :=
With[{history = evolveBackward[ToRule[rule], init, {t, 0, -t}]},
	First[ToArray[history, OptionValue[Padding]]] /;
		!MatchQ[history, _evolveBackward]
]
ReversibleCellularAutomaton[rule_?ValidRuleQ, init : {_List, _Integer} | {_Integer, _List}, {{{0}}}, OptionsPattern[]] :=
	First[ToArray[{init}, OptionValue[Padding]]]
ReversibleCellularAutomaton[rule_?ValidRuleQ, init : {_List, _Integer} | {_Integer, _List}, {{{t_Integer?Positive}}}, OptionsPattern[]] :=
	Last[ToArray[evolveForward[ToRule[rule], init, {0, t, t}], OptionValue[Padding]]]
(* steps t1, t1 + dt, ... *)
ReversibleCellularAutomaton[rule_?ValidRuleQ, init : {_List, _Integer} | {_Integer, _List}, {{t1_Integer?Negative, t2_Integer?NonPositive, dt : (_Integer?Positive) : 1}} /; t1 <= t2, OptionsPattern[]] :=
With[{history = evolveBackward[ToRule[rule], init, {t1, t2, dt}]},
	ToArray[history, OptionValue[Padding]] /;
		!MatchQ[history, _evolveBackward]
]
ReversibleCellularAutomaton[rule_?ValidRuleQ, init : {_List, _Integer} | {_Integer, _List}, {{t1_Integer?Negative, t2_Integer?Positive, dt : (_Integer?Positive) : 1}} /; t1 <= t2, OptionsPattern[]] :=
With[{history = evolveBackward[ToRule[rule], init, {t1, -1, dt}]},
	ToArray[
		Join[
			history,
			If[Mod[t1, dt] <= t2,
				evolveForward[ToRule[rule], init, {Mod[t1, dt], t2, dt}],
				{}
			]
		],
		OptionValue[Padding]
	] /;
		!MatchQ[history, _evolveBackward]
]
ReversibleCellularAutomaton[rule_?ValidRuleQ, init : {_List, _Integer} | {_Integer, _List}, {{t1_Integer?NonNegative, t2_Integer?Positive, dt : (_Integer?Positive) : 1}} /; t1 <= t2, OptionsPattern[]] :=
	ToArray[evolveForward[ToRule[rule], init, {t1, t2, dt}], OptionValue[Padding]]
Options[ReversibleCellularAutomaton] = {Padding -> 0}
SyntaxInformation[ReversibleCellularAutomaton] = {"ArgumentsPattern" -> {_, _, _, OptionsPattern[]}}
ReversibleCellularAutomaton::background = "Background color `1` does not appear in a cycle for rule `2`."

RuleTable[rule_?ValidRuleQ] :=
Module[{n, k, r},
	{n, k, r} = ToRule[rule];
	Thread[Tuples[Range[0, k - 1], 2 r + 1] -> Reverse[IntegerDigits[n, k, k^(2 r + 1)]]]
]
SyntaxInformation[RuleTable] = {"ArgumentsPattern" -> {_}}


End[]

Protect["BijectiveRules`*"]
Unprotect[ApplyRightBijectiveRuleInverse, RightBijectiveInverse]

EndPackage[]
