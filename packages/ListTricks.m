(* :Title: List Tricks *)

(* :Context: ListTricks` *)

(* :Author: Eric Rowland *)

(* :Date: {2019, 7, 22} *)

(* :Package Version: 2.52 *)

(* :Mathematica Version: 12 *)

(* :Discussion:
	ListTricks is a collection of about 50 structure manipulation, classification, and searching tools
	that can be thought of as extending the core Wolfram Language.
	Documentation can be found at  http://people.hofstra.edu/Eric_Rowland/packages.html .
*)


BeginPackage["ListTricks`"]

ListTricks`Private`$SymbolList = {
	Accrete,
	AgreementLength,
	ArrayMap,
(* no longer exposed
	ClassifyBy,
*)
	ColumnMap,
	ColumnWrap,
	Complements,
	Counterexamples,
	Distinct,
	DropAfter,
	DropBefore,
	Examples,
	FirstSortedElement,
	FirstSortedRotation,
	FixedPointPeriod,
	IndentedExport,
	InExpression,
	IntegerCompositions,
	MapAcross,
	MapList,
	MatchLength,
	MulticolumnArrayPlot,
	MultiRiffle,
	MultirowArrayPlot,
	MultisetComplement,
	Multisets,
	NextTuple,
	Occurrence,
	Only,
	Orbit,
	OrbitRepresentatives,
	ParallelSelect,
	PartitionAfter,
	PartitionAt,
	PartitionBefore,
	Period,
	PeriodLength,
	Portion,
	RaggedArrayDepth,
	RationalRange,
	ReverseAll,
	RotateClockwise,
	RotateCounterClockwise,
	RotateLeftTo,
	RotateRightTo,
	Second,
	Shear,
	Sift,
	SuccessiveMaxima,
	SuccessiveMinima,
	Swap,
	TakeAfter,
	TakeBefore,
	Tile,
	Trim,
	Unpad,
	UnpadLeft,
	UnpadRight,
	Unriffle,
	$UserCloudDirectory
}


Unprotect["ListTricks`*"]

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


Accrete::usage =
box[Accrete["list"]] <> " gives a list of the successive accumulated totals of elements in " <> box["list"] <> ".\n" <>
box[Accrete[SubscriptList["e", {1, 2, 3, "..."}], "f"]] <> " gives " <> box[{"f"[Subscript["e", 1]], "f"[SubscriptSequence["e", {1, 2}]], "f"[SubscriptSequence["e", {1, 2, 3}]], "\[Ellipsis]"}] <> "."

AgreementLength::usage =
box[AgreementLength[SubscriptSequence["list", {1, 2, "..."}]]] <> " gives the number of beginning entries for which several lists agree."

ArrayMap::usage =
box[ArrayMap["f", "array", {"level"}]] <> " applies " <> box["f"] <> " to the subarrays of " <> box["array"] <> " specified by " <> box["level"] <> ".\n" <>
box[ArrayMap["f", "array", {"level"}, "d"]] <> " applies " <> box["f"] <> " along direction " <> box["d"] <> "."

ClassifyBy::usage =
box[ClassifyBy["list"]] <> " partitions the elements of " <> box["list"] <> " into labeled equivalence classes " <> box[{{SubscriptList["e", {11, 12, "..."}], Subscript["p", 1]}, {SubscriptList["e", {21, 22, "..."}], Subscript["p", 2]}, "\[Ellipsis]"}] <> ".\n" <>
box[ClassifyBy["list", "f"]] <> " classifies elements by their values under " <> box["f"] <> ".\n" <>
box[ClassifyBy["list", "f", "g"]] <> " applies " <> box["g"] <> " to each element after it is classified.\n" <>
box[ClassifyBy["list", "f", "g", "h"]] <> " applies " <> box["h"] <> " to class."

ColumnMap::usage =
box[ColumnMap["f", "array"]] <> " maps " <> box["f"] <> " onto each column of a two\[Hyphen]dimensional ragged array, giving as the second argument the row index of the first element in the column.\n" <>
box[ColumnMap["f", "array", "offset"]] <> " indexes rows starting with " <> box["offset"] <> " rather than 1."

ColumnWrap::usage =
box[ColumnWrap["list", "n"]] <> " wraps a list into at most " <> box["n"] <> " columns.\n" <>
box[ColumnWrap["array", "n"]] <> " wraps a two\[Hyphen]dimensional array into at most " <> box["n"] <> " super\[Hyphen]columns.\n" <>
box[ColumnWrap["array", "n", "spacing"]] <> " leaves a space of size " <> box["spacing"] <> " between successive super\[Hyphen]columns."

Complements::usage =
box[Complements[Subscript["list", 1], Subscript["list", 2]]] <> " gives the list " <> box[{Complement[Subscript["list", 1], Subscript["list", 2]], Complement[Subscript["list", 2], Subscript["list", 1]]}] <> ".\n" <>
box[Complements[SubscriptSequence["list", {1, 2, 3, "..."}]]] <> " gives " <> box[{Complement[Subscript["list", 1], Subscript["list", 2], Subscript["list", 3], "\[Ellipsis]"], Complement[Subscript["list", 2], Subscript["list", 1], Subscript["list", 3], "\[Ellipsis]"], Complement[Subscript["list", 3], Subscript["list", 1], Subscript["list", 2], "\[Ellipsis]"], "\[Ellipsis]"}] <> "."

Counterexamples::usage =
box[Counterexamples["expr", SubscriptList["i", {Null, "min", "max"}], SubscriptList["j", {Null, "min", "max"}], "\[Ellipsis]"]] <> " gives the list of values of " <> box[{"i", "j", "\[Ellipsis]"}] <> " for which " <> box["expr"] <> " does not evaluate to True.\n" <>
box[Counterexamples["expr", SubscriptList["i", {Null, "min", "max"}], SubscriptList["j", {Null, "min", "max"}], "\[Ellipsis]", "n"]] <> " finds at most " <> box["n"] <> " counterexamples."

Distinct::usage =
"Distinct is an option for Sift that specifies whether to check for duplicates."

DropAfter::usage =
box[DropAfter["list", "pattern"]] <> " drops the elements of " <> box["list"] <> " appearing after the first element matching " <> box["pattern"] <> ".\n" <>
box[DropAfter["list", "pattern", "n"]] <> " drops the elements of " <> box["list"] <> " appearing after the " <> box["n"] <> "th element matching " <> box["pattern"] <> ". Negative " <> box["n"] <> " counts from the end of the list."

DropBefore::usage =
box[DropBefore["list", "pattern"]] <> " drops the elements of " <> box["list"] <> " appearing before the first element matching " <> box["pattern"] <> ".\n" <>
box[DropBefore["list", "pattern", "n"]] <> " drops the elements of " <> box["list"] <> " appearing before the " <> box["n"] <> "th element matching " <> box["pattern"] <> ". Negative " <> box["n"] <> " counts from the end of the list."

Examples::usage =
box[Examples["expr", SubscriptList["i", {Null, "min", "max"}], SubscriptList["j", {Null, "min", "max"}], "\[Ellipsis]"]] <> " gives the list of values of " <> box[{"i", "j", "\[Ellipsis]"}] <> " for which " <> box["expr"] <> " evaluates to True.\n" <>
box[Examples["expr", SubscriptList["i", {Null, "min", "max"}], SubscriptList["j", {Null, "min", "max"}], "\[Ellipsis]", "n"]] <> " finds at most " <> box["n"] <> " examples."

FirstSortedElement::usage =
box[FirstSortedElement["expr"]] <> " gives the first element in " <> box[Sort["expr"]] <> ".\n" <>
box[FirstSortedElement["expr", "p"]] <> " sorts using the ordering function " <> box["p"] <> "."

FirstSortedRotation::usage =
box[FirstSortedRotation["list"]] <> " gives the rotation of " <> box["list"] <> " that appears first in canonical order.\n" <>
box[FirstSortedRotation["list", "p"]] <> " uses the ordering function " <> box["p"] <> "."

FixedPointPeriod::usage =
box[FixedPointPeriod["f", "expr"]] <> " gives the eventual period obtained by applying " <> box["f"] <> " repeatedly to " <> box["expr"] <> ".\n" <>
box[FixedPointPeriod["f", "expr", "n"]] <> " stops after at most " <> box["n"] <> " steps."

IndentedExport::usage =
box[IndentedExport[String["file.ext"], "expr"]] <> " exports data to a text file, with indentation reflecting list structure."

InExpression::usage =
box[InExpression["n"]] <> " gives the expression submitted as the " <> box["n"] <> "th input line, wrapped in HoldComplete."

IntegerCompositions::usage =
box[IntegerCompositions["n"]] <> " gives a list of all ways to partition " <> box["n"] <> " into an ordered sum of positive integers.\n" <>
box[IntegerCompositions["n", "k"]] <> " gives compositions into at most " <> box["k"] <> " integers.\n" <>
box[IntegerCompositions["n", {"k"}]] <> " gives compositions into exactly " <> box["k"] <> " integers."

MapAcross::usage =
box[MapAcross[SubscriptList["f", {1, 2, "..."}], SubscriptList["x", {1, 2, "..."}]]] <> " gives " <> box[{Subscript["f", 1][Subscript["x", 1]], Subscript["f", 2][Subscript["x", 2]], "\[Ellipsis]"}] <> "."

MapList::usage =
box[MapList["f", "list"]] <> " applies " <> box["f"] <> " to each element of " <> box["list"] <> " independently, returning a list of lists which differ from " <> box["list"] <> " in only one position each."

MatchLength::usage =
box[MatchLength["list", "pattern"]] <> " gives the number of consecutive elements at the beginning of " <> box["list"] <> " that match " <> box["pattern"] <> "."

MulticolumnArrayPlot::usage =
box[MulticolumnArrayPlot["array", "n"]] <> " generates a plot of the values in an array after wrapping into at most " <> box["n"] <> " super\[Hyphen]columns.\n" <>
box[MulticolumnArrayPlot["array", "n", "spacing"]] <> " leaves " <> box["spacing"] <> " white cells between successive super\[Hyphen]columns."

MultiRiffle::usage =
box[MultiRiffle[SubscriptList["a", {1, 2, "..."}], SubscriptList["b", {1, 2, "..."}], "\[Ellipsis]", SubscriptList["z", {1, 2, "..."}]]] <> " gives " <> box[{Subscript["a", 1], Subscript["b", 1], "\[Ellipsis]", Subscript["z", 1], Subscript["a", 2], Subscript["b", 2], "\[Ellipsis]", Subscript["z", 2], "\[Ellipsis]"}] <> "."

MultirowArrayPlot::usage =
box[MultirowArrayPlot["array", "n"]] <> " generates a plot of the values in an array after wrapping into at most " <> box["n"] <> " super\[Hyphen]rows.\n" <>
box[MultirowArrayPlot["array", "n", "spacing"]] <> " leaves " <> box["spacing"] <> " white cells between successive super\[Hyphen]rows."

MultisetComplement::usage =
box[MultisetComplement[SubscriptSequence["list", {"all", Null}]]] <> " removes elements in " <> box["list"] <> " from " <> box[Subscript["list", "all"]] <> ", respecting multiplicity."

Multisets::usage =
box[Multisets["list", "n"]] <> " gives all multisets of " <> box["list"] <> " containing at most " <> box["n"] <> " elements.\n" <>
box[Multisets["list", {"n"}]] <> " gives all multisets containing exactly " <> box["n"] <> " elements.\n" <>
box[Multisets["list", SubscriptList["n", {"min", "max"}]]] <> " gives all multisets containing between " <> box[Subscript["n", "min"]] <> " and " <> box[Subscript["n", "max"]] <> " elements."

NextTuple::usage =
box[NextTuple["tuple", "alphabet"]] <> " gives the tuple following " <> box["tuple"] <> " in the lexicographic ordering specified by the order of " <> box["alphabet"] <> ".\n" <>
box[NextTuple["tuple", SubscriptList["alphabet", {1, 2, "..."}]]] <> " gives the following tuple in a mixed base."

Occurrence::usage =
box[Occurrence["list", "pattern"]] <> " gives the position of the first element in " <> box["list"] <> " that matches " <> box["pattern"] <> ", or Missing[\"NotFound\"] if no such element is found.\n" <>
box[Occurrence["list", "pattern" -> "f"]] <> " applies " <> box["f"] <> " to the position of the matching element.\n" <>
box[Occurrence["list", "pattern", "default"]] <> " gives " <> box["default"] <> " if no element matching " <> box["pattern"] <> " is found.\n" <>
box[Occurrence["list", "pattern", "default", "n"]] <> " finds the " <> box["n"] <> "th matching element, where negative " <> box["n"] <> " counts from the end of the list."

Only::usage =
box[Only["expr"]] <> " gives the only element in " <> box["expr"] <> " if " <> box["expr"] <> " has length 1, and gives $Failed otherwise.\n" <>
box[Only["expr", "default"]] <> " gives " <> box["default"] <> " if " <> box["expr"] <> " does not have a unique element."

Orbit::usage =
box[Orbit["f", "expr"]] <> " generates a list of all expressions that can be reached from " <> box["expr"] <> " by applying " <> box["f"] <> " repeatedly.\n" <>
box[Orbit[SubscriptList["f", {1, 2, "..."}], "expr"]] <> " generates a list of all expressions that can be reached from " <> box["expr"] <> " by applying sequences of " <> box[Subscript["f", "i"]] <> "."

OrbitRepresentatives::usage =
box[OrbitRepresentatives["f", "list"]] <> " gives a list of representatives from each orbit of the elements in " <> box["list"] <> " under applications of " <> box["f"] <> ".\n" <>
box[OrbitRepresentatives[SubscriptList["f", {1, 2, "..."}], "list"]] <> " gives representatives of orbits under " <> box[SubscriptSequence["f", {1, 2, "..."}]] <> "."

ParallelSelect::usage =
box[ParallelSelect["list", "crit"]] <> " picks out in parallel all elements " <> box[Subscript["e", "i"]] <> " of " <> box["list"] <> " for which " <> box["crit"[Subscript["e", "i"]]] <> " is True."

PartitionAfter::usage =
box[PartitionAfter["list", "pattern"]] <> " partitions " <> box["list"] <> " by placing a break after each element matching " <> box["pattern"] <> ".\n" <>
box[PartitionAfter["list", "pattern", "n"]] <> " places a break after each of the first " <> box["n"] <> " such elements."

PartitionBefore::usage =
box[PartitionBefore["list", "pattern"]] <> " partitions " <> box["list"] <> " by placing a break before each element matching " <> box["pattern"] <> ".\n" <>
box[PartitionBefore["list", "pattern", "n"]] <> " places a break before the first " <> box["n"] <> " such elements."

PartitionAt::usage =
box[PartitionAt["list", SubscriptList["n", {1, 2, "..."}]]] <> " partitions " <> box["list"] <> " by placing breaks after positions " <> box[SubscriptSequence["n", {1, 2, "..."}]] <> ".\n" <>
box[PartitionAt["list", "n"]] <> " places a break after position " <> box["n"] <> "."

Period::usage =
box[Period["list"]] <> " gives the repetition period of " <> box["list"] <> "."

PeriodLength::usage =
box[PeriodLength["list"]] <> " gives the period length of " <> box["list"] <> "."

Portion::usage =
box[Portion["list"]] <> " gives the first half of " <> box["list"] <> ".\n" <>
box[Portion["list", 1/"n"]] <> " gives the first " <> box["n"] <> "th of " <> box["list"] <> ".\n" <>
box[Portion["list", "frac", "i"]] <> " gives the " <> box["i"] <> "th fraction of " <> box["list"] <> ".\n" <>
box[Portion["list", "frac", SubscriptList["i", {"min", "max"}]]] <> " gives parts " <> box[Subscript["i", "min"]] <> " through " <> box[Subscript["i", "max"]] <> "."

RaggedArrayDepth::usage =
box[RaggedArrayDepth["expr"]] <> " gives the depth to which " <> box["expr"] <> " consists of nested lists."

RationalRange::usage =
(*
box[RationalRange[Subscript["i", "max"], Subscript["d", "max"]]] <> " generates the list of all rational numbers from 1 to " <> box[Subscript["i", "max"]] <> " with denominator at most " <> box[Subscript["d", "max"]] <> ".\n" <>
*)
box[RationalRange[Subscript["i", "min"], Subscript["i", "max"], Subscript["d", "max"]]] <> " generates the list of all rational numbers from " <> box[Subscript["i", "min"]] <> " to " <> box[Subscript["i", "max"]] <> " with denominator at most " <> box[Subscript["d", "max"]] <> ".\n" <>
box[RationalRange[Subscript["i", "min"], Subscript["i", "max"], SubscriptList["d", {"min", "max"}]]] <> " generates rational numbers with denominators " <> box[Subscript["d", "min"]] <> " through " <> box[Subscript["d", "max"]] <> "."

ReverseAll::usage =
box[ReverseAll["expr"]] <> " reverses every subexpression in " <> box["expr"] <> "."

RotateClockwise::usage =
box[RotateClockwise["array", "n"]] <> " rotates " <> box["array"] <> " clockwise " <> box["n"] <> " times.\n" <>
box[RotateClockwise["array"]] <> " rotates clockwise once."

RotateCounterClockwise::usage =
box[RotateCounterClockwise["array", "n"]] <> " rotates " <> box["array"] <> " counter\[Hyphen]clockwise " <> box["n"] <> " times.\n" <>
box[RotateCounterClockwise["array"]] <> " rotates counter\[Hyphen]clockwise once."

RotateLeftTo::usage =
box[RotateLeftTo["list", "pattern"]] <> " rotates " <> box["list"] <> " left until an element matching " <> box["pattern"] <> " is in the first position. If no such element exists, " <> box["list"] <> " is returned.\n" <>
box[RotateLeftTo["list"]] <> " rotates " <> box["list"] <> " left until a nonzero element is in the first position."

RotateRightTo::usage =
box[RotateRightTo["list", "pattern"]] <> " rotates " <> box["list"] <> " right until an element matching " <> box["pattern"] <> " is in the last position. If no such element exists, " <> box["list"] <> " is returned.\n" <>
box[RotateRightTo["list"]] <> " rotates " <> box["list"] <> " right until a nonzero element is in the last position."

Second::usage =
box[Second["expr"]] <> " gives the second element in " <> box["expr"] <> ".\n" <>
box[Second["expr", "default"]] <> " gives the second element if it exists, or " <> box["default"] <> " otherwise."

Shear::usage =
box[Shear["array", "n"]] <> " rotates each row of " <> box["array"] <> " by " <> box["n"] <> " with respect to the previous row.\n" <>
box[Shear["array", "x", "r"]] <> " shears " <> box["array"] <> " at the angle " <> box[ArcTan["x"]] <> " and additionally rotates each row by " <> box["r"] <> ".\n" <>
box[Shear["array", SubscriptList["x", {1, 2, "..."}]]] <> " rotates each subarray on level 1 of " <> box["array"] <> " by the vector " <> box[SubscriptList["x", {1, 2, "..."}]] <> " with respect to the previous subarray."

Sift::usage =
box[Sift["randomobject", "test"]] <> " repeatedly generates a random object until one is found that satisfies the condition " <> box["test"] <> ".\n" <>
box[Sift["randomobject", "test", "n"]] <> " generates a list of " <> box["n"] <> " objects satisfying " <> box["test"] <> "."

SuccessiveMaxima::usage =
box[SuccessiveMaxima["list"]] <> " gives the list " <> box[{{Subscript["x", 1], Subscript["e", 1]}, {Subscript["x", 2], Subscript["e", 2]}, "\[Ellipsis]"}] <> ", where " <> box[SubscriptSequence["e", {1, 2, "..."}]] <> " are the successive maxima of " <> box["list"] <> " and " <> box[SubscriptSequence["x", {1, 2, "..."}]] <> " are the positions at which they occur.\n" <>
box[SuccessiveMaxima["list", "f"]] <> " finds the successive maxima under the fitness function " <> box["f"] <> ".\n" <>
box[SuccessiveMaxima["list", "f", "p"]] <> " finds the successive maxima under the fitness function " <> box["f"] <> " relative to the ordering function " <> box["p"] <> "."

SuccessiveMinima::usage =
box[SuccessiveMinima["list"]] <> " gives the list " <> box[{{Subscript["x", 1], Subscript["e", 1]}, {Subscript["x", 2], Subscript["e", 2]}, "\[Ellipsis]"}] <> ", where " <> box[SubscriptSequence["e", {1, 2, "..."}]] <> " are the successive minima of " <> box["list"] <> " and " <> box[SubscriptSequence["x", {1, 2, "..."}]] <> " are the positions at which they occur.\n" <>
box[SuccessiveMinima["list", "f"]] <> " finds the successive minima under the fitness function " <> box["f"] <> ".\n" <>
box[SuccessiveMinima["list", "f", "p"]] <> " finds the successive minima under the fitness function " <> box["f"] <> " relative to the ordering function " <> box["p"] <> "."

Swap::usage =
box[Swap["list", {"m", "n"}]] <> " exchanges the elements at positions " <> box["m"] <> " and " <> box["n"] <> " of " <> box["list"] <> ".\n" <>
box[Swap["list", SubscriptList["n", {1, 2, "...", "k"}]]] <> " simultaneously moves the element in position " <> box[Subscript["n", 1]] <> " to " <> box[Subscript["n", 2]] <> ", the element in position " <> box[Subscript["n", 2]] <> " to " <> box[Subscript["n", 3]] <> ", \[Ellipsis], and the element in position " <> box[Subscript["n", "k"]] <> " to " <> box[Subscript["n", 1]] <> ".\n" <>
box[Swap["list", Subscript["cycle", 1], Subscript["cycle", 2], "\[Ellipsis]"]] <> " applies the permutations " <> box[Subscript["cycle", "i"]] <> " in succession."

TakeAfter::usage =
box[TakeAfter["list", "pattern"]] <> " gives the elements of " <> box["list"] <> " appearing after the first element matching " <> box["pattern"] <> ".\n" <>
box[TakeAfter["list", "pattern", "n"]] <> " gives the elements of " <> box["list"] <> " appearing after the " <> box["n"] <> "th element matching " <> box["pattern"] <> ". Negative " <> box["n"] <> " counts from the end of the list."

TakeBefore::usage =
box[TakeBefore["list", "pattern"]] <> " gives the elements of " <> box["list"] <> " appearing before the first element matching " <> box["pattern"] <> ".\n" <>
box[TakeBefore["list", "pattern", "n"]] <> " gives the elements of " <> box["list"] <> " appearing before the " <> box["n"] <> "th element matching " <> box["pattern"] <> ". Negative " <> box["n"] <> " counts from the end of the list."

Tile::usage =
box[Tile["list", "len"]] <> " tiles " <> box["list"] <> " to form a periodic list of length " <> box["len"] <> ".\n" <>
box[Tile["array", "dims"]] <> " tiles " <> box["array"] <> " to form an array with dimensions " <> box["dims"] <> "."

Trim::usage =
box[Trim["array"]] <> " gives the largest full array that can be obtained by removing elements of a ragged array.\n" <>
box[Trim["array", "levelspec"]] <> " trims a ragged array on levels specified by " <> box["levelspec"] <> "."

Unpad::usage =
box[Unpad["list"]] <> " removes all zeros from the beginning and end of " <> box["list"] <> ".\n" <>
box[Unpad["list", "pattern"]] <> " removes all elements matching " <> box["pattern"] <> " from the beginning and end of " <> box["list"] <> ".\n" <>
box[Unpad["array", "pattern"]] <> " gives the smallest full array obtainable by removing elements matching " <> box["pattern"] <> " from the beginning and end of each level of " <> box["array"] <> ".\n" <>
box[Unpad["array", "pattern", "levelspec"]] <> " unpads on levels specified by " <> box["levelspec"] <> "."

UnpadLeft::usage =
box[UnpadLeft["list"]] <> " removes all zeros from the beginning of " <> box["list"] <> ".\n" <>
box[UnpadLeft["list", "pattern"]] <> " removes all elements matching " <> box["pattern"] <> " from the beginning of " <> box["list"] <> ".\n" <>
box[UnpadLeft["array", "pattern"]] <> " gives the smallest full array obtainable by removing elements matching " <> box["pattern"] <> " from the beginning of each level of " <> box["array"] <> ".\n" <>
box[UnpadLeft["array", "pattern", "levelspec"]] <> " unpads on levels specified by " <> box["levelspec"] <> "."

UnpadRight::usage =
box[UnpadRight["list"]] <> " removes all zeros from the end of " <> box["list"] <> ".\n" <>
box[UnpadRight["list", "pattern"]] <> " removes all elements matching " <> box["pattern"] <> " from the end of " <> box["list"] <> ".\n" <>
box[UnpadRight["array", "pattern"]] <> " gives the smallest full array obtainable by removing elements matching " <> box["pattern"] <> " from the end of each level of " <> box["array"] <> ".\n" <>
box[UnpadRight["array", "pattern", "levelspec"]] <> " unpads on levels specified by " <> box["levelspec"] <> "."

Unriffle::usage =
box[Unriffle["list", "n"]] <> " gives a list of " <> box["n"] <> " lists whose MultiRiffle gives " <> box["list"] <> ".\n" <>
box[Unriffle["list"]] <> " unriffles " <> box["list"] <> " into two components."

$UserCloudDirectory::usage =
"$UserCloudDirectory gives the user\[Hyphen]specific directory where the operating system keeps files stored on the cloud."


(* not necessary for what it's being used for
SetAttributes[NonZero, Listable]
NonZero[x_?NumberQ] := !PossibleZeroQ[x]
*)
NonZero[0] := False
NonZero[_] := True

RealNumberQ[x_] := NumericQ[x] && Element[x, Reals]

SetAttributes[ReapExpressions, HoldFirst]
ReapExpressions[expression_, tag_] :=
	Replace[
		Reap[expression, tag][[2]],
		{only_} :> only
	]

StrictFloor[x_] := If[IntegerQ[x], x - 1, Floor[x]]


Accrete[list : _[___]] := Accumulate[list]
Accrete[list : _[], _] := list
Accrete[list : _[__], Plus] := Accumulate[list]
Accrete[list : _[__], List] :=
	Head[list] @@ FoldList[{Sequence @@ #1, #2} &, {First[list]}, Rest[list]]
Accrete[list : _[__], f : Except[List, _Symbol] /; MemberQ[Attributes[f], Flat]] :=
	Head[list] @@ FoldList[f, f[First[list]], Rest[list]]
Accrete[list : _[__], f_] := f @@@ Accrete[list, List]
SyntaxInformation[Accrete] = {"ArgumentsPattern" -> {_, _., OptionsPattern[]}}

AgreementLength[lists__?(Depth[#] >= 2 &)] :=
LengthWhile[
	Transpose[PadRight[
		List @@@ {lists},
		{Length[{lists}], Max[Length /@ {lists}]},
		Unique[]
	]],
	SameQ @@ # &
]
SyntaxInformation[AgreementLength] = {"ArgumentsPattern" -> {__}}

ArrayMap[f_, array_List, {level_Integer?Positive}, direction : (_Integer?Positive) : 1] /;
	direction <= level <= ArrayDepth[array] :=
Module[{perm, result},
	perm = RotateRight[Range[level, 1, -1], direction - 1];
	result = Map[f, Transpose[array, perm], {level - 1}];
	Transpose[result, perm] /;
		level <= ArrayDepth[result] || Message[ArrayMap::tperm, result, perm]
]
SyntaxInformation[ArrayMap] = {"ArgumentsPattern" -> {_, _, {_}, _.}}
ArrayMap::tperm = "The array `1` cannot be transposed by `2`."

(*
ClassifyBy[list_List, f_ : Identity, g_ : Identity, h_ : Identity] :=
	Last[Reap[Sow[g[#], {f[#]}] & /@ list, _, {h[#2], #1} &]]
*)
ClassifyBy[list_List, f_ : Identity, g_ : Identity, h_ : Identity] :=
	KeyValueMap[{#2, #1} &, GroupBy[list, f -> g, h]]
SyntaxInformation[ClassifyBy] = {"ArgumentsPattern" -> {_, _., _., _.}}

ColumnMap[f_, grid : {___List}, offset : Except[_Rule] : 1, OptionsPattern[]] :=
Module[{p = OptionValue[DefaultElement]},
	With[{length = MatchLength[#, p]},
		f[UnpadRight[Drop[#, length], p], length + offset]
	] & /@
		Transpose[PadRight[grid, {Length[grid], Max[Length /@ grid]}, p]]
]
Options[ColumnMap] = {DefaultElement -> Null}
SyntaxInformation[ColumnMap] = {"ArgumentsPattern" -> {_, _, _., OptionsPattern[]}}

ColumnWrap[
	{},
	n : (_Integer?Positive) : 2,
	spacing : (_?NonNegative) : 3,
	OptionsPattern[]
] :=
	Grid[{}]
ColumnWrap[
	array : {__List},
	n : (_Integer?Positive) : 2,
	spacing : (_?NonNegative) : 3,
	options : OptionsPattern[]
] :=
With[{width = Max[Length /@ array]},
	Grid[
		Flatten[#, 1] & /@ Unriffle[
			PadRight[array, {Length[array], width}, Null],
			Ceiling[Length[array] / n]
		],
		options,
		ItemSize -> Full,
		Spacings -> {
			{Automatic, Append[ConstantArray[Automatic, Max[0, width - 1]], spacing], Automatic},
			Automatic
		}
	]
]
ColumnWrap[
	list : {__},
	n : (_Integer?Positive) : 2,
	spacing : (_?NonNegative) : 3,
	options : OptionsPattern[]
] :=
	ColumnWrap[List /@ list, n, spacing, options]
Options[ColumnWrap] = Options[Grid] /. {(ItemSize -> _) -> (ItemSize -> Full), (Spacings -> _) -> Sequence[]}
SyntaxInformation[ColumnWrap] = {"ArgumentsPattern" -> {_, _., _., OptionsPattern[]}}

Complements[lists : (h_[___] ...)] :=
Table[
	Complement[{lists}[[i]], Sequence @@ Drop[{lists}, {i}]],
	{i, Length[{lists}]}
]
SyntaxInformation[Complements] = {"ArgumentsPattern" -> {___}}

SetAttributes[Counterexamples, HoldAll]
Counterexamples[__, 0] := {}
Counterexamples[expr_, varspec : ({_, __} ...), n : (_Integer?Positive | Infinity) : Infinity] :=
Module[{variables = Join @@ Take[Hold[varspec], All, 1], count = 0, tag},
	ReapExpressions[
		Do[
			If[!TrueQ[expr],
				Sow[variables, tag];
				count++;
				If[count == n, Break[]]
			],
			varspec
		];,
		tag
	]
]
SyntaxInformation[Counterexamples] = {"ArgumentsPattern" -> {_, {_, _., _., _.}, ___}, "LocalVariables" -> {"Table", {2, Infinity}}}

SetAttributes[Examples, HoldAll]
Examples[__, 0] := {}
Examples[expr_, varspec : ({_, __} ...), n : (_Integer?Positive | Infinity) : Infinity] :=
Module[{variables = Join @@ Take[Hold[varspec], All, 1], count = 0, tag},
	ReapExpressions[
		Do[
			If[TrueQ[expr],
				Sow[variables, tag];
				count++;
				If[count == n, Break[]]
			],
			varspec
		];,
		tag
	]
]
SyntaxInformation[Examples] = {"ArgumentsPattern" -> {_, {_, _., _., _.}, ___}, "LocalVariables" -> {"Table", {2, Infinity}}}

FirstSortedRotation[list : _[]] :=
	list
FirstSortedRotation[list : _[__]] :=
	FirstSortedElement[
		RotateLeft[list, #[[1]] - 1] & /@
			Position[list, FirstSortedElement[list], {1}, Heads -> False]
	]
FirstSortedRotation[list : _[__], p_] :=
	FirstSortedElement[
		NestList[RotateLeft, list, Max[0, Length[list] - 1]],
		p
	]
SyntaxInformation[FirstSortedRotation] = {"ArgumentsPattern" -> {_, _.}}

FirstSortedElement[list : _[__]] :=
	list[[First[Ordering[list, 1]]]]
FirstSortedElement[list : _[__], p_] :=
	list[[First[Ordering[list, 1, p]]]]
SyntaxInformation[FirstSortedElement] = {"ArgumentsPattern" -> {_, _.}}

FixedPointPeriod[f_, expr_, n_ : Infinity] :=
Module[{list = {expr}, val = expr, i = 0},
	While[!MemberQ[list, val = f[val]] && i <= n,
		AppendTo[list, val];
		i++
	];
	If[i <= n, Take[list, {Occurrence[list, val], -1}], {}]
]
SyntaxInformation[FixedPointPeriod] = {"ArgumentsPattern" -> {_, _, _.}}


(*** IndentedExport code ***)

StringPower[s_, n_] :=
	StringJoin[ConstantArray[s, n]]

(* Explicitly insert parentheses around expressions for which the head has lower precendence than Rule;
   for example, Function. *)
ToParenthesizedString[expression_ /; TrueQ[Precedence[Head[expression]] < Precedence[Rule]]] :=
	"(" <> ToString[expression, InputForm] <> ")"
ToParenthesizedString[expression_] :=
	ToString[expression, InputForm]
ToParenthesizedIndentedString[expression_ /; TrueQ[Precedence[Head[expression]] < Precedence[Rule]], n_] :=
	"(" <> ToIndentedString[expression, n] <> ")"
ToParenthesizedIndentedString[expression_, n_] :=
	ToIndentedString[expression, n]

ToIndentedString[rulelist : Association[__Rule], n_ : 0] :=
	StringJoin[
		"<|",
		StringTake[ToIndentedString[Normal[rulelist], n], {2, -2}],
		"|>"
	]
ToIndentedString[rulelist : {__Rule}, n_ : 0] :=
	StringJoin[
		"{\n",
		StringPower["\t", n + 1],
		Riffle[
			ToParenthesizedString[First[#]] <> " -> " <> ToParenthesizedIndentedString[Last[#], n + 1] & /@ rulelist,
			",\n" <> StringPower["\t", n + 1]
		],
		"\n",
		StringPower["\t", n],
		"}"
	]
ToIndentedString[rulelists : {(Association | List)[__Rule] ..}, n_ : 0] :=
	StringJoin[
		"{\n",
		StringPower["\t", n + 1],
		Riffle[
			ToIndentedString[#, n + 1] & /@ rulelists,
			",\n" <> StringPower["\t", n + 1]
		],
		"\n",
		StringPower["\t", n],
		"}"
	]
ToIndentedString[expression_, _ : 0] :=
	ToString[expression, InputForm]

IndentedExport[filename_String, data_] :=
	Export[filename, ToIndentedString[data], "Text"]
SyntaxInformation[IndentedExport] = {"ArgumentsPattern" -> {_, _}}

(*** end IndentedExport code ***)


InExpression[] := InExpression[$Line - 1]
InExpression[n_Integer /; n != 0 && n <= $Line] :=
	MakeExpression[ToExpression[InString[n]], StandardForm]
SyntaxInformation[InExpression] = {"ArgumentsPattern" -> {_.}}

IntegerCompositions[
	n_Integer?NonNegative,
	kspec : Alternatives[
		All,
		_Integer?NonNegative,
		Infinity,
		{_Integer?NonNegative},
		{_Integer?NonNegative, _Integer?NonNegative | Infinity},
		{_Integer?NonNegative, _Integer?NonNegative | Infinity, _Integer?NonNegative}
	] : All
] :=
With[{partitions = IntegerPartitions[n, kspec]},
	Sort[
		Join @@ Permutations /@ partitions,
		Positive[FirstCase[Subtract @@ PadRight[{##}], Except[0]]] &
	] /; !MatchQ[partitions, _IntegerPartitions]
]
SyntaxInformation[IntegerCompositions] = {"ArgumentsPattern" -> {_, _.}}

MapAcross[functions_List, arguments_List] /; Length[functions] == Length[arguments] :=
	MapThread[#1[#2] &, {functions, arguments}]
SyntaxInformation[MapAcross] = {"ArgumentsPattern" -> {_, _}}

MapList[f_, list : _[___]] := Table[MapAt[f, list, i], {i, Length[list]}]
SyntaxInformation[MapList] = {"ArgumentsPattern" -> {_, _}}

MatchLength[list : _[___], pattern_] :=
	LengthWhile[list, MatchQ[pattern]]
SyntaxInformation[MatchLength] = {"ArgumentsPattern" -> {_, _}}

MulticolumnArrayPlot[
	array : {__List},
	n : (_Integer?Positive) : 2,
	spacing : (_?NonNegative) : 10,
	options : OptionsPattern[]
] :=
Module[{partition},
	partition = (PadRight[#, {Length[#], Max[Length /@ #]}] &) /@
		Partition[
			array,
			Ceiling[Length[array]/n],
			Ceiling[Length[array]/n],
			1,
			{{}}
		];
	ArrayPlot[
		ArrayFlatten[{
			Riffle[
				partition,
				{ConstantArray[0, {Length[First[partition]], spacing}]}
			]
		}],
		options
	]
]
Options[MulticolumnArrayPlot] = Options[ArrayPlot]
SyntaxInformation[MulticolumnArrayPlot] = {"ArgumentsPattern" -> {_, _., _., OptionsPattern[]}}

MultiRiffle[listsequence__List] :=
Module[{p},
	TakeBefore[
		Flatten[Transpose[
			PadRight[
				{listsequence},
				{Length[{listsequence}], Min[Length /@ {listsequence}] + 1},
				p
			]
		], 1],
	p]
]
SyntaxInformation[MultiRiffle] = {"ArgumentsPattern" -> {__}}

MultirowArrayPlot[
	array : {__List},
	n : (_Integer?Positive) : 2,
	spacing : (_?NonNegative) : 10,
	options : OptionsPattern[]
] :=
Module[{width = Ceiling[Max[Length /@ array]/n], partition, p},
	partition = Partition[
		PadRight[
			array,
			(* This list tells PadRight to only pad in the first two dimensions. *)
			{Automatic, Automatic},
			p
		],
		{Length[array], width},
		{Length[array], width},
		1,
		p
	];
	ArrayPlot[
		ArrayFlatten[
			Riffle[
				Transpose[partition],
				{{ConstantArray[0, {spacing, width}]}}
			]
		] /. p -> Sequence[],
		options
	]
]
Options[MultirowArrayPlot] = Options[ArrayPlot]
SyntaxInformation[MultirowArrayPlot] = {"ArgumentsPattern" -> {_, _., _., OptionsPattern[]}}

MultisetComplement[baseelements_List, removalelements___List] :=
	Fold[DeleteCases[#1, #2, {1}, 1] &, baseelements, Join[removalelements]]
SyntaxInformation[MultisetComplement] = {"ArgumentsPattern" -> {__}}

Multisets[_[], {_Integer?Positive} | ({n1_Integer, n2_Integer} /; 0 < n1 <= n2)] := {}
Multisets[h_[], _Integer?NonNegative | {0} | {0, _Integer?NonNegative}] := {h[]}
Multisets[set : _[__], n_Integer?NonNegative] := Multisets[set, {0, n}]
Multisets[set : _[__], {n_Integer?NonNegative}] := Multisets[set, {n, n}]
Multisets[set : h_[__], {n1_Integer, n2_Integer} /; 0 <= n1 <= n2] :=
Module[{list = Prepend[Table[0, {Length[set] - 1}], n1]},
	(h @@ Join @@ Table @@@ Transpose[{List @@ set, List /@ #}] &) /@ Reap[
		Sow[list];
		Do[
			If[Most[list] == Table[0, {Length[list] - 1}],
				{list[[-1]], list[[1]]} = {0, list[[-1]] + 1},
				((
					list[[#]]--; list[[# + 1]]++;
					If[# + 2 <= Length[list], {list[[-1]], list[[# + 1]]} = {0, list[[-1]] + 1}]
				) &)[
					Occurrence[list, Except[0], Missing["NotFound"], Evaluate[If[list[[-1]] == 0, -1, -2]]]
				]
			];
			Sow[list]
			,
			{Subtract @@ Binomial[{n2, n1 - 1} + Length[list], Length[list]] - 1}
		]
	][[2, 1]]
]
SyntaxInformation[Multisets] = {"ArgumentsPattern" -> {_, _}}

NextTuple[tuple : h_[__], alphabets : {h_[__] ...}] /;
	And[
		And @@ UnsameQ @@@ alphabets,
		Length[tuple] == Length[alphabets],
		And @@ MapThread[MemberQ, {alphabets, tuple}, 1],
		!MatchQ[tuple, h @@ Last /@ alphabets]
	] :=
Module[{t = tuple, i},
	For[i = Length[t], i > 0, i--,
		Occurrence[
			Most[alphabets[[i]]],
			t[[i]] -> ((t[[i]] = alphabets[[i, # + 1]]; Break[]) &),
			t[[i]] = alphabets[[i, 1]]
		]
	];
	t
]
NextTuple[tuple : h_[__], alphabet : h_[__]] /;
	And[
		UnsameQ @@ alphabet,
		ContainsOnly[List @@ tuple, List @@ alphabet],
		!MatchQ[tuple, h[Last[alphabet] ...]]
	] :=
Module[{t = tuple, i},
	For[i = Length[t], i > 0, i--,
		Occurrence[
			Most[alphabet],
			t[[i]] -> ((t[[i]] = alphabet[[# + 1]]; Break[]) &),
			t[[i]] = alphabet[[1]]
		]
	];
	t
]
SyntaxInformation[NextTuple] = {"ArgumentsPattern" -> {_, _}}

SetAttributes[Occurrence, HoldRest]
Occurrence[list : _[___], Rule[p_, f_], default_ : Missing["NotFound"], n : (_Integer?Positive) : 1] :=
	If[Length[#] >= n,
		f[#[[-1,1]]],
		default
	] & @ Position[list, p, {1}, n, Heads -> False]
Occurrence[list : _[___], Rule[p_, f_], default_, n_Integer?Negative] :=
	If[Length[#] >= -n,
		f[Length[list] + 1 - #[[-1,1]]],
		default
	] & @ Position[Reverse[list], p, {1}, -n, Heads -> False]
Occurrence[list : _[___], p_, default_ : Missing["NotFound"], n : (_Integer?NonZero) : 1] :=
	Occurrence[list, Rule[p, Identity], default, n]
SyntaxInformation[Occurrence] = {"ArgumentsPattern" -> {_, _, _., _.}}

SetAttributes[Only, HoldRest]
Only[_[a_], _ : $Failed] := a
Only[_[___], default_ : $Failed] := default
Only[atom_?AtomQ, _ : $Failed] /; Message[Only::normal, 1, HoldForm[Only][atom]] := Null
SyntaxInformation[Only] = {"ArgumentsPattern" -> {_, _.}}

Orbit[function : Except[_List], expression_] :=
	Orbit[{function}, expression]
Orbit[functions_List, expression_] :=
Module[{orbit = {expression}, elementindex = 1},
	While[elementindex <= Length[orbit],
		orbit = Join[
			orbit,
			(* new elements *)
			DeleteCases[
				Through[functions[orbit[[elementindex]]]],
				Alternatives @@ orbit
			]
		];
		elementindex++
	];
	orbit
]
SyntaxInformation[Orbit] = {"ArgumentsPattern" -> {_, _}}

OrbitRepresentatives[function : Except[_List], list_List] :=
	OrbitRepresentatives[{function}, list]
OrbitRepresentatives[functions_List, list_List] :=
Module[{representatives = {}, remainingelements = list, orbit},
	While[remainingelements != {},
		orbit = Orbit[functions, First[remainingelements]];
		remainingelements = DeleteCases[remainingelements, Alternatives @@ orbit];
		AppendTo[representatives, FirstSortedElement[orbit]]
	];
	representatives
]
SyntaxInformation[OrbitRepresentatives] = {"ArgumentsPattern" -> {_, _}}

ParallelSelect[list : _[___], f_, options : OptionsPattern[]] :=
	ParallelCombine[
		Select[f],
		list,
		options
	]
Options[ParallelSelect] = Options[ParallelCombine]
SyntaxInformation[ParallelSelect] = {"ArgumentsPattern" -> {_, _}}

PartitionAfter[list : _[___], p_, n : (_Integer?NonNegative | Infinity) : Infinity] :=
	PartitionAt[
		list,
		DeleteCases[Flatten[Position[list, p, {1}, n, Heads -> False]], Length[list]]
	]
PartitionBefore[list : _[___], p_, n : (_Integer?NonNegative | Infinity) : Infinity] :=
	PartitionAt[
		list,
		DeleteCases[Flatten[Position[list, p, {1}, n, Heads -> False]] - 1, 0]
	]
SyntaxInformation[PartitionAfter] = {"ArgumentsPattern" -> {_, _, _.}}
SyntaxInformation[PartitionBefore] = {"ArgumentsPattern" -> {_, _, _.}}

PartitionAt[list : _[___], {}] := Head[list] @ list
PartitionAt[list : _[___], positions : {__Integer}] /; Max[Abs[positions]] <= Length[list] :=
Take[list, # + {1, 0}] & /@
	Partition[
		Sort[Join[
			{0, Length[list]},
			positions /. n_Integer?Negative :> Length[list] + n
		]],
		2,
		1
	]
PartitionAt[list_, n_Integer] := PartitionAt[list, {n}]
SyntaxInformation[PartitionAt] = {"ArgumentsPattern" -> {_, _}}

Period[list : _[___]] := Take[list, PeriodLength[list]]
SyntaxInformation[Period] = {"ArgumentsPattern" -> {_}}

PeriodLength[_[]] = 0
PeriodLength[list : _[__]] :=
Module[{length = 1},
	While[Drop[list, length] =!= Drop[list, -length],
		length++
	];
	If[Length[list] < 2 length,
		Message[PeriodLength::full, Take[list, length]]
	];
	length
]
SyntaxInformation[PeriodLength] = {"ArgumentsPattern" -> {_}}
PeriodLength::full = "`1` does not repeat in full."

Portion[list : _[___], frac_ : 1/2, i : Except[_List] : 1] :=
	Portion[list, frac, {i, i}]
Portion[list : _[___], frac_, {imin_, imax_}] /; 1 <= imin <= imax <= 1/frac :=
Take[
	list,
	{
		Ceiling[(imin - 1) frac Length[list]] + 1,
		StrictFloor[imax frac Length[list]] + 1
	}
]
SyntaxInformation[Portion] = {"ArgumentsPattern" -> {_, _., _.}}

RaggedArrayDepth[array_] :=
Module[{depth = Depth[array], i = 0},
	While[
		(* This depth check prevents an infinite loop for  RaggedArrayDepth[{}] . *)
		i <= depth - 2 && !MemberQ[array, Except[_List], {i}],
		i++
	];
	i
]
SyntaxInformation[RaggedArrayDepth] = {"ArgumentsPattern" -> {_}}

RationalRange[intervalmin_, intervalmax_, {denominatormin_Integer?Positive, denominatormax_Integer?Positive, denominatorstep_Integer?Positive}] /;
		TrueQ[Element[{intervalmin, intervalmax}, Reals]] :=
	Sort[Join @@
		Table[
			Select[
				Range[Ceiling[denominator intervalmin], Floor[denominator intervalmax]],
				CoprimeQ[#, denominator] &
			]/denominator,
			{denominator, denominatormin, denominatormax, denominatorstep}
		]
	]
(* This isn't worth supporting, because one frequently types things like  RationalRange[3/2, 2]  forgetting to give a denominator bound because there's no syntax coloring for the missing argument.
RationalRange[imax_, denominatorspec_] :=
	RationalRange[1, imax, denominatorspec]
*)
RationalRange[imin_, imax_, denominatormax_Integer?Positive] :=
	RationalRange[imin, imax, {1, denominatormax, 1}]
RationalRange[imin_, imax_, {denominatormin_Integer?Positive, denominatormax_Integer?Positive}] :=
	RationalRange[imin, imax, {denominatormin, denominatormax, 1}]
SyntaxInformation[RationalRange] = {"ArgumentsPattern" -> {_, _, _}}

ReverseAll[expr : _[__]] := ReverseAll /@ Reverse[expr]
ReverseAll[expr_] := expr
SyntaxInformation[ReverseAll] = {"ArgumentsPattern" -> {_}}

RotateClockwise[array_ /; ArrayDepth[array] >= 2, n_Integer : 1] :=
	Nest[Transpose[Reverse[#]] &, array, Mod[n, 4]]
RotateCounterClockwise[array_ /; ArrayDepth[array] >= 2, n_Integer : 1] :=
	Nest[Reverse[Transpose[#]] &, array, Mod[n, 4]]
SyntaxInformation[RotateClockwise] = {"ArgumentsPattern" -> {_, _.}}
SyntaxInformation[RotateCounterClockwise] = {"ArgumentsPattern" -> {_, _.}}

RotateLeftTo[list_] := RotateLeftTo[list, Except[0]]
RotateLeftTo[list : _[___], p_] :=
	RotateLeft[list, Occurrence[list, p, 1] - 1]
RotateRightTo[list_] := RotateRightTo[list, Except[0]]
RotateRightTo[list : _[___], p_] :=
	RotateLeft[list, Occurrence[list, p, 1, -1]]
SyntaxInformation[RotateLeftTo] = {"ArgumentsPattern" -> {_, _.}}
SyntaxInformation[RotateRightTo] = {"ArgumentsPattern" -> {_, _.}}

SetAttributes[Second, HoldRest]
Second[_[_, second_, ___], _ : $Failed] := second
Second[expression : _[] | _[_]] /; Message[Second::nosecond, expression] := Null
Second[expression : _[] | _[_], default_] := default
Second[atom_?AtomQ] /; Message[Second::normal, 1, HoldForm[Second][atom]] := Null
Second[atom_?AtomQ, default_] := default
SyntaxInformation[Second] = {"ArgumentsPattern" -> {_, _.}}
Second::nosecond = "`1` has no second element."

Shear[
	array_,
	v : {___?RealNumberQ},
	r : (_?RealNumberQ | {___?RealNumberQ}) : 0,
	OptionsPattern[]
] /; ArrayDepth[array] >= Max[2, Length[v] + 1] && (NumberQ[r] || Length[v] == Length[r]) :=
With[
	{d = Replace[OptionValue[Axis], {
		Top -> 1,
		Center -> Floor[(Length[array] + 1) / 2],
		Bottom -> Length[array],
		a_Integer?(1 <= # <= Length[array] &) :> a,
		a_Integer?(1 <= -# <= Length[array] &) :> Length[array] + a + 1,
		a_ :> (Message[Shear::axis, a]; 1)
	}]},
	MapIndexed[RotateRight[#1, Floor[(First[#2] - d) v] + r] &, array]
]
Shear[
	array_ /; ArrayDepth[array] >= 2,
	x : (_?RealNumberQ) : 1,
	r : (_?RealNumberQ) : 0,
	options : OptionsPattern[]
] := Shear[array, {x}, r, options]
Options[Shear] = {Axis -> Top}
SyntaxInformation[Shear] = {"ArgumentsPattern" -> {_, _., _., OptionsPattern[]}}
Shear::axis = "Invalid row specification `1` received. Using top subarray as axis."

SetAttributes[Sift, HoldFirst]
Sift[object_, test_, OptionsPattern[]] :=
Module[{temp},
	While[!TrueQ[test[temp = object]]];
	temp
]
Sift[object_, test_, n_Integer?NonNegative, OptionsPattern[]] :=
Module[{results = {}, temp},
	While[Length[results] < n,
		temp = object;
		If[TrueQ[test[temp]] && (!OptionValue[Distinct] || UnsameQ @@ Append[results, temp]),
			AppendTo[results, temp]
		]
	];
	results
]
Options[Sift] = {Distinct -> False}
SyntaxInformation[Sift] = {"ArgumentsPattern" -> {_, _, _., OptionsPattern[]}}

SuccessiveMaxima[list : _[___?NumericQ]] :=
Module[{best = First[list]},
	Transpose[{#, list[[#]]}] & @
		Prepend[First /@
			Position[list, y_ /; If[y > best, best = y; True, False], {1}, Heads -> False],
			1
		]
]
SuccessiveMaxima[list : _[___], f_, p_ : Greater] :=
Module[{best = f[First[list]]},
	Transpose[{#, list[[#]]}] & @
		Prepend[First /@
			Position[list, y_ /; If[p[f[y], best], best = f[y]; True, False], {1}, Heads -> False],
			1
		]
]
SyntaxInformation[SuccessiveMaxima] = {"ArgumentsPattern" -> {_, _., _.}}

SuccessiveMinima[list : _[___?NumericQ]] :=
Module[{best = First[list]},
	Transpose[{#, list[[#]]}] & @
		Prepend[First /@
			Position[list, y_ /; If[y < best, best = y; True, False], {1}, Heads -> False],
			1
		]
]
SuccessiveMinima[list : _[___], f_, p_ : Less] :=
Module[{best = f[First[list]]},
	Transpose[{#, list[[#]]}] & @
		Prepend[First /@
			Position[list, y_ /; If[p[f[y], best], best = f[y]; True, False], {1}, Heads -> False],
			1
		]
]
SyntaxInformation[SuccessiveMinima] = {"ArgumentsPattern" -> {_, _., _.}}

Swap[expr_] := expr
Swap[expr_, cycles__List] /; MatchQ[Flatten[{cycles}], {___Integer}] :=
Module[{copy = expr, cycle = First[{cycles}], valid = True},
	Quiet[
		Check[
			(copy[[Sequence @@ #1]] = expr[[Sequence @@ #2]]) & @@@
				Transpose[{RotateLeft[cycle], cycle}],
			valid = False,
			{Part::partw, Set::partw}
		],
		{Part::partw, Set::partw}
	];
	(Swap[copy, ##2] &)[cycles] /; (valid || Message[Swap::partw, expr])
]
SyntaxInformation[Swap] = {"ArgumentsPattern" -> {__}}
Swap::partw = "Specified part of `1` does not exist."

TakeAfter[list : _[___], pattern_, n : (_Integer?NonZero) : 1] :=
	Drop[list, Occurrence[list, pattern, All, n]]
TakeBefore[list : _[___], pattern_, n : (_Integer?NonZero) : 1] :=
	Take[list, Occurrence[list, pattern -> (# - 1 &), All, n]]
DropAfter[list : _[___], pattern_, n : (_Integer?NonZero) : 1] :=
	Take[list, Occurrence[list, pattern, All, n]]
DropBefore[list : _[___], pattern_, n : (_Integer?NonZero) : 1] :=
	Drop[list, Occurrence[list, pattern -> (# - 1 &), All, n]]
SyntaxInformation[TakeAfter] = {"ArgumentsPattern" -> {_, _, _.}}
SyntaxInformation[TakeBefore] = {"ArgumentsPattern" -> {_, _, _.}}
SyntaxInformation[DropAfter] = {"ArgumentsPattern" -> {_, _, _.}}
SyntaxInformation[DropBefore] = {"ArgumentsPattern" -> {_, _, _.}}

Tile[list : _[], 0] := list
Tile[list : _[__], length_Integer?NonNegative] :=
	Join @@ Append[
		ConstantArray[list, Floor[length/Length[list]]],
		Take[list, Mod[length, Length[list]]]
	]
Tile[array_List, dimensions : {__Integer?NonNegative}] /; ArrayDepth[array] >= Length[dimensions] :=
	Take[
		ArrayFlatten[
			Table @@ Prepend[
				List /@ Ceiling[dimensions/Dimensions[array, Length[dimensions]]],
				array
			],
			Length[dimensions]
		],
		Sequence @@ dimensions
	]
SyntaxInformation[Tile] = {"ArgumentsPattern" -> {_, _}}

Trim[array_List] :=
	Trim[array, {1, RaggedArrayDepth[array] - 1}]
Trim[expr : Except[_List]] :=
	expr
Trim[array_, level_Integer?NonNegative] /;
		RaggedArrayDepth[array] - 1 >= level :=
	Trim[array, {1, level}]
Trim[array_, {level_Integer?NonNegative}] /;
		RaggedArrayDepth[array] - 1 >= level :=
	Trim[array, {level, level}]
Trim[array_, {levelmin_Integer?NonNegative, levelmax_Integer?NonNegative}] /;
		RaggedArrayDepth[array] - 1 >= Min[levelmin, levelmax] :=
	Fold[
		Function[{expr, level},
			With[{length = Min[Map[Length, expr, {level}]]},
				Map[Take[#, length] &, expr, {level}]
			]
		],
		array,
		Range[levelmin, levelmax]
	]
SyntaxInformation[Trim] = {"ArgumentsPattern" -> {_, _.}}

UnpadLeft[array_, pattern_ : 0] :=
	UnpadLeft[array, pattern, ArrayDepth[array]]
UnpadLeft[array_, pattern_, level_Integer?Positive] :=
	UnpadLeft[array, pattern, {1, level}]
UnpadLeft[array_, pattern_, {level_Integer?Positive}] :=
	UnpadLeft[array, pattern, {level, level}]
UnpadLeft[list_List, pattern_, {1, 1}] :=
	Drop[list, LengthWhile[list, MatchQ[pattern]]]
(* TODO Allow negative integers (and 0?) in the level specification. *)
UnpadLeft[array_, pattern_, {levelmin_Integer?Positive, Infinity}] :=
	UnpadLeft[array, pattern, {levelmin, ArrayDepth[array]}]
UnpadLeft[array_, pattern_, levelspec : {levelmin_Integer?Positive, levelmax_Integer?Positive}] :=
With[{depth = ArrayDepth[array]},
	Take @@
		Join[
			{array},
			ConstantArray[All, levelmin - 1],
			Replace[
				Take[Position[array, Except[pattern], {depth}, Heads -> False], All, levelspec],
				{
					{} :> ConstantArray[0, levelmax - levelmin + 1],
					positions_ :> ({Min[#], -1} &) /@ Transpose[positions]
				}
			],
			ConstantArray[All, depth - levelmax]
		] /; levelmin <= levelmax <= depth
]
SyntaxInformation[UnpadLeft] = {"ArgumentsPattern" -> {_, _., _.}}

UnpadRight[array_, pattern_ : 0] :=
	UnpadRight[array, pattern, ArrayDepth[array]]
UnpadRight[array_, pattern_, level_Integer?Positive] :=
	UnpadRight[array, pattern, {1, level}]
UnpadRight[array_, pattern_, {level_Integer?Positive}] :=
	UnpadRight[array, pattern, {level, level}]
UnpadRight[list_List, pattern_, {1, 1}] :=
	Drop[list, -LengthWhile[Reverse[list], MatchQ[pattern]]]
(* TODO Allow negative integers (and 0?) in the level specification. *)
UnpadRight[array_, pattern_, {levelmin_Integer?Positive, Infinity}] :=
	UnpadRight[array, pattern, {levelmin, ArrayDepth[array]}]
UnpadRight[array_, pattern_, levelspec : {levelmin_Integer?Positive, levelmax_Integer?Positive}] :=
With[{depth = ArrayDepth[array]},
	Take @@
		Join[
			{array},
			ConstantArray[All, levelmin - 1],
			Replace[
				Take[Position[array, Except[pattern], {depth}, Heads -> False], All, levelspec],
				{
					{} :> ConstantArray[0, levelmax - levelmin + 1],
					positions_ :> Max /@ Transpose[positions]
				}
			],
			ConstantArray[All, depth - levelmax]
		] /; levelmin <= levelmax <= depth
]
SyntaxInformation[UnpadRight] = {"ArgumentsPattern" -> {_, _., _.}}

Unpad[array_, pattern_ : 0] :=
	Unpad[array, pattern, ArrayDepth[array]]
Unpad[array_, pattern_, level_Integer?Positive] :=
	Unpad[array, pattern, {1, level}]
Unpad[array_, pattern_, {level_Integer?Positive}] :=
	Unpad[array, pattern, {level, level}]
(* This is probably faster (than the general down value) when there is not much padding but slower when there is a lot of padding. *)
Unpad[list_List, pattern_, {1, 1}] :=
	UnpadRight[UnpadLeft[list, pattern, {1, 1}], pattern, {1, 1}]
(* TODO Allow negative integers (and 0?) in the level specification. *)
Unpad[array_, pattern_, {levelmin_Integer?Positive, Infinity}] :=
	Unpad[array, pattern, {levelmin, ArrayDepth[array]}]
Unpad[array_, pattern_, levelspec : {levelmin_Integer?Positive, levelmax_Integer?Positive}] :=
With[{depth = ArrayDepth[array]},
	Take @@
		Join[
			{array},
			ConstantArray[All, levelmin - 1],
			Replace[
				Take[Position[array, Except[pattern], {depth}, Heads -> False], All, levelspec],
				{
					{} :> ConstantArray[0, levelmax - levelmin + 1],
					positions_ :> MinMax /@ Transpose[positions]
				}
			],
			ConstantArray[All, depth - levelmax]
		] /; levelmin <= levelmax <= depth
]
SyntaxInformation[Unpad] = {"ArgumentsPattern" -> {_, _., _.}}

Unriffle[{}, m : (_Integer?Positive) : 2] := ConstantArray[{}, m]
Unriffle[list_List, m : (_Integer?Positive) : 2] :=
Module[{p},
	Transpose[Partition[list, m, m, 1, p]] /. p -> Sequence[]
]
SyntaxInformation[Unriffle] = {"ArgumentsPattern" -> {_, _.}}

$UserCloudDirectory = If[
	And[
		$OperatingSystem === "MacOSX",
		DirectoryQ[FileNameJoin[{$HomeDirectory, "Library", "Mobile Documents", "com~apple~CloudDocs"}]]
	],
	FileNameJoin[{$HomeDirectory, "Library", "Mobile Documents", "com~apple~CloudDocs"}],
	None
]


End[]

Protect["ListTricks`*"]

EndPackage[]
