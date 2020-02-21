(* :Title: Pocket Change *)

(* :Context: PocketChange` *)

(* :Author: Eric Rowland *)

(* :Date: {2013, 11, 12} *)

(* :Package Version: 1.02 *)

(* :Mathematica Version: 9 *)

(* :Discussion:
	PocketChange is a package for analyzing the long-term behavior of the set of coins in one's pocket.
	Documentation can be found at  http://people.hofstra.edu/Eric_Rowland/packages.html .
*)


BeginPackage["PocketChange`"]

PocketChange`Private`$SymbolList = {
	BigSpenderBestPartition,
	BigSpenderTransaction,
	DistinctSubsets,
	GreedyPartition,
	PartitionList,
	PenniesFirstBigSpenderTransaction
}


Unprotect["PocketChange`*"]

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


BigSpenderBestPartition::usage =
box[BigSpenderBestPartition["partitions"]] <> " breaks ties among a list of integer partitions by favoring larger parts."

BigSpenderTransaction::usage =
box[BigSpenderTransaction["partition", "price", "currency"]] <> " gives the state after a big spender transaction in which the price is " <> box["price"] <> " and the previous state was " <> box["partition"] <> ".\n" <>
box[BigSpenderTransaction["partition", "price"]] <> " uses the U.S. currency " <> box[{1, 5, 10, 25}] <> ".\n" <>
box[BigSpenderTransaction["partition", "price", "currency", "modulus"]] <> " uses a modulus different from 100."

DistinctSubsets::usage =
box[DistinctSubsets["list"]] <> " gives a list of all distinct subsets of " <> box["list"] <> "."

GreedyPartition::usage =
box[GreedyPartition["n", "currency"]] <> " gives the integer partition of " <> box["n"] <> " into parts from " <> box["currency"] <> " found by the greedy algorithm.\n" <>
box[GreedyPartition["n"]] <> " uses the U.S. currency " <> box[{1, 5, 10, 25}] <> "."

PartitionList::usage =
box[PartitionList["currency", "modulus"]] <> " gives a list of all integer partitions using parts from " <> box["currency"] <> " such that the sum of the parts of any single type in any partition is less than " <> box["modulus"] <> ".\n" <>
box[PartitionList[]] <> " uses the U.S. currency " <> box[{1, 5, 10, 25}] <> " and modulus 100."

PenniesFirstBigSpenderTransaction::usage =
box[PenniesFirstBigSpenderTransaction["partition", "price", "currency"]] <> " gives the state after a pennies\[Hyphen]first big spender transaction in which the price is " <> box["price"] <> " and the previous state was " <> box["partition"] <> ".\n" <>
box[PenniesFirstBigSpenderTransaction["partition", "price"]] <> " uses the U.S. currency " <> box[{1, 5, 10, 25}] <> ".\n" <>
box[PenniesFirstBigSpenderTransaction["partition", "price", "currency", "modulus"]] <> " uses a modulus different from 100."


MultisetComplement[baseelements_List, removalelements___List] :=
	Fold[DeleteCases[#1, #2, {1}, 1] &, baseelements, Join[removalelements]]


BigSpenderBestPartition[{partition : {___Integer?Positive}}] := partition
BigSpenderBestPartition[listofpartitions : {{___Integer?Positive} ..}] :=
With[{max = Max[listofpartitions]},
	Prepend[
		BigSpenderBestPartition[Cases[
			listofpartitions,
			partition : {___, max, ___} :> MultisetComplement[partition, {max}]
		]],
		max
	]
]
SyntaxInformation[BigSpenderBestPartition] = {"ArgumentsPattern" -> {_}}

BigSpenderTransaction[
	pocketpartition : {___Integer?Positive},
	price_Integer,
	currency : {___Integer?Positive} : {1, 5, 10, 25},
	modulus : (_Integer?Positive) : 100
] /; 0 <= price < modulus :=
Module[{exactorgreaterchangepartitions, whatwepay},
	exactorgreaterchangepartitions = Select[DistinctSubsets[pocketpartition], Total[#] >= price &];
	If[exactorgreaterchangepartitions != {},
		whatwepay = BigSpenderBestPartition[Select[exactorgreaterchangepartitions, Total[#] == Min[Total /@ exactorgreaterchangepartitions] &]];
		Reverse[Sort[Join[
			MultisetComplement[pocketpartition, whatwepay],
			GreedyPartition[Total[whatwepay] - price, currency]
		]]]
		,
		Reverse[Sort[Join[pocketpartition, GreedyPartition[modulus - price, currency]]]]
	]
]
SyntaxInformation[BigSpenderTransaction] = {"ArgumentsPattern" -> {_, _, _., _.}}

DistinctSubsets[list_List] :=
With[{tallies = Tally[list]},
	Prepend[
		Join @@ (Flatten[
			Outer[
				Join,
				Sequence @@ (Table[ConstantArray[tallies[[#, 1]], i], {i, tallies[[#, 2]]}] &) /@ #,
				1
			],
			Length[#] - 1
		] &) /@
			Rest[Subsets[Range[Length[tallies]]]],
		{}
	]
]
SyntaxInformation[DistinctSubsets] = {"ArgumentsPattern" -> {_}}

GreedyPartition[
	n_Integer?NonNegative,
	currency : {___Integer?Positive} : {1, 5, 10, 25}
] :=
Module[{remaining = n, partition = {}, max, failed = False},
	While[remaining > 0,
		max = Max[Select[currency, remaining >= # &]];
		If[max === -Infinity,
			failed = True; Break[]
		];
		AppendTo[partition, max];
		remaining -= max
	];
	partition /; !failed
]
SyntaxInformation[GreedyPartition] = {"ArgumentsPattern" -> {_, _.}}

PartitionList[
	currency : {___Integer?Positive} : {1, 5, 10, 25},
	modulus : (_Integer?Positive) : 100
] :=
	Select[
		(Join @@ MapThread[ConstantArray, {Reverse[currency], #}] &) /@
			Tuples[(Range[0, Ceiling[modulus/#] - 1] &) /@ Reverse[currency]],
		Total[#] < modulus &
	]
SyntaxInformation[PartitionList] = {"ArgumentsPattern" -> {_., _.}}

PenniesFirstBigSpenderTransaction[
	pocketpartition : {___Integer?Positive},
	price_Integer,
	currency : {___Integer?Positive} : {1, 5, 10, 25},
	modulus : (_Integer?Positive) : 100
] /; 0 <= price < modulus :=
Module[{remainingpocketpartition, remainingprice, exactorgreaterchangepartitions, whatwepay},
	{remainingpocketpartition, remainingprice} = If[Count[pocketpartition, 1] >= Mod[price, 5],
		{MultisetComplement[pocketpartition, ConstantArray[1, Mod[price, 5]]], Floor[price, 5]},
		{pocketpartition, price}
	];
	exactorgreaterchangepartitions =
	Select[DistinctSubsets[remainingpocketpartition], Total[#] >= remainingprice &];
	If[exactorgreaterchangepartitions != {},
		whatwepay = BigSpenderBestPartition[Select[
			exactorgreaterchangepartitions,
			Total[#] == Min[Total /@ exactorgreaterchangepartitions] &
		]];
		Reverse[Sort[Join[
			MultisetComplement[remainingpocketpartition, whatwepay],
			GreedyPartition[Total[whatwepay] - remainingprice, currency]
		]]]
		,
		Reverse[Sort[Join[
			remainingpocketpartition,
			GreedyPartition[modulus - remainingprice, currency]
		]]]
	]
]
SyntaxInformation[PenniesFirstBigSpenderTransaction] = {"ArgumentsPattern" -> {_, _, _., _.}}


End[]

Protect["PocketChange`*"]

EndPackage[]
