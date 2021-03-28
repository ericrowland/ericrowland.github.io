(* :Title: Parse Words *)

(* :Context: ParseWords` *)

(* :Author: Eric Rowland *)

(* :Date: {2014, 6, 1} *)

(* :Package Version: 1.01 *)

(* :Mathematica Version: 7 *)

(* :Discussion:
	ParseWords is a package for studying parse words of pairs of binary trees
	under a certain grammar related to the four color theorem.
	Documentation can be found at  https://ericrowland.github.io/packages.html .
*)


BeginPackage["ParseWords`", {"BinaryTrees`"}]

ParseWords`Private`$SymbolList = {
	AllParseWords,
	BottomLeafDisjointQ,
	BottomLeafLabels,
	CanonicalWord,
	ConsecutiveLeafPairs,
	DecomposeTrees,
	IndecomposableQ,
	LabelLeaves,
	LabelTree,
	MutuallyCrookedQ,
	ParentLabel,
	ParseWords,
	RootLabel,
	SiblingLabel,
	WeaklyMutuallyCrookedQ
}


Unprotect["ParseWords`*"]

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


AllParseWords::usage =
box[AllParseWords["tree"]] <> " gives the list of words that are parsed by a binary tree."

BottomLeafDisjointQ::usage =
box[BottomLeafDisjointQ[SubscriptSequence["tree", {1, 2}]]] <> " yields True if the path trees " <> box[Subscript["tree", 1]] <> " and " <> box[Subscript["tree", 2]] <> " share no bottom leaves, and False otherwise."

BottomLeafLabels::usage =
box[BottomLeafLabels["tree", "word"]] <> " gives the labels received by the two bottom leaves of a path tree when the leaves are labeled with entries from " <> box["word"] <> "."

CanonicalWord::usage =
box[CanonicalWord["word"]] <> " gives the lexicographically first word equivalent to " <> box["word"] <> " under permutations of the alphabet."

ConsecutiveLeafPairs::usage =
box[ConsecutiveLeafPairs[SubscriptSequence["tree", {1, 2}]]] <> " gives the indices of all pairs of leaves that appear consecutively in a comb structure in two binary trees " <> box[Subscript["tree", 1]] <> " and " <> box[Subscript["tree", 2]] <> "."

DecomposeTrees::usage =
box[DecomposeTrees[SubscriptSequence["tree", {1, 2}]]] <> " gives all levels where partitioning the path trees " <> box[Subscript["tree", 1]] <> " and " <> box[Subscript["tree", 2]] <> " at that level creates the same partition of leaves in both trees."

IndecomposableQ::usage =
box[IndecomposableQ[SubscriptSequence["tree", {1, 2}]]] <> " yields True if the path trees " <> box[Subscript["tree", 1]] <> " and " <> box[Subscript["tree", 2]] <> " are indecomposable, and False otherwise."

LabelLeaves::usage =
box[LabelLeaves["tree", "word"]] <> " labels the leaves of a binary tree with entries from " <> box["word"] <> "."

LabelTree::usage =
box[LabelTree["tree", "word"]] <> " labels the vertices of a binary tree with labels induced by a parse word."

MutuallyCrookedQ::usage =
box[MutuallyCrookedQ[SubscriptSequence["tree", {1, 2}]]] <> " yields True if the binary trees " <> box[Subscript["tree", 1]] <> " and " <> box[Subscript["tree", 2]] <> " are mutually crooked, and False otherwise."

ParentLabel::usage =
box[ParentLabel["tree", "word", "i"]] <> " gives the label received by the parent of the " <> box["i"] <> "th leaf when the leaves are labeled with " <> box["word"] <> "."

ParseWords::usage =
box[ParseWords["tree"]] <> " gives the list of words parsed by a tree that are lexicographically first in their equivalent classes (under permutations of " <> box[{0, 1, 2}] <> ").\n" <>
box[ParseWords[SubscriptSequence["tree", {1, 2, "..."}]]] <> " gives the lexicographically first words that are simultaneously parsed by several trees."

RootLabel::usage =
box[RootLabel["tree", "word"]] <> " gives the label received by the root of a binary tree when the leaves are labeled with entries from " <> box["word"] <> "."

SiblingLabel::usage =
box[SiblingLabel["tree", "word", "i"]] <> " gives the label received by the sibling of the " <> box["i"] <> "th leaf when the leaves are labeled with " <> box["word"] <> "."

WeaklyMutuallyCrookedQ::usage =
box[WeaklyMutuallyCrookedQ[SubscriptSequence["tree", {1, 2}]]] <> " yields True if the path trees " <> box[Subscript["tree", 1]] <> " and " <> box[Subscript["tree", 2]] <> " are weakly mutually crooked, and False otherwise."


SetAttributes[Not3, Orderless]
Not3[0, 1] = 2
Not3[1, 2] = 0
Not3[2, 0] = 1

ternaryword = {(0 | 1 | 2) ..}


parsewords[rootlabel : 0 | 1 | 2, {}] := {{rootlabel}}
(* This might be faster to just compute for one value of i, and then permute. *)
parsewords[rootlabel : 0 | 1 | 2, tree_] := parsewords[rootlabel, tree] =
With[{labels = Complement[{0, 1, 2}, {rootlabel}]},
	Flatten[Join[
		Outer[Join, parsewords[labels[[1]], tree[[1]]], parsewords[labels[[2]], tree[[2]]], 1],
		Outer[Join, parsewords[labels[[2]], tree[[1]]], parsewords[labels[[1]], tree[[2]]], 1]
	], 1]
]
AllParseWords[tree_?BinaryTreeQ] := Union[parsewords[0, tree], parsewords[1, tree], parsewords[2, tree]]
SyntaxInformation[AllParseWords] = {"ArgumentsPattern" -> {_}}

BottomLeafDisjointQ[tree1_?PathTreeQ, tree2_?PathTreeQ] :=
With[{n = Count[tree1, {}, {0, Infinity}]},
	Intersection[BottomLeafLabels[tree1, Range[n]], BottomLeafLabels[tree2, Range[n]]] == {} /;
		n == Count[tree2, {}, {0, Infinity}]
]
SyntaxInformation[BottomLeafDisjointQ] = {"ArgumentsPattern" -> {_, _}}

BottomLeafLabels[tree_?PathTreeQ, word : {Except[_List] ..}] /; Count[tree, {}, {0, Infinity}] == Length[word] :=
	First[Cases[LabelLeaves[tree, word], {Except[_List] ..}, {0, Infinity}, 1]]
SyntaxInformation[BottomLeafLabels] = {"ArgumentsPattern" -> {_, _}}

CanonicalWord[word : {0 .. | 1 .. | 2 ..}] := ConstantArray[0, Length[word]]
CanonicalWord[word : ternaryword] := word /. Thread[
	(Append[#, Not3 @@ #] &)[
		Take[First /@ Split[word], 2]
	] -> {0, 1, 2}
]
SyntaxInformation[CanonicalWord] = {"ArgumentsPattern" -> {_}}

ConsecutiveLeafPairs[tree1_?BinaryTreeQ, tree2_?BinaryTreeQ] :=
With[{n = Count[tree1, {}, {0, Infinity}]},
	Intersection @@ (Cases[
		LabelLeaves[#, Range[n]],
		{a_Integer, {b_Integer, _}} | {{_, a_Integer}, b_Integer} :> {a, b},
		{0, Infinity}
	] &) /@ {tree1, tree2} /;
		n == Count[tree2, {}, {0, Infinity}]
]
SyntaxInformation[ConsecutiveLeafPairs] = {"ArgumentsPattern" -> {_, _}}

DecomposeTrees[tree1_?PathTreeQ, tree2_?PathTreeQ] :=
Module[{n = Count[tree1, {}, {0, Infinity}], labeledtree1, labeledtree2},
	labeledtree1 = LabelLeaves[tree1, Range[n]];
	labeledtree2 = LabelLeaves[tree2, Range[n]];
	Select[Range[n - 1],
		Cases[TreeChop[labeledtree1, #], _Integer, {0, Infinity}] ==
			Cases[TreeChop[labeledtree2, #], _Integer, {0, Infinity}] &
	] - 1 /;
		n == Count[tree2, {}, {0, Infinity}]
]
SyntaxInformation[DecomposeTrees] = {"ArgumentsPattern" -> {_, _}}

IndecomposableQ[tree1_?PathTreeQ, tree2_?PathTreeQ] :=
	DecomposeTrees[tree1, tree2] == {0}
SyntaxInformation[IndecomposableQ] = {"ArgumentsPattern" -> {_, _}}

LabelLeaves[tree_?BinaryTreeQ, word_List] /; Count[tree, {}, {0, Infinity}] == Length[word] :=
Module[{i = 1},
	tree /. {} :> word[[i++]]
]
SyntaxInformation[LabelLeaves] = {"ArgumentsPattern" -> {_, _}}

LabelTree[tree_?BinaryTreeQ, word : ternaryword] /; Count[tree, {}, {0, Infinity}] == Length[word] :=
With[
	{
		labeledtree = LabelLeaves[tree, Through[word[]]] //.
			{a_Integer[v___], b_Integer[w___]} :> Not3[a, b][a[v], b[w]]
	},
	labeledtree /; FreeQ[labeledtree, Not3]
]
SyntaxInformation[LabelTree] = {"ArgumentsPattern" -> {_, _}}

MutuallyCrookedQ[tree1_?BinaryTreeQ, tree2_?BinaryTreeQ] /;
		Count[tree1, {}, {0, Infinity}] == Count[tree2, {}, {0, Infinity}] :=
	ConsecutiveLeafPairs[tree1, tree2] == {}
SyntaxInformation[MutuallyCrookedQ] = {"ArgumentsPattern" -> {_, _}}

ParentLabel[tree_?BinaryTreeQ, word : ternaryword, leaf_Integer?Positive] /;
	2 <= Count[tree, {}, {0, Infinity}] == Length[word] >= leaf :=
Module[{i = 1},
	First[Cases[
		LabelTree[tree, word] /. h_[] :> h[i++],
		parent_[_, _[leaf]] | parent_[_[leaf], _] :> parent,
		{0, Infinity}
	]]
]
SyntaxInformation[ParentLabel] = {"ArgumentsPattern" -> {_, _, _}}

(* Probably this is not a great implementation; it should just call parsewords[i,tree] for one value of i. *)
ParseWords[tree_?BinaryTreeQ] := Cases[AllParseWords[tree], {0} | {(0) .., 1, ___}]
ParseWords[trees__?BinaryTreeQ] := Intersection @@ ParseWords /@ {trees}
SyntaxInformation[ParseWords] = {"ArgumentsPattern" -> {__}}

RootLabel[tree_?BinaryTreeQ, word : ternaryword] /; Count[tree, {}, {0, Infinity}] == Length[word] :=
With[{label = LabelLeaves[tree, word] /. List -> Not3},
	label /; !MatchQ[label, _Not3]
]
SyntaxInformation[RootLabel] = {"ArgumentsPattern" -> {_, _}}

SiblingLabel[tree_?BinaryTreeQ, word : ternaryword, leaf_Integer?Positive] /;
	2 <= Count[tree, {}, {0, Infinity}] == Length[word] >= leaf :=
Module[{i = 1},
	First[Cases[
		LabelTree[tree, word] /. h_[] :> h[i++],
		_[sibling_[___], _[leaf]] | _[_[leaf], sibling_[___]] :> sibling,
		{0, Infinity}
	]]
]
SyntaxInformation[SiblingLabel] = {"ArgumentsPattern" -> {_, _, _}}

(* I think this only works right for path trees. *)
WeaklyMutuallyCrookedQ[tree1_?PathTreeQ, tree2_?PathTreeQ] /;
	Count[tree1, {}, {0, Infinity}] == Count[tree2, {}, {0, Infinity}] :=
Count[
	Partition[Transpose[(Abs[Differences[Length /@ Position[#, {}]]] &) /@ {tree1, tree2}], 2, 1],
	{{1, 1}, {1, 1}}
] == 0
SyntaxInformation[WeaklyMutuallyCrookedQ] = {"ArgumentsPattern" -> {_, _}}


End[]

Protect["ParseWords`*"]

EndPackage[]
