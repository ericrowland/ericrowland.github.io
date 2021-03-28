(* :Title: Binary Trees *)

(* :Context: BinaryTrees` *)

(* :Author: Eric Rowland *)

(* :Date: {2016, 5, 12} *)

(* :Package Version: 1.04 *)

(* :Mathematica Version: 7 *)

(* :Discussion:
	BinaryTrees is a package for generating, visualizing, and manipulating binary trees.
	Documentation can be found at  https://ericrowland.github.io/packages.html .
*)


BeginPackage["BinaryTrees`"]

BinaryTrees`Private`$SymbolList = {
	BareTreeForm,
	BinaryTree,
	BinaryTreeQ,
	BinaryTrees,
	CompleteBinaryTree,
	DyckWord,
	DyckWordQ,
	DyckWords,
	FromBinaryTree,
	FromDyckWord,
	FromPathTree,
	FromTreeEdgeRules,
	LeftCombTree,
	LeftCrookedTree,
	LeftPathTree,
	LeftTurnTree,
	LevelHeight,
	PathTree,
	PathTreeQ,
	PathTrees,
	RandomBinaryTree,
	RandomPathTree,
	RankBinaryTree,
	RankTree,
	RightCombTree,
	RightCrookedTree,
	RightPathTree,
	RightTurnTree,
	TreeChop,
	TreeEdgeRules,
	Trees
}


Unprotect["BinaryTrees`*"]

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


BareTreeForm::usage =
box[BareTreeForm["expr"]] <> " displays " <> box["expr"] <> " as an unlabeled tree with coloring to indicate instances of __ and ___."

BinaryTree::usage =
box[BinaryTree["tree"]] <> " gives the binary tree corresponding to a tree."

BinaryTreeQ::usage =
box[BinaryTreeQ["expr"]] <> " yields True if " <> box["expr"] <> " is a binary tree, and False otherwise."

BinaryTrees::usage =
box[BinaryTrees["n"]] <> " gives a list of all binary trees with " <> box["n"] <> " leaves."

CompleteBinaryTree::usage =
box[CompleteBinaryTree[2^"n"]] <> " gives the binary tree with " <> box[2^"n"] <> " leaves, all on the lowest level."

DyckWord::usage =
box[DyckWord["tree"]] <> " gives the Dyck word corresponding to a tree."

DyckWordQ::usage =
box[DyckWordQ["string"]] <> " yields True if " <> box["string"] <> " is a Dyck word on {\"0\", \"1\"}, and False otherwise."

DyckWords::usage =
box[DyckWords["n"]] <> " gives a list of the length\[Hyphen]" <> box[2 "n"] <> " Dyck words on {\"0\", \"1\"}."

FromBinaryTree::usage =
box[FromBinaryTree["binarytree"]] <> " gives the tree corresponding to a binary tree."

FromDyckWord::usage =
box[FromDyckWord["word"]] <> " gives the tree corresponding to a Dyck word."

FromPathTree::usage =
box[FromPathTree["pathtree"]] <> " gives the " <> box[{0, 1}] <> "\[Hyphen]tuple corresponding to a path tree."

FromTreeEdgeRules::usage =
box[FromTreeEdgeRules["rules"]] <> " constructs a tree from its list of parent-child relationships, where a vertex is represented by its position in the breadth-first traversal of the tree."

LeftCombTree::usage =
box[LeftCombTree["n"]] <> " gives the " <> box["n"] <> "\[Hyphen]leaf path tree in which only the left child of a vertex has children."

LeftCrookedTree::usage =
box[LeftCrookedTree["n"]] <> " gives the " <> box["n"] <> "\[Hyphen]leaf path tree in which alternate vertices on successive levels have children, beginning with the left child."

LeftPathTree::usage =
box[LeftPathTree[SubscriptSequence["n", {1, 2, "...", "k"}]]] <> " gives the (" <> box[Subscript["n", 1] + Subscript["n", 2] + "\[CenterEllipsis]" + Subscript["n", "k"]] <> ")\[Hyphen]leaf path tree made up of combs of length " <> box[Subscript["n", "i"]] <> ", beginning with a left comb."

LeftTurnTree::usage =
box[LeftTurnTree["n", "m"]] <> " gives the (" <> box["n" + "m"] <> ")\[Hyphen]leaf path tree made up of an (" <> box["n" + 1] <> ")\[Hyphen]leaf left comb and an " <> box["m"] <> "\[Hyphen]leaf right comb."

LevelHeight::usage =
"LevelHeight is an option for BareTreeForm that specifies the height of each tree level."

PathTree::usage =
box[PathTree["tuple"]] <> " gives the path tree corresponding to a " <> box[{0, 1}] <> "\[Hyphen]tuple."

PathTreeQ::usage =
box[PathTreeQ["expr"]] <> " yields True if " <> box["expr"] <> " is a path tree, and False otherwise."

PathTrees::usage =
box[PathTrees["n"]] <> " gives a list of all path trees with " <> box["n"] <> " leaves."

RandomBinaryTree::usage =
box[RandomBinaryTree["n"]] <> " gives a pseudorandom binary tree with " <> box["n"] <> " leaves."

RandomPathTree::usage =
box[RandomPathTree["n"]] <> " gives a pseudorandom path tree with " <> box["n"] <> " leaves."

RankBinaryTree::usage =
box[RankBinaryTree["tree"]] <> " gives the position of an " <> box["n"] <> "\[Hyphen]leaf binary tree in " <> box[BinaryTrees["n"]] <> "."

RankTree::usage =
box[RankTree["tree"]] <> " gives the position of an " <> box["n"] <> "\[Hyphen]vertex tree in " <> box[Trees["n"]] <> "."

RightCombTree::usage =
box[RightCombTree["n"]] <> " gives the " <> box["n"] <> "\[Hyphen]leaf path tree in which only the right child of a vertex has children."

RightCrookedTree::usage =
box[RightCrookedTree["n"]] <> " gives the " <> box["n"] <> "\[Hyphen]leaf path tree in which alternate vertices on successive levels have children, beginning with the right child."

RightPathTree::usage =
box[RightPathTree[SubscriptSequence["n", {1, 2, "...", "k"}]]] <> " gives the (" <> box[Subscript["n", 1] + Subscript["n", 2] + "\[CenterEllipsis]" + Subscript["n", "k"]] <> ")\[Hyphen]leaf path tree made up of combs of length " <> box[Subscript["n", "i"]] <> ", beginning with a right comb."

RightTurnTree::usage =
box[RightTurnTree["n", "m"]] <> " gives the (" <> box["n" + "m"] <> ")\[Hyphen]leaf path tree made up of an (" <> box["n" + 1] <> ")\[Hyphen]leaf right comb and an " <> box["m"] <> "\[Hyphen]leaf left comb."

TreeChop::usage =
box[TreeChop["expr", "d"]] <> " replaces all subexpressions of " <> box["expr"] <> " at depth " <> box["d"] <> " with {}."

TreeEdgeRules::usage =
box[TreeEdgeRules["tree"]] <> " gives a list of parent-child relationships in a tree, where a vertex is represented by its position in the breadth-first traversal of the tree."

Trees::usage =
box[Trees["n"]] <> " gives a list of all rooted trees with " <> box["n"] <> " vertices.\n" <>
box[Trees["n", "degrees"]] <> " gives a list of all rooted trees with " <> box["n"] <> " vertices such that the number of children of each vertex is a member of the list " <> box["degrees"] <> "."


Occurrence[list : _[___], p_] := Position[list, p, {1}, 1, Heads -> False][[-1,1]]

StringReplaceRepeated[
	s_String,
	rules : _Rule | _RuleDelayed | {(_Rule | _RuleDelayed) ...},
	n : (_Integer | Infinity) : Infinity
] := FixedPoint[StringReplace[#, rules] &, s, n]

TopDownReplaceAll[expr_, rules_] :=
Module[{a},
	a[expr] //. {a[h_[body___]] :> a /@ Replace[h[body], rules], a[atom_?AtomQ] :> atom}
]

TreeQ[t_] := MatchQ[t, {___}] && And @@ TreeQ /@ t


BareTreeForm[tree_, opts : OptionsPattern[]] :=
TreeForm[
	tree /. {{Verbatim[__]} -> __, {Verbatim[___]} -> ___},
	(* TODO This isn't great design; specifying ImageSize has no effect unless LevelHeight is set to Automatic. *)
	ImageSize -> If[NumericQ[OptionValue[LevelHeight]],
		{Automatic, Max[Depth[tree] - 2, 1] OptionValue[LevelHeight]},
		OptionValue[ImageSize]
	],
	VertexRenderingFunction -> ({
		Switch[#2,
			HoldForm[Null], RGBColor[.5, 0, 0],
			HoldForm[Verbatim[__]], GrayLevel[.3],
			HoldForm[Verbatim[___]], GrayLevel[.6],
			_, RGBColor[0, 0, .7]
		],
		Point[#1]
	} &)
]
Options[BareTreeForm] = {ImageSize -> Automatic, LevelHeight -> 10}
SyntaxInformation[BareTreeForm] = {"ArgumentsPattern" -> {_, OptionsPattern[]}}

(* Can this be written in terms of BottomUpRelaceAll ? *)
BinaryTree[tree_?TreeQ] :=
Module[{a},
	(Map[a, tree /.{} -> {{}, {}}, {-2}] //.
		{body__a} :> a[{Fold[ReplacePart[#2, 2 -> #1] &, {}, Reverse[Identity @@@ {body}]], {}}]
	)[[1, 1]]
]
SyntaxInformation[BinaryTree] = {"ArgumentsPattern" -> {_}}

BinaryTreeQ[t_] := MatchQ[t, {} | {_, _}] && And @@ BinaryTreeQ /@ t
SyntaxInformation[BinaryTreeQ] = {"ArgumentsPattern" -> {_}}

binaryTrees[0] = {}
binaryTrees[1] = {{}}
binaryTrees[n_] := binaryTrees[n] =
	Join @@ Table[Flatten[Outer[List, binaryTrees[k], binaryTrees[n - k], 1], 1], {k, n - 1}]
BinaryTrees[n_Integer?NonNegative] := binaryTrees[n]
SyntaxInformation[BinaryTrees] = {"ArgumentsPattern" -> {_}}

CompleteBinaryTree[1] = {}
CompleteBinaryTree[n_Integer?Positive] :=
With[{l = Log[2, n]},
	Quiet[
		ReplaceRepeated[{}, {} -> {{}, {}}, MaxIterations -> l],
		ReplaceRepeated::rrlim
	] /; IntegerQ[l]
]
SyntaxInformation[CompleteBinaryTree] = {"ArgumentsPattern" -> {_}}

dyckWords[0] = {""}
dyckWords[1] = {"01"}
dyckWords[n_] := dyckWords[n] =
Join[
	("01" <> # &) /@ dyckWords[n - 1],
	("0" <> # <> "1" &) /@ dyckWords[n - 1],
	Flatten[Table[
		Outer["0" <> #1 <> "1" <> #2 &, dyckWords[i], dyckWords[n - 1 - i]],
		{i, n - 2}
	], 2]
]
DyckWords[n_Integer?NonNegative] := dyckWords[n]
SyntaxInformation[DyckWords] = {"ArgumentsPattern" -> {_}}

DyckWordQ[s_] := StringQ[s] && StringMatchQ[s, ("0" | "1") ...] &&
	MatchQ[Accumulate[Characters[s] /. {"0" -> 1, "1" -> -1}], {} | {_?NonNegative ..., 0}]
SyntaxInformation[DyckWordQ] = {"ArgumentsPattern" -> {_}}

DyckWord[tree_?TreeQ] :=
StringTake[
	StringReplace[
		ToString[tree],
		{"{" -> "0", "}" -> "1", _ -> ""}
	],
	{2, -2}
]
SyntaxInformation[DyckWord] = {"ArgumentsPattern" -> {_}}

FromBinaryTree[binarytree_?BinaryTreeQ] :=
Module[{g},
	{
		TopDownReplaceAll[binarytree, {l_, r_} :> g[{l}, r]] /.
			{g -> Sequence, {} -> Sequence[]}
	}
]
SyntaxInformation[FromBinaryTree] = {"ArgumentsPattern" -> {_}}

FromDyckWord[word_?DyckWordQ] :=
ToExpression["{" <> StringReplaceRepeated[
	word,
	{"0" -> "{", "1" -> "}", "}{" -> "},{"}
] <> "}"]
SyntaxInformation[FromDyckWord] = {"ArgumentsPattern" -> {_}}

FromPathTree[{{}, {}}] = {}
FromPathTree[tree_?PathTreeQ /; tree != {}] :=
Reap[NestWhile[
	Function[t, ((Sow[# - 1]; t[[#]]) &)[Position[t, Except[{}], {1}, Heads -> False][[1, 1]]]],
	tree,
	# != {{}, {}} &
]][[2, 1]]
SyntaxInformation[FromPathTree] = {"ArgumentsPattern" -> {_}}

(* uncommenting below causes things like BinaryTree[{{},{}}] to fail (well, when BinaryTree used to use FromTreeEdgeRules...) *)
FromTreeEdgeRules[{}] = {}
FromTreeEdgeRules[rules : {(*1 -> 2, _*)__Rule}] (*/; LessEqual @@ First /@ rules && Last /@ rules == Range[2, Length[rules] + 1]*) :=
	1 //. Table[n -> Cases[rules, (n -> child_) :> child], {n, rules[[-1, -1]]}]
SyntaxInformation[FromTreeEdgeRules] = {"ArgumentsPattern" -> {_}}

LeftCombTree[n_Integer?Positive] := Nest[{#, {}} &, {}, n - 1]
RightCombTree[n_Integer?Positive] := Nest[{{}, #} &, {}, n - 1]
SyntaxInformation[LeftCombTree] = {"ArgumentsPattern" -> {_}}
SyntaxInformation[RightCombTree] = {"ArgumentsPattern" -> {_}}

LeftCrookedTree[n_Integer /; n >= 2] := PathTree[Mod[Range[0, n - 3], 2]]
RightCrookedTree[n_Integer /; n >= 2] := PathTree[Mod[Range[n - 2], 2]]
SyntaxInformation[LeftCrookedTree] = {"ArgumentsPattern" -> {_}}
SyntaxInformation[RightCrookedTree] = {"ArgumentsPattern" -> {_}}

LeftPathTree[nsequence : (_Integer?Positive ..)] /; Last[{nsequence}] >= 2 :=
PathTree[Join @@ MapIndexed[
	ConstantArray[Mod[First[#2] + 1, 2], #1] &,
	MapAt[# - 2 &, {nsequence}, -1]
]]
RightPathTree[nsequence : (_Integer?Positive ..)] /; Last[{nsequence}] >= 2 :=
PathTree[Join @@ MapIndexed[
	ConstantArray[Mod[First[#2], 2], #1] &,
	MapAt[# - 2 &, {nsequence}, -1]
]]
SyntaxInformation[LeftPathTree] = {"ArgumentsPattern" -> {__}}
SyntaxInformation[RightPathTree] = {"ArgumentsPattern" -> {__}}

LeftTurnTree[n_Integer?Positive, m_Integer?Positive] := LeftPathTree[n, m]
RightTurnTree[n_Integer?Positive, m_Integer?Positive] := RightPathTree[n, m]
SyntaxInformation[LeftTurnTree] = {"ArgumentsPattern" -> {_, _}}
SyntaxInformation[RightTurnTree] = {"ArgumentsPattern" -> {_, _}}

PathTree[tuple : {(0 | 1) ...}] :=
Module[{v},
	Fold[
		#1 /. If[#2 == 0, v -> {v, {}}, v -> {{}, v}] &,
		v,
		tuple
	] /. v -> {{}, {}}
]
SyntaxInformation[PathTree] = {"ArgumentsPattern" -> {_}}

PathTreeQ[tree_] := BinaryTreeQ[tree] && Depth[tree] == Count[tree, {}, {0, Infinity}] + 1
SyntaxInformation[PathTreeQ] = {"ArgumentsPattern" -> {_}}

PathTrees[n_Integer /; n >= 2] := PathTree /@ Tuples[{1, 0}, n - 2]
SyntaxInformation[PathTrees] = {"ArgumentsPattern" -> {_}}

(* This is an implementation of R\[EAcute]my's algorithm (as described in a paper by M\[ADoubleDot]kinen and Siltaneva). *)
RandomBinaryTree[n_Integer?Positive] :=
Module[{max = 1},
	Nest[
		# /. v : Blank[RandomInteger[{1, (max += 2) - 2}]] :>
			RandomChoice[{max[(max - 1)[], v], max[v, (max - 1)[]]}] &,
		1[],
		n - 1
	] /. _Integer -> List
]
SyntaxInformation[RandomBinaryTree] = {"ArgumentsPattern" -> {_}}

RandomPathTree[n_Integer?Positive] := PathTree[RandomChoice[{0, 1}, n - 2]]
SyntaxInformation[RandomPathTree] = {"ArgumentsPattern" -> {_}}

RankBinaryTree[binarytree_?BinaryTreeQ] := Occurrence[BinaryTrees[Count[binarytree, {}, {0, Infinity}]], binarytree]
SyntaxInformation[RankBinaryTree] = {"ArgumentsPattern" -> {_}}

RankTree[tree_?TreeQ] := Occurrence[Trees[Count[tree, _List, {0, Infinity}]], tree]
SyntaxInformation[RankTree] = {"ArgumentsPattern" -> {_}}

TreeChop[tree_, depth_Integer?NonNegative] := Map[{} &, tree, {depth}]
SyntaxInformation[TreeChop] = {"ArgumentsPattern" -> {_, _}}

TreeEdgeRules[tree_?TreeQ] :=
Module[{i = 0, labeledtree},
	labeledtree = Fold[
		Replace[#1, List :> ++i, {#2}, Heads -> True] &,
		tree,
		Range[Depth[tree] - 1]
	];
	Join @@ Table[
		Thread[n -> First[Cases[labeledtree, n[children___] :> Head /@ {children}, {0, Infinity}, 1]]],
		{n, i}
	]
]
SyntaxInformation[TreeEdgeRules] = {"ArgumentsPattern" -> {_}}

(* The necessity of Union makes this not really optimal;
   but Permutations produces duplicates in some cases. *)
trees[0, _List : {}] := {}
trees[1, {___, 0, ___}] := {{}}
trees[1, _List] := {}
trees[n_, degrees_] := trees[n, degrees] =
Union[Join @@ Permutations /@ Join @@ (Flatten[Outer[List, ##, 1], Length[{##}] - 1] &) @@@
	Map[
		trees[#, degrees] &,
		Join @@ (IntegerPartitions[n - 1, {#}] &) /@ degrees,
		{2}
	]
]
Trees[n_Integer?NonNegative, degrees_List /; Unequal @@ degrees] := trees[n, degrees]
Trees[n_Integer?NonNegative] := trees[n, Range[0, n - 1]]
SyntaxInformation[Trees] = {"ArgumentsPattern" -> {_, _.}}


End[]

Protect["BinaryTrees`*"]

EndPackage[]
