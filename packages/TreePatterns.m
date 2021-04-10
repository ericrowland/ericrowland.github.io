(* :Title: Tree Patterns *)

(* :Context: TreePatterns` *)

(* :Author: Eric Rowland *)

(* :Date: {2021, 4, 10} *)

(* :Package Version: 1.09 *)

(* :Mathematica Version: 9 *)

(* :Discussion:
	TreePatterns is a package for studying trees that avoid a given tree pattern.
	Documentation can be found at  https://ericrowland.github.io/packages.html .
*)


BeginPackage["TreePatterns`", {"BinaryTrees`"}]

TreePatterns`Private`$SymbolList = {
	AvoidingWeightEquation,
	Bijections,
	BinaryTreeClassData,
	BinaryTree42Bijection,
	BinaryTree42BijectionInverse,
	BinaryTree43Bijection,
	BinaryTree43BijectionInverse,
	BinaryTree45Bijection,
	BinaryTree45BijectionInverse,
	BinaryTreePatternQ,
	BottomUpReplaceAll,
	FindOverlaps,
	FromTreePattern,
	Leaves,
	MatchingTrees,
	NonMatchingTrees,
	PatternIntersection,
	ProbableAvoidingBijectionQ,
	ProbableAvoidingBijections,
	TopDownReplaceAll,
	TreePattern,
	TreeReplacementRules,
	Weight,
	WeightEquation
}


Unprotect["TreePatterns`*"]

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


AvoidingWeightEquation::usage =
box[AvoidingWeightEquation["t", "f", "x"]] <> " gives an equation satisfied by the weight " <> box["f"] <> " of the set of binary trees that avoid the tree " <> box["t"] <> ", where the weight of a tree is " <> box["x"^"number of vertices"] <> "."

Bijections::usage =
box[Bijections[SubscriptSequence["tree", {1, 2}]]] <> " gives the leaf permutations of " <> box[Subscript["tree", 1]] <> " that produce top-down (and also bottom-up) replacement bijections in which " <> box[Subscript["tree", 1]] <> " and " <> box[Subscript["tree", 2]] <> " are exchanged."

BinaryTreeClassData::usage =
box[BinaryTreeClassData["class", String["property"]]] <> " gives the value of the specified property for an equivalence class of binary trees.\n" <>
box[BinaryTreeClassData["n"]] <> " gives the equivalence classes of " <> box["n"] <> "\[Hyphen]leaf binary trees."

BinaryTree42Bijection::usage =
box[BinaryTree42Bijection["tree"]] <> " gives the binary tuple corresponding to a binary tree avoiding {{___}, {{{___}, {___}}, {___}}}."

BinaryTree42BijectionInverse::usage =
box[BinaryTree42BijectionInverse["list"]] <> " gives the binary tree avoiding {{___}, {{{___}, {___}}, {___}}} corresponding to a binary tuple."

BinaryTree43Bijection::usage =
box[BinaryTree43Bijection["tree"]] <> " gives the binary tuple corresponding to a binary tree avoiding {{{___}, {___}}, {{___}, {___}}}."

BinaryTree43BijectionInverse::usage =
box[BinaryTree43BijectionInverse["list"]] <> " gives the binary tree avoiding {{{___}, {___}}, {{___}, {___}}} corresponding to a binary tuple."

BinaryTree45Bijection::usage =
box[BinaryTree45Bijection["tree"]] <> " gives the Motzkin path corresponding to a binary tree avoiding {{{{___}, {___}}, {___}}, {___}}."

BinaryTree45BijectionInverse::usage =
box[BinaryTree45BijectionInverse["motzkinpath"]] <> " gives the binary tree avoiding {{{{___}, {___}}, {___}}, {___}} corresponding to a Motzkin path on " <> box[{-1, 0, 1}] <> "."

BinaryTreePatternQ::usage =
box[BinaryTreePatternQ["expr"]] <> " yields True if " <> box["expr"] <> " is a binary tree pattern, and False otherwise."

BottomUpReplaceAll::usage =
box[BottomUpReplaceAll["expr", "rules"]] <> " applies a rule or list of rules in an attempt to transform each subpart of " <> box["expr"] <> " up from the bottom."

FindOverlaps::usage =
box[FindOverlaps[SubscriptSequence["p", {1, 2}]]] <> " gives the positions of all sub\[Hyphen]patterns in " <> box[Subscript["p", 1]] <> " that have a non\[Hyphen]full intersection with tree pattern " <> box[Subscript["p", 2]] <> ".
In other words, it finds the places in " <> box[Subscript["p", 1]] <> " where " <> box[Subscript["p", 2]] <> " can be hung."

FromTreePattern::usage =
box[FromTreePattern["treepattern"]] <> " forms a tree by replacing each leaf {__} or {___} of " <> box["treepattern"] <> " by {}."

Leaves::usage =
"Leaves is an option for FindOverlaps that specifies whether to allow matches at the leaves."

MatchingTrees::usage =
box[MatchingTrees["treepattern"]] <> " gives a list of tree patterns such that every tree matching " <> box["treepattern"] <> " matches precisely one tree pattern in the list."

NonMatchingTrees::usage =
box[NonMatchingTrees["treepattern"]] <> " gives a list of tree patterns such that every tree not matching " <> box["treepattern"] <> " matches precisely one tree pattern in the list."

PatternIntersection::usage =
box[PatternIntersection[SubscriptSequence["p", {1, 2, "..."}]]] <> " gives a pattern which is matched by any expression matching all of the tree patterns " <> box[SubscriptSequence["p", {1, 2, "..."}]] <> "."

ProbableAvoidingBijectionQ::usage =
box[ProbableAvoidingBijectionQ[Subscript["p", 1], Subscript["p", 2], "rules"]] <> " determines whether the bijection given by " <> box["rules"] <> " induces a top-down replacement bijection from trees avoiding " <> box[Subscript["p", 1]] <> " to trees avoiding " <> box[Subscript["p", 2]] <> ", assuming that the patterns are sufficiently shallow that three overlapping patterns in a tree does not cause problems."

ProbableAvoidingBijections::usage =
box[ProbableAvoidingBijections[SubscriptSequence["t", {1, 2}]]] <> " gives a list of the permutations that provide top-down replacement bijections on the set of binary trees and induce bijections from trees avoiding " <> box[Subscript["t", 1]] <> " to trees avoiding " <> box[Subscript["t", 2]] <> ", assuming that the patterns are sufficiently shallow that three overlapping patterns in a tree does not cause problems."

TopDownReplaceAll::usage =
box[TopDownReplaceAll["expr", "rules"]] <> " applies a rule or list of rules in an attempt to transform each subpart of " <> box["expr"] <> " down from the top."

TreePattern::usage =
box[TreePattern["tree"]] <> " forms a tree pattern by replacing each leaf {} of " <> box["tree"] <> " by {___}."

TreeReplacementRules::usage =
box[TreeReplacementRules[Subscript["tree", 1], Subscript["tree", 2], "perm"]] <> " gives a list containing the rule for replacing " <> box[Subscript["tree", 1]] <> " with " <> box[Subscript["tree", 2]] <> " according to the given permutation of leaves, and its inverse."

Weight::usage =
box[Weight["tree", "t", "x"]] <> " computes the weight of a binary tree with respect to the tree " <> box["t"] <> ".\n" <>
box[Weight["tree", SubscriptList["t", {1, 2, "...", "k"}], SubscriptList["x", {1, 2, "...", "k"}]]] <> " computes the weight of a binary tree with respect to several trees."

WeightEquation::usage =
box[WeightEquation["t", "f", "x"]] <> " gives an equation satisfied by the weight " <> box["f"] <> " of the set of binary trees, where the weight of a tree is " <> box["x"[{}]^"number of vertices" "x"["t"]^"number of occurrences of t"] <> ".\n" <>
box[WeightEquation[Subscript["t", 1], Subscript["t", 2], "\[Ellipsis]", Subscript["t", "k"], "f", "x"]] <> " uses the weight function " <> box["x"[{}]^"number of vertices" Product["x"[Subscript["t", "i"]]^("number of occurrences of" Subscript["t", "i"]), {"i", 1, "k"}]] <> "."


(* This loads the Singular interface by Manuel Kauers and Viktor Levandovskyy, if available. *)
$Singular =
	Quiet[Check[
		Block[{CellPrint = List, Print = List}, Needs["Singular`"]]; True,
		False
	]]

ReverseAll[tree_] := ReverseAll /@ Reverse[tree]


(* In the innermost ReplaceAll for the construction of testtree, I'm assuming each tree has at least two vertices. *)
Bijections[tree1_?BinaryTreeQ, tree2_?BinaryTreeQ] /;
	Count[tree1, {}, {0, Infinity}] == Count[tree2, {}, {0, Infinity}] :=
Module[{testtree, i = 1},
	testtree = PatternIntersection @@ ({tree1, tree2} /. {} -> {___}) /. {Verbatim[___]} :> {i++};
	Select[
		Permutations[Range[Count[tree1, {}, {0, Infinity}]]],
		Function[perm,
			With[{rules = TreeReplacementRules[tree1, tree2, perm]},
				Equal @@ (testtree /. # &) /@ rules
			]
		]
	]
]
SyntaxInformation[Bijections] = {"ArgumentsPattern" -> {_, _}}

BinaryTree42Bijection[tree_?BinaryTreeQ /; FreeQ[tree, {{___}, {{{___}, {___}}, {___}}}] && tree != {}] :=
	Flatten[{
		If[tree[[2]] != {}, {1, BinaryTree42Bijection[tree[[2]]]}, {}],
		If[tree[[1]] != {}, {0, BinaryTree42Bijection[tree[[1]]]}, {}]
	}]
SyntaxInformation[BinaryTree42Bijection] = {"ArgumentsPattern" -> {_}}

BinaryTree42BijectionInverse[tuple : {(0 | 1) ...}] :=
Module[{l, r},
	Fold[
		#1 /. If[#2 == 0, {r -> {}, l -> {l, r}}, r -> {{}, r}] &,
		{l, r},
		tuple
	] /. r | l -> {}
]
SyntaxInformation[BinaryTree42BijectionInverse] = {"ArgumentsPattern" -> {_}}

BinaryTree43Bijection[{{}, {}}] = {}
BinaryTree43Bijection[tree_?PathTreeQ /; tree != {}] := FromPathTree[tree]
SyntaxInformation[BinaryTree43Bijection] = {"ArgumentsPattern" -> {_}}

BinaryTree43BijectionInverse[tuple : {(0 | 1) ...}] := PathTree[tuple]
SyntaxInformation[BinaryTree43BijectionInverse] = {"ArgumentsPattern" -> {_}}

BinaryTree45Bijection[tree_?BinaryTreeQ /; FreeQ[tree, {{{{___}, {___}}, {___}}, {___}}]] :=
	ToExpression /@ Characters[StringReplace[
		DyckWord[FromBinaryTree[tree]],
		{"001" -> "1", "01" -> "0", "1" -> "2"}
	]] /. 2 -> -1
SyntaxInformation[BinaryTree45Bijection] = {"ArgumentsPattern" -> {_}}

BinaryTree45BijectionInverse[motzkinpath : {(-1 | 0 | 1) ...} /; MatchQ[Accumulate[motzkinpath], {} | {_?NonNegative ..., 0}]] :=
	BinaryTree[FromDyckWord[StringReplace[
		StringJoin[ToString /@ (motzkinpath /. -1 -> 2)],
		{"1" -> "001", "0" -> "01", "2" -> "1"}
	]]]
SyntaxInformation[BinaryTree45BijectionInverse] = {"ArgumentsPattern" -> {_}}

BinaryTreePatternQ[p_] := MatchQ[p, {} | {Verbatim[__] | Verbatim[___]}] || (MatchQ[p, {_, _}] && And @@ BinaryTreePatternQ /@ p)
SyntaxInformation[BinaryTreePatternQ] = {"ArgumentsPattern" -> {_}}

BottomUpReplaceAll[expr_, rules_] :=
Module[{a, b},
	Map[a, b[expr], {-2}] //.
		h_[body__a] :> a[h @@ (Replace[Sequence @@ #, rules] &) /@ {body}] /.
			a | b -> Identity
]
SyntaxInformation[BottomUpReplaceAll] = {"ArgumentsPattern" -> {_, _}}

FindOverlaps[p1_, p2_, OptionsPattern[]] :=
	Position[p1, _List?(
		(OptionValue[Leaves] || MatchQ[#, {__List}]) && FreeQ[PatternIntersection[p2, #], Null]
	&)]
Options[FindOverlaps] = {Leaves -> False}
SyntaxInformation[FindOverlaps] = {"ArgumentsPattern" -> {_, _, OptionsPattern[]}}

FromTreePattern[treepattern_] :=  treepattern /. {Verbatim[__] | Verbatim[___]} -> {}
SyntaxInformation[FromTreePattern] = {"ArgumentsPattern" -> {_}}

(* This can have only ___ in its trees. *)
MatchingTrees[treepattern_List] :=
Module[{i = 0, t},
	t = treepattern //. {Verbatim[___]} :> ++i;
	(t /. Thread[Range[i] -> #] &) /@ Tuples[{{}, {{___}, {___}}}, i]
]
SyntaxInformation[MatchingTrees] = {"ArgumentsPattern" -> {_}}

(* This can have __ or ___ in its trees. *)
(* currently not in use by any of the algorithms *)
NonMatchingTrees[treepattern_List] :=
Module[{i = 1, t},
	t = treepattern //. List :> i++;
	(t /. (Alternatives @@ #)[___] -> {} /. _Integer -> List &) /@
		DeleteCases[
			RootedSubtrees[1,
				Cases[
					t,
					h_Integer[args___] :> h -> Cases[Head /@ {args}, _Integer],
					{0, Infinity}
				]
			],
			{} | {___, Alternatives @@ Cases[t, n_[Verbatim[___]] :> n, {0, Infinity}], ___}
		]
]
SyntaxInformation[NonMatchingTrees] = {"ArgumentsPattern" -> {_}}

(* Every subexpression I'm dealing with matches either {Verbatim[___]} or {{___},{___}},
   so in this context _ is the same as {___}. *)
SetAttributes[PatternIntersection, {(*Flat, OneIdentity, *)Orderless}]
PatternIntersection[p_] := p
PatternIntersection[{Verbatim[___]}, p_] := p
PatternIntersection[p1 : {_, _}, p2 : {_, _}] := PatternIntersection @@@ Transpose[{p1, p2}]
(* These cases aren't needed for *WeightEquation but are useful in other contexts. *)
PatternIntersection[{}, {}] := {}
PatternIntersection[{}, p_] := Null
SyntaxInformation[PatternIntersection] = {"ArgumentsPattern" -> {_, _.}}

ProbableAvoidingBijectionQ[p1_?BinaryTreePatternQ, p2_?BinaryTreePatternQ, rules_] :=
	And @@ Join[
		(!FreeQ[
			BottomUpReplaceAll[
				FromTreePattern[ReplacePart[p2, {#} -> PatternIntersection[First[Extract[p2, {#}]], p1]]],
				rules
			],
			p1
		] &) /@ FindOverlaps[p2, p1],
		(With[{subtree = PatternIntersection[First[Extract[p1, {#}]], p1]},
			Implies[
				FreeQ[Replace[FromTreePattern[ReplacePart[p1, {#} -> subtree]], rules], p1],
				FreeQ[FromTreePattern[ReplacePart[p1, {#} -> Replace[subtree, rules]]], p2]
			]
		] &) /@ DeleteCases[FindOverlaps[p1, p1], {}]
	]
SyntaxInformation[ProbableAvoidingBijectionQ] = {"ArgumentsPattern" -> {_, _, _}}

ProbableAvoidingBijections[t1_?BinaryTreeQ, t2_?BinaryTreeQ] :=
	Select[
		Bijections[t1, t2],
		ProbableAvoidingBijectionQ[TreePattern[t1], TreePattern[t2], TreeReplacementRules[t1, t2, #]] &
	]
SyntaxInformation[ProbableAvoidingBijections] = {"ArgumentsPattern" -> {_, _}}

(*
This gives all subtrees (as lists of vertices at which to "snip") having the given vertex number as the root.
But it takes a weird input (e.g.,
   RootedSubtrees[1, {2 -> {}, 4 -> {}, 5 -> {}, 3 -> {4, 5}, 1 -> {2, 3}}]
for
   NonMatchingTrees[{{___}, {{___}, {___}}}]
), so I'm not exposing it to the user.
*)
RootedSubtrees[root_Integer?Positive, treerules : {(_Integer -> {___Integer}) ..}] /;
		MemberQ[First /@ treerules, root] :=
	{
		{root},
		Sequence @@ Flatten /@ Tuples[RootedSubtrees[#, treerules] & /@ (root /. treerules)]
	}

TopDownReplaceAll[expr_, rules_] :=
Module[{a},
	a[expr] //. {a[h_[body___]] :> a /@ Replace[h[body], rules], a[atom_?AtomQ] :> atom}
]
SyntaxInformation[TopDownReplaceAll] = {"ArgumentsPattern" -> {_, _}}

TreePattern[tree_] := tree /. {} -> {___}
SyntaxInformation[TreePattern] = {"ArgumentsPattern" -> {_}}

(* In hindsight, these rules should be given in the reverse order, since, as is,
   the second rule is used for top-down replacements and the first rule is used for bottom-up replacements. *)
TreeReplacementRules[tree1_?BinaryTreeQ, tree2_?BinaryTreeQ, perm_List /; Sort[perm] == Range[Length[perm]]] /;
	Count[tree1, {}, {0, Infinity}] == Count[tree2, {}, {0, Infinity}] == Length[perm] :=
Module[{vars, i},
	vars = (Symbol["$" <> ToString[#]] &) /@ Range[Count[tree1, {}, {0, Infinity}]];
	{
		RuleDelayed @@ {
			i = 1; tree1 /. {} :> Pattern[Evaluate[vars[[i++]]], _],
			i = 1; tree2 /. {} :> vars[[perm]][[i++]]
		},
		RuleDelayed @@ {
			i = 1; tree2 /. {} :> Pattern[Evaluate[vars[[perm]][[i++]]], _],
			i = 1; tree1 /. {} :> vars[[i++]]
		}
	}
]
SyntaxInformation[TreeReplacementRules] = {"ArgumentsPattern" -> {_, _, _}}

Weight[tree_?BinaryTreeQ, t_?BinaryTreeQ, var : Except[_List]] :=
	var^Count[tree, t /. {} -> {___}, {0, Infinity}]
Weight[tree_?BinaryTreeQ, trees : {___?BinaryTreeQ}, vars_List] /; Length[trees] == Length[vars] :=
	Times @@ (#1^Count[tree, #2 /. {} -> {___}, {0, Infinity}] &) @@@ Transpose[{vars, trees}]
SyntaxInformation[Weight] = {"ArgumentsPattern" -> {_, _, _}}

AvoidingWeightEquation[{}, f_, _, OptionsPattern[]] :=
	f == 0
AvoidingWeightEquation[tree_?BinaryTreeQ, f_, x_, OptionsPattern[]] :=
Module[{tl, tr, weight, logicrule, vars, eqns, newvars},
	{tl, tr} = tree /. {} -> {___};
	logicrule = weight[{pl_, pr_}] :> weight[{}] (
		weight[pl] weight[pr] - weight[PatternIntersection[pl, tl]] weight[PatternIntersection[pr, tr]]
	);
	vars = {weight[{}], weight[{___}]};
	eqns = {weight[{___}] == weight[{}] + weight[{{___}, {___}}]};
	newvars = {weight[{{___}, {___}}]};
	While[newvars != {},
		eqns = Join[
			eqns,
(* I'm deleting cases of True; is this really necessary?  (Do they still occur?) *)
			DeleteCases[(# == (# /. logicrule) &) /@ newvars, True]
		];
		vars = Join[vars, newvars];
		newvars = Complement[Cases[Last /@ eqns, _weight, Infinity], vars]
	];
	Replace[
		If[OptionValue["Singular"] && $Singular,
			newvars = Unique[ConstantArray["w", Length[vars]]];
			SingularEliminate[
				Subtract @@@ (eqns /. Thread[(Verbatim /@ # &) /@ vars -> newvars]),
				Drop[newvars, 2],
				newvars
			] /. Thread[Take[newvars, 2] -> Take[vars, 2]]
			,
			GroebnerBasis[
				Subtract @@@ eqns,
				vars,
				Drop[vars, 2],
				MonomialOrder -> EliminationOrder
			]
		],
		list : {_} :> First[list] == 0
	] /.
		{weight[{Verbatim[___]}] -> f, weight[{}] -> x}
]
Options[AvoidingWeightEquation] = {"Singular" -> $Singular}
SyntaxInformation[AvoidingWeightEquation] = {"ArgumentsPattern" -> {_, _, _, OptionsPattern[]}}

WeightEquation[tree : Except[{}, _?BinaryTreeQ], f : Except[_List], x_, OptionsPattern[]] :=
Module[{tl, tr, weight, logicrule, vars, eqns, newvars},
	{tl, tr} = tree /. {} -> {___};
	logicrule = weight[{pl_, pr_}] :> weight[{}] (
		weight[pl] weight[pr] + (weight[tree] - 1) weight[PatternIntersection[pl, tl]] weight[PatternIntersection[pr, tr]]
	);
	vars = {weight[{}], weight[tree], weight[{___}]};
	eqns = {weight[{___}] == weight[{}] + weight[{{___}, {___}}]};
	newvars = {weight[{{___}, {___}}]};
	While[newvars != {},
		eqns = Join[
			eqns,
			DeleteCases[(# == (# /. logicrule) &) /@ newvars, True]
		];
		vars = Join[vars, newvars];
		newvars = Complement[Cases[Last /@ eqns, _weight, Infinity], vars]
	];
	Replace[
		If[OptionValue["Singular"] && $Singular,
			newvars = Unique[ConstantArray["w", Length[vars]]];
			SingularEliminate[
				Subtract @@@ (eqns /. Thread[(Verbatim /@ # &) /@ vars -> newvars]),
				Drop[newvars, 3],
				newvars
			] /. Thread[Take[newvars, 3] -> Take[vars, 3]]
			,
			GroebnerBasis[
				Subtract @@@ eqns,
				vars,
				Drop[vars, 3],
				MonomialOrder -> EliminationOrder
			]
		],
		list : {_} :> First[list] == 0
	] /.
		{weight[{Verbatim[___]}] -> f, weight[t_] :> x[t]}
]
WeightEquation[trees___?BinaryTreeQ, f : Except[_List], x_, OptionsPattern[]] :=
Module[
	{
		depth = Depth[{trees}] - 2,
		treepatterns = List @@ (Hold[trees] /. {} -> {___}),
		weight, logicrule, expandrule, variablesrule,
		vars, eqns, newvars
	},
	logicrule = weight[p_List] :> Total[weight /@ MatchingTrees[p]];
	expandrule =
		weight[p_List /;
			!FreeQ[p, BlankNullSequence] && Depth[p /. {Verbatim[___]} -> {}] - 1 >= depth
		] :>
			Times @@ weight /@ p *
				Times @@ (x[# /. {Verbatim[___]} -> {}]^Boole[MatchQ[p, #]] &) /@
					Prepend[treepatterns, {___}];
	variablesrule =
		weight[p_List /; FreeQ[p, BlankNullSequence]] :>
			Weight[p, Prepend[{trees}, {}], x /@ Prepend[{trees}, {}]];
	vars = Prepend[x /@ Prepend[{trees}, {}], weight[{___}]];
	eqns = {weight[{___}] == x[{}] + weight[{{___}, {___}}]};
	newvars = {weight[{{___}, {___}}]};
	While[newvars != {},
		eqns = Join[
			eqns,
			(# == (# /. logicrule /. expandrule /. variablesrule) &) /@ newvars
		];
		vars = Join[vars, newvars];
		newvars = Complement[Cases[Last /@ eqns, _weight, Infinity], vars]
	];
	Replace[
		If[OptionValue["Singular"] && $Singular,
			newvars = Unique[ConstantArray["w", Length[vars]]] (*Thread[Subscript[w, Range[Length[vars]]]]*);
			SingularEliminate[
				Subtract @@@ (eqns /. Thread[(Verbatim /@ # &) /@ vars -> newvars]),
				Drop[newvars, Length[treepatterns] + 2],
				newvars
			] /. Thread[Take[newvars, Length[treepatterns] + 2] -> Take[vars, Length[treepatterns] + 2]]
			,
			GroebnerBasis[
				Subtract @@@ eqns,
				vars,
				Drop[vars, Length[treepatterns] + 2],
				MonomialOrder -> EliminationOrder
			]
		],
		list : {_} :> First[list] == 0
	] /.
		weight[{Verbatim[___]}] -> f
]
Options[WeightEquation] = {"Singular" -> $Singular}
SyntaxInformation[WeightEquation] = {"ArgumentsPattern" -> {_, _, _, OptionsPattern[]}}


BinaryTreeClassData[1] := Thread[{1, Range[1]}]
BinaryTreeClassData[2] := Thread[{2, Range[1]}]
BinaryTreeClassData[3] := Thread[{3, Range[1]}]
BinaryTreeClassData[4] := Thread[{4, Range[2]}]
BinaryTreeClassData[5] := Thread[{5, Range[3]}]
BinaryTreeClassData[6] := Thread[{6, Range[7]}]
BinaryTreeClassData[7] := Thread[{7, Range[15]}]
BinaryTreeClassData[8] := Thread[{8, Range[43]}]
$BinaryTreeClasses = Join @@ BinaryTreeClassData /@ Range[1, 8]
classQ[class_] := MemberQ[$BinaryTreeClasses, class]
BinaryTreeClassData[All] := $BinaryTreeClasses
BinaryTreeClassData[] := BinaryTreeClassData[All]
BinaryTreeClassData[class : (_?classQ) : {1, 1}, "Properties"] :=
	{
		"AvoidingSequenceNumber",
		"AvoidingWeightEquation",
		"EquivalenceGraph",
		"Indices",
		"Members",
		"ProbableAvoidingBijections",
		"StatisticIdentifier",
		"WeightEquation"
	}
BinaryTreeClassData[{1, 1}, "Indices"] := {1}
BinaryTreeClassData[{2, 1}, "Indices"] := {1}
BinaryTreeClassData[{3, 1}, "Indices"] := {1, 2}
BinaryTreeClassData[{4, 1}, "Indices"] := {1, 5}
BinaryTreeClassData[{4, 2}, "Indices"] := {2, 3, 4}
BinaryTreeClassData[{5, 1}, "Indices"] := {1, 14}
BinaryTreeClassData[{5, 2}, "Indices"] := {2, 3, 4, 6, 7, 8, 9, 11, 12, 13}
BinaryTreeClassData[{5, 3}, "Indices"] := {5, 10}
BinaryTreeClassData[{6, 1}, "Indices"] := {1, 42}
BinaryTreeClassData[{6, 2}, "Indices"] := {2, 3, 6, 15, 28, 37, 40, 41}
BinaryTreeClassData[{6, 3}, "Indices"] := {4, 8, 10, 18, 19, 20, 21, 22, 23, 24, 25, 33, 35, 39}
BinaryTreeClassData[{6, 4}, "Indices"] := {5, 9, 12, 13, 30, 31, 34, 38}
BinaryTreeClassData[{6, 5}, "Indices"] := {7, 11, 17, 26, 32, 36}
BinaryTreeClassData[{6, 6}, "Indices"] := {14, 29}
BinaryTreeClassData[{6, 7}, "Indices"] := {16, 27}
BinaryTreeClassData[{7, 1}, "Indices"] := {1, 132}
BinaryTreeClassData[{7, 2}, "Indices"] := {2, 3, 6, 15, 43, 90, 118, 127, 130, 131}
BinaryTreeClassData[{7, 3}, "Indices"] := {4, 8, 10, 20, 24, 53, 57, 60, 62, 66, 67, 70, 75, 76, 80, 109, 113, 123, 125, 129}
BinaryTreeClassData[{7, 4}, "Indices"] := {5, 9, 22, 112, 124, 128}
BinaryTreeClassData[{7, 5}, "Indices"] := {7, 17, 32, 48, 49, 84, 85, 101, 116, 126}
BinaryTreeClassData[{7, 6}, "Indices"] := {11, 12, 13, 26, 27, 34, 36, 38, 95, 97, 99, 106, 107, 120, 121, 122}
BinaryTreeClassData[{7, 7}, "Indices"] := {14, 28, 37, 40, 41, 92, 93, 96, 105, 119}
BinaryTreeClassData[{7, 8}, "Indices"] := {16, 45, 88, 117}
BinaryTreeClassData[{7, 9}, "Indices"] := {18, 21, 25, 30, 31, 50, 51, 54, 59, 64, 71, 72, 79, 82, 83, 102, 103, 108, 111, 115}
BinaryTreeClassData[{7, 10}, "Indices"] := {19, 23, 33, 35, 39, 94, 98, 100, 110, 114}
BinaryTreeClassData[{7, 11}, "Indices"] := {29, 55, 56, 77, 78, 104}
BinaryTreeClassData[{7, 12}, "Indices"] := {42, 91}
BinaryTreeClassData[{7, 13}, "Indices"] := {44, 89}
BinaryTreeClassData[{7, 14}, "Indices"] := {46, 47, 58, 63, 73, 74, 86, 87}
BinaryTreeClassData[{7, 15}, "Indices"] := {52, 61, 65, 68, 69, 81}
BinaryTreeClassData[{8, 1}, "Indices"] := {1, 429}
BinaryTreeClassData[{8, 2}, "Indices"] := {2, 3, 6, 15, 43, 133, 297, 387, 415, 424, 427, 428}
BinaryTreeClassData[{8, 3}, "Indices"] := {4, 8, 20, 57, 175, 189, 254, 255, 373, 410, 422, 426}
BinaryTreeClassData[{8, 4}, "Indices"] := {5, 9, 22, 62, 372, 409, 421, 425}
BinaryTreeClassData[{8, 5}, "Indices"] := {7, 17, 48, 147, 283, 382, 413, 423}
BinaryTreeClassData[{8, 6}, "Indices"] := {10, 24, 29, 67, 77, 185, 202, 203, 211, 223, 227, 228, 235, 353, 363, 401, 406, 420}
BinaryTreeClassData[{8, 7}, "Indices"] := {11, 12, 13, 25, 26, 27, 31, 34, 38, 71, 73, 82, 86, 344, 348, 360, 361, 392, 396, 399, 403, 404, 405, 417, 418, 419}
BinaryTreeClassData[{8, 8}, "Indices"] := {14, 28, 75, 359, 402, 416}
BinaryTreeClassData[{8, 9}, "Indices"] := {16, 45, 138, 292, 385, 414}
BinaryTreeClassData[{8, 10}, "Indices"] := {18, 21, 30, 50, 59, 60, 79, 80, 94, 98, 100, 150, 151, 152, 153, 154, 155, 167, 180, 181, 182, 194, 195, 197, 238, 241, 242, 243, 244, 245, 263, 275, 276, 277, 278, 279, 280, 330, 332, 336, 350, 351, 367, 369, 380, 400, 408, 412}
BinaryTreeClassData[{8, 11}, "Indices"] := {19, 23, 51, 64, 102, 108, 322, 328, 368, 379, 407, 411}
BinaryTreeClassData[{8, 12}, "Indices"] := {32, 36, 84, 105, 110, 114, 119, 311, 316, 320, 325, 346, 394, 398}
BinaryTreeClassData[{8, 13}, "Indices"] := {33, 35, 37, 39, 40, 41, 85, 88, 89, 112, 116, 117, 124, 126, 128, 302, 304, 306, 313, 314, 319, 341, 342, 345, 389, 390, 391, 393, 395, 397}
BinaryTreeClassData[{8, 14}, "Indices"] := {42, 90, 118, 127, 130, 131, 299, 300, 303, 312, 340, 388}
BinaryTreeClassData[{8, 15}, "Indices"] := {44, 135, 295, 386}
BinaryTreeClassData[{8, 16}, "Indices"] := {46, 58, 140, 141, 177, 191, 250, 251, 289, 290, 371, 384}
BinaryTreeClassData[{8, 17}, "Indices"] := {47, 63, 370, 383}
BinaryTreeClassData[{8, 18}, "Indices"] := {49, 101, 149, 281, 329, 381}
BinaryTreeClassData[{8, 19}, "Indices"] := {52, 68, 69, 78, 156, 157, 163, 186, 200, 205, 210, 213, 216, 217, 225, 232, 233, 267, 273, 274, 352, 358, 362, 378}
BinaryTreeClassData[{8, 20}, "Indices"] := {53, 70, 97, 158, 215, 272, 333, 357, 377}
BinaryTreeClassData[{8, 21}, "Indices"] := {54, 55, 61, 65, 72, 74, 81, 83, 87, 95, 99, 103, 106, 107, 111, 115, 120, 121, 122, 308, 309, 310, 315, 318, 323, 324, 327, 331, 335, 343, 347, 349, 355, 356, 365, 366, 375, 376}
BinaryTreeClassData[{8, 22}, "Indices"] := {56, 76, 104, 113, 125, 129, 301, 305, 317, 326, 354, 374}
BinaryTreeClassData[{8, 23}, "Indices"] := {66, 109, 123, 307, 321, 364}
BinaryTreeClassData[{8, 24}, "Indices"] := {91, 173, 174, 256, 257, 339}
BinaryTreeClassData[{8, 25}, "Indices"] := {92, 93, 96, 159, 160, 168, 169, 172, 258, 261, 262, 270, 271, 334, 337, 338}
BinaryTreeClassData[{8, 26}, "Indices"] := {132, 298}
BinaryTreeClassData[{8, 27}, "Indices"] := {134, 296}
BinaryTreeClassData[{8, 28}, "Indices"] := {136, 137, 176, 190, 252, 253, 293, 294}
BinaryTreeClassData[{8, 29}, "Indices"] := {139, 148, 282, 291}
BinaryTreeClassData[{8, 30}, "Indices"] := {142, 204, 218, 222, 224, 288}
(* Originally, binary tree 219 was incorrectly reported to be in its own class;
   in fact the polynomial I computed for its avoiding generating function factors. *)
BinaryTreeClassData[{8, 31}, "Indices"] := {143, 198, 207, 209, 219, 221, 236, 287}
BinaryTreeClassData[{8, 32}, "Indices"] := {144, 214, 220, 286}
BinaryTreeClassData[{8, 33}, "Indices"] := {145, 146, 284, 285}
BinaryTreeClassData[{8, 34}, "Indices"] := {161, 188, 229, 269}
BinaryTreeClassData[{8, 35}, "Indices"] := {162, 184, 187, 199, 206, 208, 212, 226, 231, 234, 237, 268}
BinaryTreeClassData[{8, 36}, "Indices"] := {164, 266}
BinaryTreeClassData[{8, 37}, "Indices"] := {165, 265}
BinaryTreeClassData[{8, 38}, "Indices"] := {166, 183, 196, 239, 240, 264}
BinaryTreeClassData[{8, 39}, "Indices"] := {170, 260}
BinaryTreeClassData[{8, 40}, "Indices"] := {171, 259}
BinaryTreeClassData[{8, 41}, "Indices"] := {178, 193, 246, 249}
BinaryTreeClassData[{8, 42}, "Indices"] := {179, 192, 247, 248}
BinaryTreeClassData[{8, 43}, "Indices"] := {201, 230}
BinaryTreeClassData[class : {n_, _}?classQ, "Members"] := BinaryTrees[n][[BinaryTreeClassData[class, "Indices"]]]
BinaryTreeClassData[{1, 1}, "AvoidingSequenceNumber"] := "A000004"
BinaryTreeClassData[{2, 1}, "AvoidingSequenceNumber"] := "A000007"
BinaryTreeClassData[{3, 1}, "AvoidingSequenceNumber"] := "A000012"
BinaryTreeClassData[{4, 1}, "AvoidingSequenceNumber"] := "A001006"
BinaryTreeClassData[{4, 2}, "AvoidingSequenceNumber"] := "A011782"
BinaryTreeClassData[{5, 1}, "AvoidingSequenceNumber"] := "A036765"
BinaryTreeClassData[{5, 2}, "AvoidingSequenceNumber"] := "A086581"
BinaryTreeClassData[{5, 3}, "AvoidingSequenceNumber"] := "A005773"
BinaryTreeClassData[{6, 1}, "AvoidingSequenceNumber"] := "A036766"
BinaryTreeClassData[{6, 2}, "AvoidingSequenceNumber"] := "A159768"
BinaryTreeClassData[{6, 3}, "AvoidingSequenceNumber"] := "A159769"
BinaryTreeClassData[{6, 4}, "AvoidingSequenceNumber"] := "A159770"
BinaryTreeClassData[{6, 5}, "AvoidingSequenceNumber"] := "A159771"
BinaryTreeClassData[{6, 6}, "AvoidingSequenceNumber"] := "A159772"
BinaryTreeClassData[{6, 7}, "AvoidingSequenceNumber"] := "A159773"
BinaryTreeClassData[_?classQ, "AvoidingSequenceNumber"] := Missing["NotAvailable"]
BinaryTreeClassData[{3, 1}, "StatisticIdentifier"] := "St000083"
BinaryTreeClassData[{4, 1}, "StatisticIdentifier"] := "St000118"
(* St000023 is a Permutations statistic.
BinaryTreeClassData[{4, 2}, "StatisticIdentifier"] := "St000023"
*)
BinaryTreeClassData[{5, 1}, "StatisticIdentifier"] := "St000121"
BinaryTreeClassData[{5, 2}, "StatisticIdentifier"] := "St000122"
BinaryTreeClassData[{5, 3}, "StatisticIdentifier"] := "St000125"
BinaryTreeClassData[{6, 1}, "StatisticIdentifier"] := "St000126"
BinaryTreeClassData[{6, 2}, "StatisticIdentifier"] := "St000127"
BinaryTreeClassData[{6, 3}, "StatisticIdentifier"] := "St000128"
BinaryTreeClassData[{6, 4}, "StatisticIdentifier"] := "St000129"
BinaryTreeClassData[{6, 5}, "StatisticIdentifier"] := "St000130"
BinaryTreeClassData[{6, 6}, "StatisticIdentifier"] := "St000131"
BinaryTreeClassData[{6, 7}, "StatisticIdentifier"] := "St000132"
BinaryTreeClassData[_?classQ, "StatisticIdentifier"] := Missing["NotAvailable"]
BinaryTreeClassData[{1, 1}, "ProbableAvoidingBijections"] := {}
BinaryTreeClassData[{2, 1}, "ProbableAvoidingBijections"] := {}
BinaryTreeClassData[{3, 1}, "ProbableAvoidingBijections"] :=
	{
		{1 -> 2, {{2, 3, 1}}},
		{2 -> 1, {{3, 1, 2}}}
	}
BinaryTreeClassData[{4, 1}, "ProbableAvoidingBijections"] := {}
BinaryTreeClassData[{4, 2}, "ProbableAvoidingBijections"] :=
	{
		{2 -> 3, {{2, 3, 1, 4}}},
		{4 -> 3, {{1, 4, 2, 3}}}
	}
BinaryTreeClassData[{5, 1}, "ProbableAvoidingBijections"] := {}
BinaryTreeClassData[{5, 2}, "ProbableAvoidingBijections"] :=
	{
		{2 -> 3, {{1, 3, 4, 2, 5}}},
		{2 -> 6, {{3, 4, 2, 1, 5}}},
		{3 -> 4, {{1, 2, 4, 5, 3}}},
		{3 -> 6, {{2, 3, 1, 4, 5}}},
		{3 -> 12, {{2, 3, 4, 5, 1}}},
		{4 -> 3, {{1, 2, 5, 3, 4}}},
		{4 -> 8, {{2, 3, 4, 1, 5}}},
		{6 -> 7, {{1, 2, 4, 5, 3}}},
		{6 -> 8, {{3, 4, 5, 1, 2}}},
		{7 -> 6, {{1, 2, 5, 3, 4}}},
		{7 -> 9, {{3, 4, 5, 1, 2}}},
		{8 -> 6, {{4, 5, 1, 2, 3}}},
		{8 -> 9, {{2, 3, 1, 4, 5}}},
		{9 -> 7, {{4, 5, 1, 2, 3}}},
		{9 -> 8, {{3, 1, 2, 4, 5}}},
		{11 -> 7, {{1, 5, 2, 3, 4}}},
		{11 -> 12, {{2, 3, 1, 4, 5}}},
		{12 -> 3, {{5, 1, 2, 3, 4}}},
		{12 -> 9, {{1, 2, 5, 3, 4}}},
		{12 -> 11, {{3, 1, 2, 4, 5}}},
		{13 -> 9, {{1, 5, 4, 2, 3}}},
		{13 -> 12, {{1, 4, 2, 3, 5}}}
	}
BinaryTreeClassData[{5, 3}, "ProbableAvoidingBijections"] := {}
BinaryTreeClassData[{6, 1}, "ProbableAvoidingBijections"] := {}
BinaryTreeClassData[{6, 2}, "ProbableAvoidingBijections"] :=
	{
		{2 -> 3, {{1, 2, 4, 5, 3, 6}}},
		{2 -> 6, {{1, 4, 5, 3, 2, 6}}},
		{2 -> 15, {{4, 5, 2, 3, 1, 6}, {4, 5, 3, 2, 1, 6}}},
		{3 -> 6, {{1, 3, 4, 2, 5, 6}}},
		{3 -> 15, {{3, 4, 2, 1, 5, 6}}},
		{6 -> 15, {{2, 3, 1, 4, 5, 6}}},
		{37 -> 28, {{1, 2, 3, 6, 4, 5}}},
		{40 -> 28, {{1, 2, 6, 5, 3, 4}}},
		{40 -> 37, {{1, 2, 5, 3, 4, 6}}},
		{41 -> 28, {{1, 6, 4, 5, 2, 3}, {1, 6, 5, 4, 2, 3}}},
		{41 -> 37, {{1, 5, 4, 2, 3, 6}}},
		{41 -> 40, {{1, 4, 2, 3, 5, 6}}}
	}
BinaryTreeClassData[{6, 3}, "ProbableAvoidingBijections"] :=
	{
		{4 -> 8, {{1, 3, 4, 5, 2, 6}}},
		{4 -> 20, {{3, 4, 5, 2, 1, 6}}},
		{8 -> 20, {{2, 3, 4, 1, 5, 6}}},
		{10 -> 8, {{1, 2, 3, 6, 4, 5}}},
		{10 -> 24, {{2, 3, 4, 5, 1, 6}}},
		{18 -> 19, {{1, 2, 4, 5, 3, 6}}},
		{18 -> 21, {{3, 4, 5, 1, 2, 6}}},
		{19 -> 18, {{1, 2, 5, 3, 4, 6}}},
		{19 -> 23, {{3, 4, 5, 1, 2, 6}}},
		{20 -> 21, {{1, 2, 3, 5, 6, 4}}},
		{20 -> 22, {{2, 3, 1, 4, 5, 6}}},
		{20 -> 23, {{2, 3, 1, 5, 6, 4}, {5, 6, 4, 2, 3, 1}}},
		{21 -> 20, {{1, 2, 3, 6, 4, 5}}},
		{21 -> 22, {{4, 5, 6, 1, 2, 3}}},
		{21 -> 23, {{2, 3, 1, 4, 5, 6}}},
		{22 -> 20, {{3, 1, 2, 4, 5, 6}}},
		{22 -> 21, {{4, 5, 6, 1, 2, 3}}},
		{22 -> 23, {{1, 2, 3, 5, 6, 4}}},
		{23 -> 20, {{3, 1, 2, 6, 4, 5}, {6, 4, 5, 3, 1, 2}}},
		{23 -> 21, {{3, 1, 2, 4, 5, 6}}},
		{23 -> 22, {{1, 2, 3, 6, 4, 5}}},
		{24 -> 20, {{1, 5, 6, 2, 3, 4}}},
		{24 -> 25, {{1, 3, 4, 2, 5, 6}}},
		{25 -> 21, {{1, 5, 6, 2, 3, 4}}},
		{25 -> 24, {{1, 4, 2, 3, 5, 6}}},
		{33 -> 19, {{1, 6, 2, 3, 4, 5}}},
		{33 -> 35, {{2, 3, 1, 4, 5, 6}}},
		{35 -> 23, {{1, 2, 6, 3, 4, 5}}},
		{39 -> 23, {{1, 6, 5, 2, 3, 4}}},
		{39 -> 35, {{1, 5, 2, 3, 4, 6}}}
	}
BinaryTreeClassData[{6, 4}, "ProbableAvoidingBijections"] :=
	{
		{5 -> 9, {{1, 3, 4, 5, 2, 6}}},
		{9 -> 12, {{1, 2, 3, 5, 6, 4}}},
		{9 -> 13, {{1, 2, 5, 6, 4, 3}}},
		{12 -> 9, {{1, 2, 3, 6, 4, 5}}},
		{12 -> 13, {{1, 2, 4, 5, 3, 6}}},
		{13 -> 9, {{1, 2, 6, 5, 3, 4}}},
		{13 -> 12, {{1, 2, 5, 3, 4, 6}}},
		{30 -> 31, {{1, 3, 4, 2, 5, 6}}},
		{30 -> 34, {{3, 4, 2, 1, 5, 6}}},
		{31 -> 30, {{1, 4, 2, 3, 5, 6}}},
		{31 -> 34, {{2, 3, 1, 4, 5, 6}}},
		{34 -> 30, {{4, 3, 1, 2, 5, 6}}},
		{34 -> 31, {{3, 1, 2, 4, 5, 6}}},
		{38 -> 34, {{1, 5, 2, 3, 4, 6}}}
	}
BinaryTreeClassData[{6, 5}, "ProbableAvoidingBijections"] :=
	{
		{7 -> 11, {{1, 2, 4, 5, 6, 3}}},
		{11 -> 7, {{1, 2, 6, 3, 4, 5}}},
		{17 -> 26, {{3, 4, 5, 6, 1, 2}}},
		{26 -> 17, {{5, 6, 1, 2, 3, 4}}},
		{32 -> 36, {{2, 3, 4, 1, 5, 6}}},
		{36 -> 32, {{4, 1, 2, 3, 5, 6}}}
	}
BinaryTreeClassData[{6, 6}, "ProbableAvoidingBijections"] := {}
BinaryTreeClassData[{6, 7}, "ProbableAvoidingBijections"] := {}
BinaryTreeClassData[{7, 1}, "ProbableAvoidingBijections"] := {}
BinaryTreeClassData[{7, 2}, "ProbableAvoidingBijections"] :=
	{
		{2 -> 3, {{1, 2, 3, 5, 6, 4, 7}}},
		{2 -> 6, {{1, 2, 5, 6, 4, 3, 7}}},
		{2 -> 15, {{1, 5, 6, 3, 4, 2, 7}, {1, 5, 6, 4, 3, 2, 7}}},
		{2 -> 43, {{5, 6, 2, 3, 4, 1, 7}, {5, 6, 2, 4, 3, 1, 7}, {5, 6, 3, 2, 4, 1, 7}, {5, 6, 4, 3, 2, 1, 7}}},
		{3 -> 6, {{1, 2, 4, 5, 3, 6, 7}}},
		{3 -> 15, {{1, 4, 5, 3, 2, 6, 7}}},
		{3 -> 43, {{4, 5, 2, 3, 1, 6, 7}, {4, 5, 3, 2, 1, 6, 7}}},
		{6 -> 15, {{1, 3, 4, 2, 5, 6, 7}}},
		{6 -> 43, {{3, 4, 2, 1, 5, 6, 7}}},
		{15 -> 43, {{2, 3, 1, 4, 5, 6, 7}}},
		{118 -> 90, {{1, 2, 3, 4, 7, 5, 6}}},
		{127 -> 90, {{1, 2, 3, 7, 6, 4, 5}}},
		{127 -> 118, {{1, 2, 3, 6, 4, 5, 7}}},
		{130 -> 90, {{1, 2, 7, 5, 6, 3, 4}, {1, 2, 7, 6, 5, 3, 4}}},
		{130 -> 118, {{1, 2, 6, 5, 3, 4, 7}}},
		{130 -> 127, {{1, 2, 5, 3, 4, 6, 7}}},
		{131 -> 90, {{1, 7, 4, 5, 6, 2, 3}, {1, 7, 4, 6, 5, 2, 3}, {1, 7, 5, 4, 6, 2, 3}, {1, 7, 6, 5, 4, 2, 3}}},
		{131 -> 118, {{1, 6, 4, 5, 2, 3, 7}, {1, 6, 5, 4, 2, 3, 7}}},
		{131 -> 127, {{1, 5, 4, 2, 3, 6, 7}}},
		{131 -> 130, {{1, 4, 2, 3, 5, 6, 7}}}
	}
BinaryTreeClassData[{7, 3}, "ProbableAvoidingBijections"] :=
	{
		{4 -> 8, {{1, 2, 4, 5, 6, 3, 7}}},
		{4 -> 20, {{1, 4, 5, 6, 3, 2, 7}}},
		{4 -> 57, {{4, 5, 6, 2, 3, 1, 7}, {4, 5, 6, 3, 2, 1, 7}}},
		{8 -> 10, {{1, 2, 3, 4, 6, 7, 5}, {1, 2, 4, 3, 6, 7, 5}}},
		{8 -> 20, {{1, 3, 4, 5, 2, 6, 7}}},
		{8 -> 57, {{3, 4, 5, 2, 1, 6, 7}}},
		{10 -> 8, {{1, 2, 3, 4, 7, 5, 6}, {1, 2, 4, 3, 7, 5, 6}}},
		{10 -> 24, {{1, 3, 4, 5, 6, 2, 7}}},
		{10 -> 67, {{3, 4, 5, 6, 2, 1, 7}}},
		{20 -> 24, {{1, 2, 5, 6, 7, 3, 4}}},
		{20 -> 57, {{2, 3, 4, 1, 5, 6, 7}}},
		{24 -> 20, {{1, 2, 6, 7, 3, 4, 5}}},
		{24 -> 67, {{2, 3, 4, 5, 1, 6, 7}}},
		{53 -> 70, {{3, 4, 5, 6, 1, 2, 7}}},
		{57 -> 60, {{1, 2, 3, 5, 6, 7, 4}}},
		{57 -> 62, {{2, 3, 1, 4, 5, 6, 7}}},
		{57 -> 67, {{4, 5, 6, 7, 1, 2, 3}}},
		{62 -> 57, {{3, 1, 2, 4, 5, 6, 7}}},
		{66 -> 76, {{4, 5, 6, 7, 1, 2, 3}}},
		{67 -> 57, {{5, 6, 7, 1, 2, 3, 4}}},
		{75 -> 76, {{1, 2, 3, 4, 6, 7, 5}}},
		{76 -> 66, {{5, 6, 7, 1, 2, 3, 4}}},
		{76 -> 70, {{4, 1, 2, 3, 5, 6, 7}}},
		{76 -> 75, {{1, 2, 3, 4, 7, 5, 6}}},
		{80 -> 60, {{1, 6, 7, 2, 3, 4, 5}}},
		{109 -> 66, {{1, 2, 7, 3, 4, 5, 6}}},
		{109 -> 113, {{3, 4, 5, 1, 2, 6, 7}}},
		{113 -> 76, {{1, 2, 3, 7, 4, 5, 6}}},
		{113 -> 109, {{4, 5, 1, 2, 3, 6, 7}}},
		{123 -> 66, {{1, 7, 6, 2, 3, 4, 5}}},
		{123 -> 109, {{1, 6, 2, 3, 4, 5, 7}}},
		{123 -> 125, {{2, 3, 1, 4, 5, 6, 7}, {2, 3, 1, 5, 4, 6, 7}}},
		{125 -> 76, {{1, 2, 7, 6, 3, 4, 5}}},
		{125 -> 113, {{1, 2, 6, 3, 4, 5, 7}}},
		{125 -> 123, {{3, 1, 2, 4, 5, 6, 7}, {3, 1, 2, 5, 4, 6, 7}}},
		{129 -> 76, {{1, 7, 5, 6, 2, 3, 4}, {1, 7, 6, 5, 2, 3, 4}}},
		{129 -> 113, {{1, 6, 5, 2, 3, 4, 7}}},
		{129 -> 125, {{1, 5, 2, 3, 4, 6, 7}}}
	}
BinaryTreeClassData[{7, 4}, "ProbableAvoidingBijections"] :=
	{
		{5 -> 9, {{1, 2, 4, 5, 6, 3, 7}}},
		{5 -> 22, {{1, 4, 5, 6, 3, 2, 7}}},
		{9 -> 22, {{1, 3, 4, 5, 2, 6, 7}}},
		{124 -> 112, {{1, 2, 6, 3, 4, 5, 7}}},
		{128 -> 112, {{1, 6, 5, 2, 3, 4, 7}}},
		{128 -> 124, {{1, 5, 2, 3, 4, 6, 7}}}
	}
BinaryTreeClassData[{7, 5}, "ProbableAvoidingBijections"] :=
	{
		{48 -> 49, {{1, 2, 3, 4, 6, 7, 5}, {3, 4, 1, 2, 6, 7, 5}}},
		{49 -> 48, {{1, 2, 3, 4, 7, 5, 6}, {3, 4, 1, 2, 7, 5, 6}}},
		{84 -> 85, {{2, 3, 1, 4, 5, 6, 7}, {2, 3, 1, 6, 7, 4, 5}}},
		{85 -> 84, {{3, 1, 2, 4, 5, 6, 7}, {3, 1, 2, 6, 7, 4, 5}}}
	}
BinaryTreeClassData[{7, 6}, "ProbableAvoidingBijections"] :=
	{
		{11 -> 12, {{1, 2, 4, 5, 3, 6, 7}, {1, 2, 4, 5, 3, 7, 6}}},
		{12 -> 11, {{1, 2, 5, 3, 4, 6, 7}, {1, 2, 5, 3, 4, 7, 6}}},
		{12 -> 13, {{1, 2, 3, 5, 6, 4, 7}}},
		{12 -> 26, {{1, 3, 4, 5, 6, 2, 7}}},
		{13 -> 12, {{1, 2, 3, 6, 4, 5, 7}}},
		{13 -> 27, {{1, 3, 4, 5, 6, 2, 7}}},
		{26 -> 27, {{1, 2, 4, 5, 3, 6, 7}}},
		{26 -> 36, {{1, 2, 6, 7, 4, 5, 3}}},
		{27 -> 26, {{1, 2, 5, 3, 4, 6, 7}}},
		{27 -> 36, {{1, 2, 3, 4, 6, 7, 5}}},
		{34 -> 26, {{1, 2, 3, 4, 7, 5, 6}}},
		{34 -> 36, {{1, 2, 5, 6, 4, 3, 7}}},
		{34 -> 38, {{1, 2, 4, 5, 6, 3, 7}}},
		{36 -> 26, {{1, 2, 7, 5, 6, 3, 4}}},
		{36 -> 27, {{1, 2, 3, 4, 7, 5, 6}}},
		{36 -> 34, {{1, 2, 6, 5, 3, 4, 7}}},
		{36 -> 38, {{1, 2, 3, 5, 6, 4, 7}}},
		{38 -> 27, {{1, 2, 3, 7, 6, 4, 5}}},
		{38 -> 34, {{1, 2, 6, 3, 4, 5, 7}}},
		{38 -> 36, {{1, 2, 3, 6, 4, 5, 7}}},
		{95 -> 97, {{1, 3, 4, 2, 5, 6, 7}}},
		{95 -> 99, {{1, 3, 4, 5, 2, 6, 7}}},
		{95 -> 106, {{3, 4, 2, 1, 5, 6, 7}}},
		{97 -> 95, {{1, 4, 2, 3, 5, 6, 7}}},
		{97 -> 99, {{1, 4, 5, 3, 2, 6, 7}}},
		{97 -> 106, {{2, 3, 1, 4, 5, 6, 7}}},
		{97 -> 107, {{4, 5, 2, 3, 1, 6, 7}}},
		{99 -> 95, {{1, 5, 2, 3, 4, 6, 7}}},
		{99 -> 97, {{1, 5, 4, 2, 3, 6, 7}}},
		{99 -> 107, {{2, 3, 1, 4, 5, 6, 7}}},
		{106 -> 97, {{3, 1, 2, 4, 5, 6, 7}}},
		{106 -> 107, {{1, 2, 4, 5, 3, 6, 7}}},
		{107 -> 97, {{5, 3, 4, 1, 2, 6, 7}}},
		{107 -> 106, {{1, 2, 5, 3, 4, 6, 7}}},
		{120 -> 106, {{1, 6, 2, 3, 4, 5, 7}}},
		{120 -> 121, {{1, 3, 4, 2, 5, 6, 7}}},
		{121 -> 107, {{1, 6, 2, 3, 4, 5, 7}}},
		{121 -> 120, {{1, 4, 2, 3, 5, 6, 7}}},
		{121 -> 122, {{1, 2, 4, 5, 3, 6, 7}, {2, 1, 4, 5, 3, 6, 7}}},
		{122 -> 121, {{1, 2, 5, 3, 4, 6, 7}, {2, 1, 5, 3, 4, 6, 7}}}
	}
BinaryTreeClassData[{7, 7}, "ProbableAvoidingBijections"] :=
	{
		{14 -> 28, {{1, 3, 4, 5, 6, 2, 7}}},
		{28 -> 37, {{1, 2, 3, 4, 6, 7, 5}, {1, 2, 4, 3, 6, 7, 5}}},
		{28 -> 40, {{1, 2, 3, 6, 7, 5, 4}, {1, 2, 5, 6, 7, 3, 4}}},
		{28 -> 41, {{1, 2, 6, 7, 4, 5, 3}, {1, 2, 6, 7, 5, 4, 3}}},
		{37 -> 28, {{1, 2, 3, 4, 7, 5, 6}, {1, 2, 4, 3, 7, 5, 6}}},
		{37 -> 40, {{1, 2, 3, 5, 6, 4, 7}, {1, 2, 7, 5, 6, 4, 3}}},
		{37 -> 41, {{1, 2, 5, 6, 4, 3, 7}, {1, 2, 5, 6, 7, 3, 4}}},
		{40 -> 28, {{1, 2, 3, 7, 6, 4, 5}, {1, 2, 6, 7, 3, 4, 5}}},
		{40 -> 37, {{1, 2, 3, 6, 4, 5, 7}, {1, 2, 7, 6, 4, 5, 3}}},
		{40 -> 41, {{1, 2, 4, 5, 3, 6, 7}, {1, 2, 4, 5, 3, 7, 6}}},
		{41 -> 28, {{1, 2, 7, 5, 6, 3, 4}, {1, 2, 7, 6, 5, 3, 4}}},
		{41 -> 37, {{1, 2, 6, 5, 3, 4, 7}, {1, 2, 6, 7, 3, 4, 5}}},
		{41 -> 40, {{1, 2, 5, 3, 4, 6, 7}, {1, 2, 5, 3, 4, 7, 6}}},
		{92 -> 93, {{1, 2, 4, 5, 3, 6, 7}, {2, 1, 4, 5, 3, 6, 7}}},
		{92 -> 96, {{1, 4, 5, 3, 2, 6, 7}, {3, 4, 5, 1, 2, 6, 7}}},
		{92 -> 105, {{4, 5, 2, 3, 1, 6, 7}, {4, 5, 3, 2, 1, 6, 7}}},
		{93 -> 92, {{1, 2, 5, 3, 4, 6, 7}, {2, 1, 5, 3, 4, 6, 7}}},
		{93 -> 96, {{1, 3, 4, 2, 5, 6, 7}, {5, 3, 4, 2, 1, 6, 7}}},
		{93 -> 105, {{3, 4, 2, 1, 5, 6, 7}, {3, 4, 5, 1, 2, 6, 7}}},
		{96 -> 92, {{1, 5, 4, 2, 3, 6, 7}, {4, 5, 1, 2, 3, 6, 7}}},
		{96 -> 93, {{1, 4, 2, 3, 5, 6, 7}, {5, 4, 2, 3, 1, 6, 7}}},
		{96 -> 105, {{2, 3, 1, 4, 5, 6, 7}, {2, 3, 1, 5, 4, 6, 7}}},
		{105 -> 92, {{5, 3, 4, 1, 2, 6, 7}, {5, 4, 3, 1, 2, 6, 7}}},
		{105 -> 93, {{4, 3, 1, 2, 5, 6, 7}, {4, 5, 1, 2, 3, 6, 7}}},
		{105 -> 96, {{3, 1, 2, 4, 5, 6, 7}, {3, 1, 2, 5, 4, 6, 7}}},
		{119 -> 105, {{1, 6, 2, 3, 4, 5, 7}}}
	}
BinaryTreeClassData[{7, 8}, "ProbableAvoidingBijections"] := {}
BinaryTreeClassData[{7, 9}, "ProbableAvoidingBijections"] :=
	{
		{18 -> 21, {{1, 2, 5, 6, 4, 3, 7}, {1, 4, 5, 6, 2, 3, 7}}},
		{21 -> 25, {{1, 2, 5, 6, 7, 3, 4}}},
		{25 -> 21, {{1, 2, 6, 7, 3, 4, 5}}},
		{30 -> 21, {{1, 2, 3, 7, 4, 5, 6}}},
		{30 -> 31, {{1, 2, 4, 5, 3, 6, 7}}},
		{31 -> 25, {{1, 2, 3, 4, 7, 5, 6}, {1, 3, 2, 4, 7, 5, 6}}},
		{31 -> 30, {{1, 2, 5, 3, 4, 6, 7}}},
		{50 -> 51, {{1, 2, 4, 5, 3, 6, 7}}},
		{50 -> 59, {{3, 4, 5, 1, 2, 6, 7}}},
		{51 -> 50, {{1, 2, 5, 3, 4, 6, 7}}},
		{51 -> 54, {{1, 2, 3, 4, 6, 7, 5}}},
		{51 -> 64, {{3, 4, 5, 1, 2, 6, 7}}},
		{54 -> 51, {{1, 2, 3, 4, 7, 5, 6}}},
		{54 -> 72, {{3, 4, 5, 6, 1, 2, 7}}},
		{59 -> 64, {{2, 3, 1, 4, 5, 6, 7}}},
		{59 -> 71, {{4, 5, 6, 7, 1, 2, 3}}},
		{64 -> 59, {{3, 1, 2, 4, 5, 6, 7}}},
		{64 -> 72, {{4, 5, 6, 7, 1, 2, 3}}},
		{71 -> 59, {{5, 6, 7, 1, 2, 3, 4}}},
		{71 -> 72, {{1, 2, 3, 4, 6, 7, 5}}},
		{72 -> 64, {{5, 6, 7, 1, 2, 3, 4}}},
		{72 -> 71, {{1, 2, 3, 4, 7, 5, 6}}},
		{79 -> 59, {{1, 6, 7, 2, 3, 4, 5}}},
		{79 -> 82, {{2, 3, 1, 4, 5, 6, 7}}},
		{82 -> 71, {{1, 2, 6, 7, 3, 4, 5}}},
		{82 -> 79, {{3, 1, 2, 4, 5, 6, 7}}},
		{82 -> 83, {{1, 2, 4, 5, 3, 6, 7}}},
		{83 -> 72, {{1, 2, 6, 7, 3, 4, 5}}},
		{83 -> 82, {{1, 2, 5, 3, 4, 6, 7}}},
		{102 -> 103, {{1, 2, 4, 5, 3, 6, 7}}},
		{102 -> 108, {{2, 3, 1, 4, 5, 6, 7}, {2, 3, 1, 4, 6, 5, 7}}},
		{103 -> 102, {{1, 2, 5, 3, 4, 6, 7}}},
		{103 -> 111, {{2, 3, 4, 1, 5, 6, 7}}},
		{108 -> 111, {{3, 4, 5, 1, 2, 6, 7}}},
		{111 -> 108, {{4, 5, 1, 2, 3, 6, 7}}},
		{115 -> 111, {{1, 5, 4, 2, 3, 6, 7}, {1, 5, 6, 2, 3, 4, 7}}}
	}
BinaryTreeClassData[{7, 10}, "ProbableAvoidingBijections"] :=
	{
		{19 -> 23, {{1, 4, 5, 3, 2, 6, 7}, {1, 4, 5, 6, 2, 3, 7}}},
		{19 -> 33, {{1, 2, 4, 5, 6, 7, 3}}},
		{23 -> 35, {{1, 2, 3, 5, 6, 7, 4}}},
		{23 -> 39, {{1, 2, 5, 6, 7, 4, 3}}},
		{33 -> 19, {{1, 2, 7, 3, 4, 5, 6}}},
		{33 -> 35, {{1, 3, 4, 2, 5, 6, 7}, {1, 3, 4, 2, 5, 7, 6}}},
		{35 -> 23, {{1, 2, 3, 7, 4, 5, 6}}},
		{35 -> 39, {{1, 2, 4, 5, 6, 3, 7}}},
		{39 -> 23, {{1, 2, 7, 6, 3, 4, 5}}},
		{39 -> 35, {{1, 2, 6, 3, 4, 5, 7}}},
		{94 -> 98, {{1, 3, 4, 5, 2, 6, 7}}},
		{94 -> 110, {{3, 4, 5, 2, 1, 6, 7}}},
		{98 -> 94, {{1, 5, 2, 3, 4, 6, 7}}},
		{98 -> 110, {{2, 3, 4, 1, 5, 6, 7}}},
		{100 -> 98, {{1, 2, 3, 6, 4, 5, 7}, {2, 1, 3, 6, 4, 5, 7}}},
		{100 -> 114, {{2, 3, 4, 5, 1, 6, 7}}},
		{110 -> 94, {{5, 4, 1, 2, 3, 6, 7}}},
		{110 -> 98, {{4, 1, 2, 3, 5, 6, 7}}},
		{114 -> 100, {{5, 1, 2, 3, 4, 6, 7}}},
		{114 -> 110, {{1, 2, 6, 5, 3, 4, 7}, {1, 5, 6, 2, 3, 4, 7}}}
	}
BinaryTreeClassData[{7, 11}, "ProbableAvoidingBijections"] :=
	{
		{29 -> 77, {{2, 3, 4, 5, 6, 1, 7}}},
		{55 -> 56, {{1, 2, 4, 5, 3, 6, 7}, {1, 2, 4, 5, 3, 7, 6}}},
		{56 -> 55, {{1, 2, 5, 3, 4, 6, 7}, {1, 2, 5, 3, 4, 7, 6}}},
		{77 -> 78, {{1, 2, 4, 5, 3, 6, 7}, {2, 1, 4, 5, 3, 6, 7}}},
		{78 -> 77, {{1, 2, 5, 3, 4, 6, 7}, {2, 1, 5, 3, 4, 6, 7}}},
		{104 -> 56, {{1, 7, 2, 3, 4, 5, 6}}}
	}
BinaryTreeClassData[{7, 12}, "ProbableAvoidingBijections"] := {}
BinaryTreeClassData[{7, 13}, "ProbableAvoidingBijections"] := {}
BinaryTreeClassData[{7, 14}, "ProbableAvoidingBijections"] :=
	{
		{46 -> 47, {{1, 2, 3, 5, 6, 4, 7}}},
		{46 -> 58, {{4, 5, 6, 3, 1, 2, 7}}},
		{47 -> 46, {{1, 2, 3, 6, 4, 5, 7}}},
		{47 -> 63, {{4, 5, 6, 3, 1, 2, 7}}},
		{58 -> 63, {{2, 3, 1, 4, 5, 6, 7}}},
		{63 -> 58, {{3, 1, 2, 4, 5, 6, 7}}},
		{73 -> 74, {{1, 2, 3, 4, 6, 7, 5}}},
		{74 -> 73, {{1, 2, 3, 4, 7, 5, 6}}},
		{86 -> 73, {{1, 6, 7, 5, 2, 3, 4}}},
		{86 -> 87, {{1, 3, 4, 2, 5, 6, 7}}},
		{87 -> 74, {{1, 6, 7, 5, 2, 3, 4}}},
		{87 -> 86, {{1, 4, 2, 3, 5, 6, 7}}}
	}
BinaryTreeClassData[{7, 15}, "ProbableAvoidingBijections"] :=
	{
		{52 -> 68, {{3, 4, 5, 6, 1, 2, 7}}},
		{81 -> 61, {{1, 6, 7, 2, 3, 4, 5}}}
	}
BinaryTreeClassData[_?classQ, "ProbableAvoidingBijections"] := Missing["NotAvailable"]
BinaryTreeClassData[class_?classQ, "EquivalenceGraph", options : OptionsPattern[]] /;
	MatchQ[BinaryTreeClassData[class, "ProbableAvoidingBijections"], _List] :=
With[
	{
		edges = Join[
			Style[# -> RankBinaryTree[ReverseAll[BinaryTrees[First[class]][[#]]]], Directive[Gray, Dashed]] & /@
				BinaryTreeClassData[class, "Indices"],
			First /@ BinaryTreeClassData[class, "ProbableAvoidingBijections"]
		]
	},
	If[Union @@ List @@@ Replace[edges, Style[edge_, _] :> edge, {1}] != BinaryTreeClassData[class, "Indices"],
		Print["Warning: Some trees are not represented in these equivalences."]
	];
	Graph[
		edges,
		options,
		VertexLabels -> "Name"
	]
]
BinaryTreeClassData[_?classQ, "EquivalenceGraph", options : OptionsPattern[]] := Missing["NotAvailable"]
(* for backward compatibility: *)
BinaryTreeClassData[class_?classQ, "EquivalenceGraphImage", options : OptionsPattern[]] :=
	BinaryTreeClassData[class, "EquivalenceGraph", options]
BinaryTreeClassData[{1, 1}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX] \[FormalY]
		- \[FormalF]
		+ \[FormalX] \[FormalY] \[FormalF]^2
		== 0
	]
BinaryTreeClassData[{2, 1}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX]
		- \[FormalF]
		+ \[FormalX] \[FormalY] \[FormalF]^2
		== 0
	]
BinaryTreeClassData[{3, 1}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX]
		+ (-1 + \[FormalX]^2 - \[FormalX]^2 \[FormalY]) \[FormalF]
		+ \[FormalX] \[FormalY] \[FormalF]^2
		== 0
	]
BinaryTreeClassData[{4, 1}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX]
		+ (-1 + \[FormalX]^2 - \[FormalX]^2 \[FormalY]) \[FormalF]
		- \[FormalX] (-\[FormalX]^2 - \[FormalY] + \[FormalX]^2 \[FormalY]) \[FormalF]^2
		== 0
	]
BinaryTreeClassData[{4, 2}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^2 \[FormalY])
		+ (-1 + 2 \[FormalX]^2 - 2 \[FormalX]^2 \[FormalY]) \[FormalF]
		+ \[FormalX] \[FormalY] \[FormalF]^2
		== 0
	]
BinaryTreeClassData[{5, 1}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX]
		+ (-1 + \[FormalX]^2 - \[FormalX]^2 \[FormalY]) \[FormalF]
		- \[FormalX] (-\[FormalX]^2 - \[FormalY] + \[FormalX]^2 \[FormalY]) \[FormalF]^2
		- \[FormalX]^4 (-1 + \[FormalY]) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{5, 2}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^2 \[FormalY])
		+ (-1 + 2 \[FormalX]^2 - \[FormalX]^4 - 2 \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY]) \[FormalF]
		- \[FormalX] (-\[FormalX]^2 - \[FormalY] + \[FormalX]^2 \[FormalY]) \[FormalF]^2
		== 0
	]
BinaryTreeClassData[{5, 3}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		-\[FormalX]^4 (-1 + \[FormalY])
		+ \[FormalX] (1 - 3 \[FormalX]^2 + 3 \[FormalX]^2 \[FormalY]) \[FormalF]
		+ (-1 + 3 \[FormalX]^2 - 3 \[FormalX]^2 \[FormalY]) \[FormalF]^2
		+ \[FormalX] \[FormalY] \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{6, 1}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX]
		+ (-1 + \[FormalX]^2 - \[FormalX]^2 \[FormalY]) \[FormalF]
		- \[FormalX] (-\[FormalX]^2 - \[FormalY] + \[FormalX]^2 \[FormalY]) \[FormalF]^2
		- \[FormalX]^4 (-1 + \[FormalY]) \[FormalF]^3
		- \[FormalX]^5 (-1 + \[FormalY]) \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{6, 2}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^2 \[FormalY])
		+ (-1 + 2 \[FormalX]^2 - \[FormalX]^4 - 2 \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY]) \[FormalF]
		+ \[FormalX] (\[FormalX]^2 - \[FormalX]^4 + \[FormalY] - \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY]) \[FormalF]^2
		- \[FormalX]^4 (-1 + \[FormalY]) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{6, 3}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^2 \[FormalY])
		+ (-1 + 2 \[FormalX]^2 - 2 \[FormalX]^4 - 2 \[FormalX]^2 \[FormalY] + 2 \[FormalX]^4 \[FormalY]) \[FormalF]
		+ \[FormalX] (2 \[FormalX]^2 - \[FormalX]^4 + \[FormalY] - 2 \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY]) \[FormalF]^2
		== 0
	]
BinaryTreeClassData[{6, 4}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		-\[FormalX]^4 (-1 + \[FormalY])
		- \[FormalX] (-1 + 3 \[FormalX]^2 - \[FormalX]^4 - 3 \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY]) \[FormalF]
		+ (-1 + 3 \[FormalX]^2 - 2 \[FormalX]^4 - 3 \[FormalX]^2 \[FormalY] + 2 \[FormalX]^4 \[FormalY]) \[FormalF]^2
		- \[FormalX] (-\[FormalX]^2 - \[FormalY] + \[FormalX]^2 \[FormalY]) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{6, 5}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		-\[FormalX] (-1 + \[FormalX]^2 - \[FormalX]^4 - \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY])
		+ (-1 + 2 \[FormalX]^2 - 3 \[FormalX]^4 - 2 \[FormalX]^2 \[FormalY] + 3 \[FormalX]^4 \[FormalY]) \[FormalF]
		- \[FormalX] (-2 \[FormalX]^2 - \[FormalY] + 2 \[FormalX]^2 \[FormalY]) \[FormalF]^2
		== 0
	]
BinaryTreeClassData[{6, 6}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		-\[FormalX]^5 (-1 + \[FormalY])
		+ 4 \[FormalX]^4 (-1 + \[FormalY]) \[FormalF]
		- \[FormalX] (1 - 6 \[FormalX]^2 + 6 \[FormalX]^2 \[FormalY]) \[FormalF]^2
		+ (1 - 4 \[FormalX]^2 + 4 \[FormalX]^2 \[FormalY]) \[FormalF]^3
		- \[FormalX] \[FormalY] \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{6, 7}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^6 + \[FormalX]^2 \[FormalY] - 2 \[FormalX]^6 \[FormalY] + \[FormalX]^6 \[FormalY]^2)
		+ (-1 + 2 \[FormalX]^2 - \[FormalX]^4 - 3 \[FormalX]^6 + \[FormalX]^8 - 2 \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY] + 6 \[FormalX]^6 \[FormalY] - 2 \[FormalX]^8 \[FormalY] - 3 \[FormalX]^6 \[FormalY]^2 + \[FormalX]^8 \[FormalY]^2) \[FormalF]
		- \[FormalX] (-\[FormalX]^2 - 2 \[FormalX]^4 + 2 \[FormalX]^6 - \[FormalY] + \[FormalX]^2 \[FormalY] + 5 \[FormalX]^4 \[FormalY] - 4 \[FormalX]^6 \[FormalY] - 3 \[FormalX]^4 \[FormalY]^2 + 2 \[FormalX]^6 \[FormalY]^2) \[FormalF]^2
		+ \[FormalX]^4 (-1 + \[FormalY]) (-\[FormalX]^2 - \[FormalY] + \[FormalX]^2 \[FormalY]) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{7, 1}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX]
		+ (-1 + \[FormalX]^2 - \[FormalX]^2 \[FormalY]) \[FormalF]
		- \[FormalX] (-\[FormalX]^2 - \[FormalY] + \[FormalX]^2 \[FormalY]) \[FormalF]^2
		- \[FormalX]^4 (-1 + \[FormalY]) \[FormalF]^3
		- \[FormalX]^5 (-1 + \[FormalY]) \[FormalF]^4
		- \[FormalX]^6 (-1 + \[FormalY]) \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{7, 2}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^2 \[FormalY])
		+ (-1 + 2 \[FormalX]^2 - \[FormalX]^4 - 2 \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY]) \[FormalF]
		+ \[FormalX] (\[FormalX]^2 - \[FormalX]^4 + \[FormalY] - \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY]) \[FormalF]^2
		+ (-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) (-1 + \[FormalY]) \[FormalF]^3
		- \[FormalX]^5 (-1 + \[FormalY]) \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{7, 3}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^2 \[FormalY])
		+ (-1 + 2 \[FormalX]^2 - 2 \[FormalX]^4 - 2 \[FormalX]^2 \[FormalY] + 2 \[FormalX]^4 \[FormalY]) \[FormalF]
		+ \[FormalX] (2 \[FormalX]^2 - 2 \[FormalX]^4 + \[FormalY] - 2 \[FormalX]^2 \[FormalY] + 2 \[FormalX]^4 \[FormalY]) \[FormalF]^2
		+ (-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) (-1 + \[FormalY]) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{7, 4}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		-\[FormalX]^4 (-1 + \[FormalY])
		- \[FormalX] (-1 + 3 \[FormalX]^2 - \[FormalX]^4 - 3 \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY]) \[FormalF]
		+ (-1 + 3 \[FormalX]^2 - 2 \[FormalX]^4 + \[FormalX]^6 - 3 \[FormalX]^2 \[FormalY] + 2 \[FormalX]^4 \[FormalY] - \[FormalX]^6 \[FormalY]) \[FormalF]^2
		+ \[FormalX] (\[FormalX]^2 - 2 \[FormalX]^4 + \[FormalY] - \[FormalX]^2 \[FormalY] + 2 \[FormalX]^4 \[FormalY]) \[FormalF]^3
		- \[FormalX]^4 (-1 + \[FormalY]) \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{7, 5}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		-\[FormalX] (-1 + \[FormalX]^2 - \[FormalX]^4 - \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY])
		+ (-1 + 2 \[FormalX]^2 - 3 \[FormalX]^4 + \[FormalX]^6 - 2 \[FormalX]^2 \[FormalY] + 3 \[FormalX]^4 \[FormalY] - \[FormalX]^6 \[FormalY]) \[FormalF]
		+ \[FormalX] (2 \[FormalX]^2 - 2 \[FormalX]^4 + \[FormalY] - 2 \[FormalX]^2 \[FormalY] + 2 \[FormalX]^4 \[FormalY]) \[FormalF]^2
		- \[FormalX]^4 (-1 + \[FormalY]) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{7, 6}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		-\[FormalX]^4 (-1 + \[FormalY])
		- \[FormalX] (-1 + 3 \[FormalX]^2 - 2 \[FormalX]^4 - 3 \[FormalX]^2 \[FormalY] + 2 \[FormalX]^4 \[FormalY]) \[FormalF]
		+ (-1 + 3 \[FormalX]^2 - 4 \[FormalX]^4 + \[FormalX]^6 - 3 \[FormalX]^2 \[FormalY] + 4 \[FormalX]^4 \[FormalY] - \[FormalX]^6 \[FormalY]) \[FormalF]^2
		+ \[FormalX] (2 \[FormalX]^2 - \[FormalX]^4 + \[FormalY] - 2 \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY]) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{7, 7}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		-\[FormalX]^5 (-1 + \[FormalY])
		- (-2 + \[FormalX]) \[FormalX]^4 (2 + \[FormalX]) (-1 + \[FormalY]) \[FormalF]
		+ \[FormalX] (-1 + 6 \[FormalX]^2 - 3 \[FormalX]^4 - 6 \[FormalX]^2 \[FormalY] + 3 \[FormalX]^4 \[FormalY]) \[FormalF]^2
		+ (1 - 4 \[FormalX]^2 + 3 \[FormalX]^4 + 4 \[FormalX]^2 \[FormalY] - 3 \[FormalX]^4 \[FormalY]) \[FormalF]^3
		+ \[FormalX] (-\[FormalX]^2 - \[FormalY] + \[FormalX]^2 \[FormalY]) \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{7, 8}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		-\[FormalX] (1 - \[FormalX]^4 + \[FormalX]^4 \[FormalY]) (-1 + \[FormalX]^2 - \[FormalX]^4 - \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY])
		+ (-1 + 2 \[FormalX]^2 - \[FormalX]^4 - 2 \[FormalX]^6 + 4 \[FormalX]^8 - 2 \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY] + 5 \[FormalX]^6 \[FormalY] - 8 \[FormalX]^8 \[FormalY] - 3 \[FormalX]^6 \[FormalY]^2 + 4 \[FormalX]^8 \[FormalY]^2) \[FormalF]
		- \[FormalX] (-\[FormalX]^2 + 5 \[FormalX]^6 - \[FormalY] + \[FormalX]^2 \[FormalY] + 3 \[FormalX]^4 \[FormalY] - 10 \[FormalX]^6 \[FormalY] - 3 \[FormalX]^4 \[FormalY]^2 + 5 \[FormalX]^6 \[FormalY]^2) \[FormalF]^2
		+ \[FormalX]^4 (-1 + \[FormalY]) (-1 - 2 \[FormalX]^2 - \[FormalY] + 2 \[FormalX]^2 \[FormalY]) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{7, 9}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		-\[FormalX] (-1 + \[FormalX]^2 - \[FormalX]^4 - \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY])
		+ (-1 + 2 \[FormalX]^2 - 4 \[FormalX]^4 + \[FormalX]^6 - 2 \[FormalX]^2 \[FormalY] + 4 \[FormalX]^4 \[FormalY] - \[FormalX]^6 \[FormalY]) \[FormalF]
		+ \[FormalX] (3 \[FormalX]^2 - 2 \[FormalX]^4 + \[FormalY] - 3 \[FormalX]^2 \[FormalY] + 2 \[FormalX]^4 \[FormalY]) \[FormalF]^2
		== 0
	]
BinaryTreeClassData[{7, 10}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		(-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) (-1 + \[FormalY])
		- \[FormalX] (-1 + 3 \[FormalX]^2 - 4 \[FormalX]^4 - 3 \[FormalX]^2 \[FormalY] + 4 \[FormalX]^4 \[FormalY]) \[FormalF]
		+ (-1 + 3 \[FormalX]^2 - 5 \[FormalX]^4 - 3 \[FormalX]^2 \[FormalY] + 5 \[FormalX]^4 \[FormalY]) \[FormalF]^2
		- \[FormalX] (-2 \[FormalX]^2 - \[FormalY] + 2 \[FormalX]^2 \[FormalY]) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{7, 11}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX]^2 (1 - \[FormalX]^2 + \[FormalX]^2 \[FormalY])
		+ \[FormalX] (-2 + 3 \[FormalX]^2 - 3 \[FormalX]^4 - 3 \[FormalX]^2 \[FormalY] + 3 \[FormalX]^4 \[FormalY]) \[FormalF]
		+ (1 - 2 \[FormalX]^2 + 6 \[FormalX]^4 - 3 \[FormalX]^6 + 3 \[FormalX]^2 \[FormalY] - 6 \[FormalX]^4 \[FormalY] + 3 \[FormalX]^6 \[FormalY]) \[FormalF]^2
		+ \[FormalX] (-3 \[FormalX]^2 + 3 \[FormalX]^4 - \[FormalX]^6 - \[FormalY] + 3 \[FormalX]^2 \[FormalY] - 3 \[FormalX]^4 \[FormalY] + \[FormalX]^6 \[FormalY]) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{7, 12}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		-\[FormalX]^6 (-1 + \[FormalY])
		+ 5 \[FormalX]^5 (-1 + \[FormalY]) \[FormalF]
		- 10 \[FormalX]^4 (-1 + \[FormalY]) \[FormalF]^2
		+ \[FormalX] (1 - 10 \[FormalX]^2 + 10 \[FormalX]^2 \[FormalY]) \[FormalF]^3
		+ (-1 + 5 \[FormalX]^2 - 5 \[FormalX]^2 \[FormalY]) \[FormalF]^4
		+ \[FormalX] \[FormalY] \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{7, 13}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		-\[FormalX] (-1 + \[FormalX]^2 - \[FormalX]^4 + \[FormalX]^6 - \[FormalX]^8 + \[FormalX]^10 + \[FormalX]^14 - \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY] - 2 \[FormalX]^6 \[FormalY] + 3 \[FormalX]^8 \[FormalY] - 3 \[FormalX]^10 \[FormalY] - 4 \[FormalX]^14 \[FormalY] + \[FormalX]^6 \[FormalY]^2 - 3 \[FormalX]^8 \[FormalY]^2 + 3 \[FormalX]^10 \[FormalY]^2 + 6 \[FormalX]^14 \[FormalY]^2 + \[FormalX]^8 \[FormalY]^3 - \[FormalX]^10 \[FormalY]^3 - 4 \[FormalX]^14 \[FormalY]^3 + \[FormalX]^14 \[FormalY]^4)
		+ (-1 + 2 \[FormalX]^2 - 3 \[FormalX]^4 + 3 \[FormalX]^6 - 3 \[FormalX]^8 + 5 \[FormalX]^10 + 5 \[FormalX]^14 - \[FormalX]^16 - 2 \[FormalX]^2 \[FormalY] + 3 \[FormalX]^4 \[FormalY] - 6 \[FormalX]^6 \[FormalY] + 10 \[FormalX]^8 \[FormalY] - 15 \[FormalX]^10 \[FormalY] - 20 \[FormalX]^14 \[FormalY] + 4 \[FormalX]^16 \[FormalY] + 3 \[FormalX]^6 \[FormalY]^2 - 11 \[FormalX]^8 \[FormalY]^2 + 15 \[FormalX]^10 \[FormalY]^2 + 30 \[FormalX]^14 \[FormalY]^2 - 6 \[FormalX]^16 \[FormalY]^2 + 4 \[FormalX]^8 \[FormalY]^3 - 5 \[FormalX]^10 \[FormalY]^3 - 20 \[FormalX]^14 \[FormalY]^3 + 4 \[FormalX]^16 \[FormalY]^3 + 5 \[FormalX]^14 \[FormalY]^4 - \[FormalX]^16 \[FormalY]^4) \[FormalF]
		+ \[FormalX] (2 \[FormalX]^2 - 3 \[FormalX]^4 + 2 \[FormalX]^6 - 8 \[FormalX]^8 - 9 \[FormalX]^12 + 4 \[FormalX]^14 + \[FormalY] - 2 \[FormalX]^2 \[FormalY] + 6 \[FormalX]^4 \[FormalY] - 10 \[FormalX]^6 \[FormalY] + 25 \[FormalX]^8 \[FormalY] + 37 \[FormalX]^12 \[FormalY] - 16 \[FormalX]^14 \[FormalY] - 3 \[FormalX]^4 \[FormalY]^2 + 14 \[FormalX]^6 \[FormalY]^2 - 26 \[FormalX]^8 \[FormalY]^2 - 57 \[FormalX]^12 \[FormalY]^2 + 24 \[FormalX]^14 \[FormalY]^2 - 6 \[FormalX]^6 \[FormalY]^3 + 9 \[FormalX]^8 \[FormalY]^3 + 39 \[FormalX]^12 \[FormalY]^3 - 16 \[FormalX]^14 \[FormalY]^3 - 10 \[FormalX]^12 \[FormalY]^4 + 4 \[FormalX]^14 \[FormalY]^4) \[FormalF]^2
		- \[FormalX]^4 (-1 + \[FormalY]) (1 + 5 \[FormalX]^4 + 7 \[FormalX]^8 - 6 \[FormalX]^10 - \[FormalY] + 3 \[FormalX]^2 \[FormalY] - 12 \[FormalX]^4 \[FormalY] - 24 \[FormalX]^8 \[FormalY] + 18 \[FormalX]^10 \[FormalY] - 4 \[FormalX]^2 \[FormalY]^2 + 7 \[FormalX]^4 \[FormalY]^2 + 27 \[FormalX]^8 \[FormalY]^2 - 18 \[FormalX]^10 \[FormalY]^2 - 10 \[FormalX]^8 \[FormalY]^3 + 6 \[FormalX]^10 \[FormalY]^3) \[FormalF]^3
		+ \[FormalX]^5 (-1 + \[FormalY]) (\[FormalX]^2 + 2 \[FormalX]^6 - 4 \[FormalX]^8 - 3 \[FormalX]^2 \[FormalY] - 9 \[FormalX]^6 \[FormalY] + 12 \[FormalX]^8 \[FormalY] - \[FormalY]^2 + 2 \[FormalX]^2 \[FormalY]^2 + 12 \[FormalX]^6 \[FormalY]^2 - 12 \[FormalX]^8 \[FormalY]^2 - 5 \[FormalX]^6 \[FormalY]^3 + 4 \[FormalX]^8 \[FormalY]^3) \[FormalF]^4
		- \[FormalX]^10 (-1 + \[FormalY])^3 (-\[FormalX]^2 - \[FormalY] + \[FormalX]^2 \[FormalY]) \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{7, 14}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^6 + \[FormalX]^2 \[FormalY] - 2 \[FormalX]^6 \[FormalY] + \[FormalX]^6 \[FormalY]^2)
		+ (-1 + 2 \[FormalX]^2 - 2 \[FormalX]^4 - 3 \[FormalX]^6 + 3 \[FormalX]^8 - 2 \[FormalX]^2 \[FormalY] + 2 \[FormalX]^4 \[FormalY] + 6 \[FormalX]^6 \[FormalY] - 6 \[FormalX]^8 \[FormalY] - 3 \[FormalX]^6 \[FormalY]^2 + 3 \[FormalX]^8 \[FormalY]^2) \[FormalF]
		+ \[FormalX] (2 \[FormalX]^2 + \[FormalX]^4 - 6 \[FormalX]^6 + 3 \[FormalX]^8 + \[FormalY] - 2 \[FormalX]^2 \[FormalY] - 4 \[FormalX]^4 \[FormalY] + 12 \[FormalX]^6 \[FormalY] - 6 \[FormalX]^8 \[FormalY] + 3 \[FormalX]^4 \[FormalY]^2 - 6 \[FormalX]^6 \[FormalY]^2 + 3 \[FormalX]^8 \[FormalY]^2) \[FormalF]^2
		+ (-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) (-1 + \[FormalY]) (2 \[FormalX]^2 - \[FormalX]^4 + \[FormalY] - 2 \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY]) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{7, 15}, "WeightEquation"] :=
	Function[{\[FormalF], \[FormalX], \[FormalY]},
		-\[FormalX] (-1 + \[FormalX]^2 - \[FormalX]^4 - \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY])
		+ (-1 + 2 \[FormalX]^2 - 4 \[FormalX]^4 - 2 \[FormalX]^2 \[FormalY] + 4 \[FormalX]^4 \[FormalY]) \[FormalF]
		+ \[FormalX] (3 \[FormalX]^2 - \[FormalX]^4 + \[FormalY] - 3 \[FormalX]^2 \[FormalY] + \[FormalX]^4 \[FormalY]) \[FormalF]^2
		+ \[FormalX]^6 (-1 + \[FormalY]) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{8, 1}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]
		+ (-1 + \[FormalX]) (1 + \[FormalX]) \[FormalF]
		+ \[FormalX]^3 \[FormalF]^2
		+ \[FormalX]^4 \[FormalF]^3
		+ \[FormalX]^5 \[FormalF]^4
		+ \[FormalX]^6 \[FormalF]^5
		+ \[FormalX]^7 \[FormalF]^6
		== 0
	]
BinaryTreeClassData[{8, 2}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX] (1 + \[FormalX])
		- (-1 + \[FormalX])^2 (1 + \[FormalX])^2 \[FormalF]
		- (-1 + \[FormalX]) \[FormalX]^3 (1 + \[FormalX]) \[FormalF]^2
		- (-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) \[FormalF]^3
		- (-1 + \[FormalX]) \[FormalX]^5 (1 + \[FormalX]) \[FormalF]^4
		+ \[FormalX]^6 \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{8, 3}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX] (1 + \[FormalX])
		+ (-1 + 2 \[FormalX]^2 - 2 \[FormalX]^4) \[FormalF]
		- 2 (-1 + \[FormalX]) \[FormalX]^3 (1 + \[FormalX]) \[FormalF]^2
		- \[FormalX]^4 (-1 + 2 \[FormalX]^2) \[FormalF]^3
		- (-1 + \[FormalX]) \[FormalX]^5 (1 + \[FormalX]) \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 4}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^4
		+ \[FormalX] (-1 - \[FormalX] + \[FormalX]^2) (-1 + \[FormalX] + \[FormalX]^2) \[FormalF]
		+ (-1 + 3 \[FormalX]^2 - 2 \[FormalX]^4 + \[FormalX]^6) \[FormalF]^2
		+ (-1 + \[FormalX])^2 \[FormalX]^3 (1 + \[FormalX])^2 \[FormalF]^3
		- \[FormalX]^4 (-1 + 2 \[FormalX]^2) \[FormalF]^4
		+ \[FormalX]^5 \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{8, 5}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^4)
		+ (-1 + 2 \[FormalX]^2 - 3 \[FormalX]^4 + \[FormalX]^6) \[FormalF]
		+ \[FormalX]^3 (2 - 2 \[FormalX]^2 + \[FormalX]^4) \[FormalF]^2
		- \[FormalX]^4 (-1 + 2 \[FormalX]^2) \[FormalF]^3
		+ \[FormalX]^5 \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 6}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX] (1 + \[FormalX])
		+ (-1 + 2 \[FormalX]^2 - 2 \[FormalX]^4) \[FormalF]
		- \[FormalX]^3 (-2 + 3 \[FormalX]^2) \[FormalF]^2
		- 2 (-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) \[FormalF]^3
		- \[FormalX]^7 \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 7}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^4
		+ (-1 + \[FormalX]) \[FormalX] (1 + \[FormalX]) (-1 + 2 \[FormalX]^2) \[FormalF]
		+ (-1 + \[FormalX]) (1 + \[FormalX]) (1 - 2 \[FormalX]^2 + 2 \[FormalX]^4) \[FormalF]^2
		+ (-1 + \[FormalX]) \[FormalX]^3 (1 + \[FormalX]) (-2 + \[FormalX]^2) \[FormalF]^3
		- (-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 8}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^5
		+ (-2 + \[FormalX]) \[FormalX]^4 (2 + \[FormalX]) \[FormalF]
		+ \[FormalX] (-1 + 6 \[FormalX]^2 - 3 \[FormalX]^4 + \[FormalX]^6) \[FormalF]^2
		+ (1 - 4 \[FormalX]^2 + 3 \[FormalX]^4 - 3 \[FormalX]^6) \[FormalF]^3
		+ \[FormalX]^3 (-1 + 3 \[FormalX]^2) \[FormalF]^4
		- \[FormalX]^4 \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{8, 9}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX] (1 + \[FormalX]) (1 + \[FormalX]^2) (1 - \[FormalX]^2 + \[FormalX]^4)
		+ (-1 + 2 \[FormalX]^2 - \[FormalX]^4 - 2 \[FormalX]^6 + 4 \[FormalX]^8 - \[FormalX]^10) \[FormalF]
		+ (-1 + \[FormalX]) \[FormalX]^3 (1 + \[FormalX]) (-1 - \[FormalX]^2 + 3 \[FormalX]^4) \[FormalF]^2
		- \[FormalX]^4 (-1 + 3 \[FormalX]^4) \[FormalF]^3
		+ \[FormalX]^5 (1 + \[FormalX]^2) \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 10}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^4)
		+ (-1 + 2 \[FormalX]^2 - 4 \[FormalX]^4 + 2 \[FormalX]^6) \[FormalF]
		+ (-1 + \[FormalX]) \[FormalX]^3 (1 + \[FormalX]) (-3 + \[FormalX]^2) \[FormalF]^2
		- (-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{8, 11}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX])
		- \[FormalX] (-1 + 3 \[FormalX]^2 - 4 \[FormalX]^4 + \[FormalX]^6) \[FormalF]
		+ (-1 + \[FormalX]) (1 + \[FormalX]) (1 - 2 \[FormalX]^2 + 3 \[FormalX]^4) \[FormalF]^2
		- \[FormalX]^3 (-2 + 3 \[FormalX]^2) \[FormalF]^3
		+ \[FormalX]^4 \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 12}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^4
		+ \[FormalX] (1 - 3 \[FormalX]^2 + 3 \[FormalX]^4) \[FormalF]
		+ (-1 + 3 \[FormalX]^2 - 6 \[FormalX]^4 + 3 \[FormalX]^6) \[FormalF]^2
		+ \[FormalX]^3 (3 - 3 \[FormalX]^2 + \[FormalX]^4) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{8, 13}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^5
		+ 2 \[FormalX]^4 (-2 + \[FormalX]^2) \[FormalF]
		+ (-1 + \[FormalX]) \[FormalX] (1 + \[FormalX]) (1 - 5 \[FormalX]^2 + \[FormalX]^4) \[FormalF]^2
		+ (1 - 4 \[FormalX]^2 + 6 \[FormalX]^4 - 2 \[FormalX]^6) \[FormalF]^3
		+ \[FormalX]^3 (-2 + \[FormalX]^2) \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 14}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^6
		+ \[FormalX]^5 (-5 + \[FormalX]^2) \[FormalF]
		- 2 \[FormalX]^4 (-5 + 2 \[FormalX]^2) \[FormalF]^2
		+ \[FormalX] (1 - 10 \[FormalX]^2 + 6 \[FormalX]^4) \[FormalF]^3
		- (-1 + \[FormalX]) (1 + \[FormalX]) (-1 + 2 \[FormalX]) (1 + 2 \[FormalX]) \[FormalF]^4
		+ \[FormalX]^3 \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{8, 15}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^4) (1 - \[FormalX]^6 + \[FormalX]^12)
		+ (-1 + 2 \[FormalX]^2 - 3 \[FormalX]^4 + 3 \[FormalX]^6 - 3 \[FormalX]^8 + 4 \[FormalX]^10 - 5 \[FormalX]^12 + 4 \[FormalX]^14 - 6 \[FormalX]^16) \[FormalF]
		+ \[FormalX]^3 (2 - 3 \[FormalX]^2 + 3 \[FormalX]^4 - 5 \[FormalX]^6 + 10 \[FormalX]^8 - 5 \[FormalX]^10 + 14 \[FormalX]^12) \[FormalF]^2
		- \[FormalX]^4 (-1 + 2 \[FormalX]^2 - 2 \[FormalX]^4 + 10 \[FormalX]^6 - \[FormalX]^8 + 16 \[FormalX]^10) \[FormalF]^3
		+ \[FormalX]^5 (1 + 5 \[FormalX]^4 + 2 \[FormalX]^6 + 9 \[FormalX]^8) \[FormalF]^4
		- \[FormalX]^8 (1 + \[FormalX]^2 + 2 \[FormalX]^4) \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{8, 16}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX] (1 + \[FormalX]) (1 + \[FormalX]^2) (1 - \[FormalX]^2 + \[FormalX]^4)
		+ (-1 + 2 \[FormalX]^2 - 2 \[FormalX]^4 - 2 \[FormalX]^6 + 6 \[FormalX]^8 - 2 \[FormalX]^10) \[FormalF]
		- \[FormalX]^3 (-2 + \[FormalX]^2 + 8 \[FormalX]^4 - 7 \[FormalX]^6 + \[FormalX]^8) \[FormalF]^2
		+ (-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) (-1 - 3 \[FormalX]^2 + 2 \[FormalX]^4) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{8, 17}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX]^9 (1 + \[FormalX])
		+ \[FormalX]^4 (1 - 5 \[FormalX]^4 + 6 \[FormalX]^6) \[FormalF]
		- \[FormalX] (-1 + 2 \[FormalX]^2) (1 - \[FormalX]^2 - \[FormalX]^4 + 7 \[FormalX]^6) \[FormalF]^2
		+ (-1 + 3 \[FormalX]^2 - 2 \[FormalX]^4 - 6 \[FormalX]^6 + 16 \[FormalX]^8) \[FormalF]^3
		- \[FormalX]^3 (-1 + 3 \[FormalX]^2) (1 + 3 \[FormalX]^2) \[FormalF]^4
		+ \[FormalX]^4 (1 + 2 \[FormalX]^2) \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{8, 18}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX] (1 + \[FormalX]) (1 + \[FormalX]^4)
		+ (-1 + 2 \[FormalX]^2 - 3 \[FormalX]^4 + 4 \[FormalX]^6) \[FormalF]
		- \[FormalX]^3 (-2 + 5 \[FormalX]^2) \[FormalF]^2
		+ 2 \[FormalX]^4 \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{8, 19}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^4)
		+ (-1 + 2 \[FormalX]^2 - 4 \[FormalX]^4 + \[FormalX]^6) \[FormalF]
		+ \[FormalX]^3 (3 - 3 \[FormalX]^2 + \[FormalX]^4) \[FormalF]^2
		- \[FormalX]^4 (-1 + 2 \[FormalX]^2) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{8, 20}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-\[FormalX] (-1 - \[FormalX] + \[FormalX]^3) (1 - \[FormalX] + \[FormalX]^3)
		+ (-1 + 2 \[FormalX]^2 - 6 \[FormalX]^4 + 4 \[FormalX]^6) \[FormalF]
		- 4 (-1 + \[FormalX]) \[FormalX]^3 (1 + \[FormalX]) \[FormalF]^2
		== 0
	]
BinaryTreeClassData[{8, 21}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX])
		- \[FormalX] (-1 + 3 \[FormalX]^2 - 5 \[FormalX]^4 + \[FormalX]^6) \[FormalF]
		+ (-1 + 3 \[FormalX]^2 - 7 \[FormalX]^4 + 3 \[FormalX]^6) \[FormalF]^2
		- \[FormalX]^3 (-3 + 2 \[FormalX]^2) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{8, 22}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX]^5 (1 + \[FormalX])
		+ \[FormalX]^4 (-4 + 5 \[FormalX]^2) \[FormalF]
		- \[FormalX] (-1 + 3 \[FormalX]^2)^2 \[FormalF]^2
		+ (1 - 4 \[FormalX]^2 + 7 \[FormalX]^4) \[FormalF]^3
		- 2 \[FormalX]^3 \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 23}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^7
		- \[FormalX]^4 (-1 + 5 \[FormalX]^2) \[FormalF]
		+ \[FormalX] (1 - 3 \[FormalX]^2 + 10 \[FormalX]^4) \[FormalF]^2
		- (1 - 3 \[FormalX] + 3 \[FormalX]^2) (1 + 3 \[FormalX] + 3 \[FormalX]^2) \[FormalF]^3
		+ 3 \[FormalX]^3 \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 24}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX]^3 (1 + \[FormalX])
		- \[FormalX]^2 (3 - 4 \[FormalX]^2 + 4 \[FormalX]^4) \[FormalF]
		- \[FormalX] (-3 + 5 \[FormalX]^2 - 12 \[FormalX]^4 + 6 \[FormalX]^6) \[FormalF]^2
		+ (-1 + 2 \[FormalX]^2 - 12 \[FormalX]^4 + 12 \[FormalX]^6 - 4 \[FormalX]^8) \[FormalF]^3
		- \[FormalX]^3 (-2 + \[FormalX]^2) (2 - 2 \[FormalX]^2 + \[FormalX]^4) \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 25}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^2 (1 - \[FormalX]^2 + \[FormalX]^4)
		+ \[FormalX] (-2 + 3 \[FormalX]^2 - 6 \[FormalX]^4 + 2 \[FormalX]^6) \[FormalF]
		+ (1 - 2 \[FormalX]^2 + 9 \[FormalX]^4 - 7 \[FormalX]^6 + \[FormalX]^8) \[FormalF]^2
		- \[FormalX]^3 (4 - 5 \[FormalX]^2 + 2 \[FormalX]^4) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{8, 26}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^7
		- 6 \[FormalX]^6 \[FormalF]
		+ 15 \[FormalX]^5 \[FormalF]^2
		- 20 \[FormalX]^4 \[FormalF]^3
		+ \[FormalX] (-1 + 15 \[FormalX]^2) \[FormalF]^4
		+ (1 - 6 \[FormalX]^2) \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{8, 27}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^4) (1 + \[FormalX]^16 + \[FormalX]^18 + \[FormalX]^20 + \[FormalX]^22)
		+ (-1 + 2 \[FormalX]^2 - 3 \[FormalX]^4 + \[FormalX]^6 - \[FormalX]^8 + \[FormalX]^10 - \[FormalX]^12 - \[FormalX]^14 - 6 \[FormalX]^16 - \[FormalX]^18 - 7 \[FormalX]^20 - 7 \[FormalX]^22 - 8 \[FormalX]^26 + \[FormalX]^28) \[FormalF]
		- \[FormalX]^3 (-2 + 2 \[FormalX]^2 - 3 \[FormalX]^4 + 3 \[FormalX]^6 - 5 \[FormalX]^8 - 4 \[FormalX]^10 - 15 \[FormalX]^12 - 5 \[FormalX]^14 - 20 \[FormalX]^16 - 21 \[FormalX]^18 - 27 \[FormalX]^22 + 7 \[FormalX]^24) \[FormalF]^2
		+ \[FormalX]^4 (1 - 3 \[FormalX]^2 + 2 \[FormalX]^4 - 8 \[FormalX]^6 - 6 \[FormalX]^8 - 20 \[FormalX]^10 - 9 \[FormalX]^12 - 31 \[FormalX]^14 - 35 \[FormalX]^16 - 50 \[FormalX]^20 + 21 \[FormalX]^22) \[FormalF]^3
		- \[FormalX]^5 (-1 - 5 \[FormalX]^4 - 4 \[FormalX]^6 - 15 \[FormalX]^8 - 7 \[FormalX]^10 - 29 \[FormalX]^12 - 35 \[FormalX]^14 - 55 \[FormalX]^18 + 35 \[FormalX]^20) \[FormalF]^4
		+ \[FormalX]^8 (-1 - \[FormalX]^2 - 6 \[FormalX]^4 - 2 \[FormalX]^6 - 17 \[FormalX]^8 - 21 \[FormalX]^10 - 36 \[FormalX]^14 + 35 \[FormalX]^16) \[FormalF]^5
		- \[FormalX]^11 (-1 - 6 \[FormalX]^4 - 7 \[FormalX]^6 - 13 \[FormalX]^10 + 21 \[FormalX]^12) \[FormalF]^6
		+ \[FormalX]^14 (-1 - \[FormalX]^2 - 2 \[FormalX]^6 + 7 \[FormalX]^8) \[FormalF]^7
		- \[FormalX]^21 \[FormalF]^8
		== 0
	]
BinaryTreeClassData[{8, 28}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-\[FormalX] (-1 + \[FormalX]^2 - \[FormalX]^4 + \[FormalX]^6 - \[FormalX]^8 + \[FormalX]^10 + \[FormalX]^14)
		+ (-1 + 2 \[FormalX]^2 - 4 \[FormalX]^4 + 4 \[FormalX]^6 - 5 \[FormalX]^8 + 8 \[FormalX]^10 - 3 \[FormalX]^12 + 5 \[FormalX]^14 - 5 \[FormalX]^16) \[FormalF]
		- \[FormalX]^3 (-1 + 2 \[FormalX]^6) (3 - 5 \[FormalX]^2 + 6 \[FormalX]^4 - 10 \[FormalX]^6 + 5 \[FormalX]^8) \[FormalF]^2
		- \[FormalX]^4 (-1 + 2 \[FormalX]^2 - 9 \[FormalX]^4 + 18 \[FormalX]^6 - 17 \[FormalX]^8 + 28 \[FormalX]^10 - 30 \[FormalX]^12 + 10 \[FormalX]^14) \[FormalF]^3
		- (-1 + \[FormalX]) \[FormalX]^7 (1 + \[FormalX]) (-1 + 4 \[FormalX]^2 - 4 \[FormalX]^4 + 12 \[FormalX]^6 - 15 \[FormalX]^8 + 5 \[FormalX]^10) \[FormalF]^4
		- (-1 + \[FormalX])^3 \[FormalX]^12 (1 + \[FormalX])^3 (-2 + \[FormalX]^2) \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{8, 29}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX] (1 + \[FormalX]) (1 + \[FormalX]^4 + \[FormalX]^6)
		+ (-1 + 2 \[FormalX]^2 - 3 \[FormalX]^4 + \[FormalX]^6 + 4 \[FormalX]^8 - \[FormalX]^10) \[FormalF]
		+ \[FormalX]^3 (2 - 2 \[FormalX]^2 - 5 \[FormalX]^4 + 3 \[FormalX]^6) \[FormalF]^2
		- (-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) (1 + 3 \[FormalX]^2) \[FormalF]^3
		+ \[FormalX]^7 \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 30}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^6)
		+ (-1 + 2 \[FormalX]^2 - 2 \[FormalX]^4 - 3 \[FormalX]^6 + 3 \[FormalX]^8) \[FormalF]
		+ \[FormalX]^3 (2 - 6 \[FormalX]^4 + 5 \[FormalX]^6) \[FormalF]^2
		+ (-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) (-1 - 2 \[FormalX]^2 + 5 \[FormalX]^4) \[FormalF]^3
		+ (-1 + \[FormalX]) \[FormalX]^7 (1 + \[FormalX]) (-1 + 3 \[FormalX]^2) \[FormalF]^4
		+ (-1 + \[FormalX]) \[FormalX]^10 (1 + \[FormalX]) \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{8, 31}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX] (1 - \[FormalX] + \[FormalX]^4) (1 + \[FormalX] + \[FormalX]^4)
		+ (-1 + 2 \[FormalX]^2 - 6 \[FormalX]^4 + 2 \[FormalX]^6 - 3 \[FormalX]^8 + 2 \[FormalX]^10) \[FormalF]
		+ \[FormalX]^3 (4 - 3 \[FormalX]^2 + 3 \[FormalX]^4 - 3 \[FormalX]^6 + \[FormalX]^8) \[FormalF]^2
		+ (-1 + \[FormalX]) \[FormalX]^6 (1 + \[FormalX]) (1 + \[FormalX]^2) \[FormalF]^3
		+ \[FormalX]^9 (-2 + \[FormalX]^2) \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 32}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^4 + \[FormalX]^6 - 2 \[FormalX]^8 + \[FormalX]^10)
		+ (-1 + 2 \[FormalX]^2 - 4 \[FormalX]^4 - 2 \[FormalX]^6 + 9 \[FormalX]^8 - 7 \[FormalX]^10 + \[FormalX]^12) \[FormalF]
		- \[FormalX]^3 (-1 - 2 \[FormalX]^2 + \[FormalX]^4) (3 - 6 \[FormalX]^2 + 4 \[FormalX]^4) \[FormalF]^2
		+ \[FormalX]^6 (-3 + 2 \[FormalX]^2) (-1 + 2 \[FormalX]^2) \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{8, 33}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^3 (1 - \[FormalX]^2 + \[FormalX]^6)
		+ \[FormalX]^2 (1 + \[FormalX]^2) (-3 + 7 \[FormalX]^2 - 10 \[FormalX]^4 + 5 \[FormalX]^6) \[FormalF]
		+ \[FormalX] (3 - 5 \[FormalX]^2 + 9 \[FormalX]^4 + 6 \[FormalX]^6 - 20 \[FormalX]^8 + 10 \[FormalX]^10) \[FormalF]^2
		+ (-1 + 2 \[FormalX]^2 - 9 \[FormalX]^4 - \[FormalX]^6 + 27 \[FormalX]^8 - 30 \[FormalX]^10 + 10 \[FormalX]^12) \[FormalF]^3
		+ \[FormalX]^3 (3 - \[FormalX]^2 - 15 \[FormalX]^4 + 29 \[FormalX]^6 - 20 \[FormalX]^8 + 5 \[FormalX]^10) \[FormalF]^4
		+ (-1 + \[FormalX])^2 \[FormalX]^6 (1 + \[FormalX])^2 (3 - 3 \[FormalX]^2 + \[FormalX]^4) \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{8, 34}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^2 (1 - \[FormalX]^2 + 2 \[FormalX]^4)
		+ \[FormalX] (-2 + 4 \[FormalX]^2 - 9 \[FormalX]^4 + 3 \[FormalX]^6) \[FormalF]
		+ (1 - 3 \[FormalX]^2 + 12 \[FormalX]^4 - 9 \[FormalX]^6 + 2 \[FormalX]^8) \[FormalF]^2
		- \[FormalX]^3 (4 - 6 \[FormalX]^2 + 5 \[FormalX]^4) \[FormalF]^3
		- \[FormalX]^6 (-2 + \[FormalX]^2) \[FormalF]^4
		- \[FormalX]^9 \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{8, 35}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^4)
		+ (-1 + 2 \[FormalX]^2 - 4 \[FormalX]^4 + \[FormalX]^6) \[FormalF]
		- 3 (-1 + \[FormalX]) \[FormalX]^3 (1 + \[FormalX]) \[FormalF]^2
		- (-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) \[FormalF]^3
		- \[FormalX]^7 \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 36}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX]^2 (1 + \[FormalX])
		- \[FormalX] (2 - 3 \[FormalX]^2 + 2 \[FormalX]^4) \[FormalF]
		- (-1 + \[FormalX]) (1 + \[FormalX]) (1 - \[FormalX]^2 + 3 \[FormalX]^4) \[FormalF]^2
		- (-1 + \[FormalX]) \[FormalX]^3 (1 + \[FormalX]) (-2 + 3 \[FormalX]^2) \[FormalF]^3
		- (-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) (-2 + \[FormalX]^2) \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 37}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^2 (1 - \[FormalX]^2 + \[FormalX]^6)
		+ \[FormalX] (-2 + 3 \[FormalX]^2 - 2 \[FormalX]^4 - 4 \[FormalX]^6 + 4 \[FormalX]^8) \[FormalF]
		+ (-1 + \[FormalX]) (1 + \[FormalX]) (-1 + \[FormalX]^2 - 3 \[FormalX]^4 - 6 \[FormalX]^6 + 6 \[FormalX]^8) \[FormalF]^2
		+ (-1 + \[FormalX]) \[FormalX]^3 (1 + \[FormalX]) (2 + \[FormalX]^2 - 8 \[FormalX]^4 + 4 \[FormalX]^6) \[FormalF]^3
		+ (-1 + \[FormalX]) \[FormalX]^4 (1 + \[FormalX]) (1 + 2 \[FormalX]^2 - 3 \[FormalX]^4 + \[FormalX]^6) \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 38}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX] (1 - \[FormalX]^2 + 2 \[FormalX]^4)
		+ (-1 + 2 \[FormalX]^2 - 6 \[FormalX]^4 + 2 \[FormalX]^6) \[FormalF]
		+ \[FormalX]^3 (4 - 3 \[FormalX]^2 + \[FormalX]^4) \[FormalF]^2
		- \[FormalX]^6 \[FormalF]^3
		== 0
	]
BinaryTreeClassData[{8, 39}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^2 (1 - \[FormalX]^2 + \[FormalX]^4)
		+ \[FormalX] (-2 + 3 \[FormalX]^2 - 6 \[FormalX]^4 + \[FormalX]^6) \[FormalF]
		+ (1 - 2 \[FormalX]^2 + 9 \[FormalX]^4 - 5 \[FormalX]^6) \[FormalF]^2
		- 2 \[FormalX]^3 (2 - 2 \[FormalX]^2 + \[FormalX]^4) \[FormalF]^3
		- (-1 + \[FormalX]) \[FormalX]^6 (1 + \[FormalX]) \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 40}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-(-1 + \[FormalX]) \[FormalX]^2 (1 + \[FormalX])
		- \[FormalX] (2 - 3 \[FormalX]^2 + 3 \[FormalX]^4) \[FormalF]
		+ (1 - 2 \[FormalX]^2 + 6 \[FormalX]^4 - 4 \[FormalX]^6) \[FormalF]^2
		- \[FormalX]^3 (3 - 5 \[FormalX]^2 + 3 \[FormalX]^4) \[FormalF]^3
		- (-1 + \[FormalX])^2 \[FormalX]^4 (1 + \[FormalX])^2 \[FormalF]^4
		== 0
	]
BinaryTreeClassData[{8, 41}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX] (1 - \[FormalX]^2 + \[FormalX]^6)
		+ (-1 + \[FormalX]) (1 + \[FormalX]) (1 - \[FormalX]^2 + \[FormalX]^4 + 4 \[FormalX]^6) \[FormalF]
		+ \[FormalX]^3 (2 + \[FormalX]^2 - 9 \[FormalX]^4 + 7 \[FormalX]^6) \[FormalF]^2
		+ (-1 + \[FormalX]) \[FormalX]^6 (1 + \[FormalX]) (-4 + 7 \[FormalX]^2) \[FormalF]^3
		+ (-1 + \[FormalX]) \[FormalX]^7 (1 + \[FormalX]) (-3 + 4 \[FormalX]^2) \[FormalF]^4
		+ (-1 + \[FormalX])^2 \[FormalX]^8 (1 + \[FormalX])^2 \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{8, 42}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		-\[FormalX] (-1 + \[FormalX]^2 - \[FormalX]^4 - \[FormalX]^6 + \[FormalX]^8)
		- (-1 + \[FormalX]) (1 + \[FormalX]) (-1 + \[FormalX]^2 - 3 \[FormalX]^4 - 5 \[FormalX]^6 + \[FormalX]^8) \[FormalF]
		- \[FormalX]^3 (-3 + 9 \[FormalX]^4 - 6 \[FormalX]^6 + \[FormalX]^8) \[FormalF]^2
		+ 3 \[FormalX]^6 (1 - 2 \[FormalX]^2 + 2 \[FormalX]^4) \[FormalF]^3
		+ 2 \[FormalX]^9 (-2 + \[FormalX]^2) \[FormalF]^4
		+ \[FormalX]^12 \[FormalF]^5
		== 0
	]
BinaryTreeClassData[{8, 43}, "AvoidingWeightEquation"] :=
	Function[{\[FormalF], \[FormalX]},
		\[FormalX]^2 (1 - \[FormalX]^2 + \[FormalX]^4)
		+ \[FormalX] (-2 + 4 \[FormalX]^2 - 6 \[FormalX]^4 + \[FormalX]^6) \[FormalF]
		+ (1 - 3 \[FormalX]^2 + 9 \[FormalX]^4 - 6 \[FormalX]^6 + \[FormalX]^8) \[FormalF]^2
		- 3 \[FormalX]^3 (1 - 2 \[FormalX]^2 + 2 \[FormalX]^4) \[FormalF]^3
		- \[FormalX]^4 (1 - 4 \[FormalX]^2 + 2 \[FormalX]^4) \[FormalF]^4
		- \[FormalX]^9 \[FormalF]^5
		== 0
	]
BinaryTreeClassData[class : {Except[8], _}?classQ, "AvoidingWeightEquation"] :=
	Function @@ {
		{\[FormalF], \[FormalX]},
		BinaryTreeClassData[class, "WeightEquation"][\[FormalF], \[FormalX], 0]
	}
BinaryTreeClassData[_?classQ, "AvoidingWeightEquation" | "WeightEquation"] := Missing["NotAvailable"]
SyntaxInformation[BinaryTreeClassData] = {"ArgumentsPattern" -> {_., _.}}


End[]

Protect["TreePatterns`*"]

EndPackage[]
