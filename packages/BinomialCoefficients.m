(* :Title: Binomial Coefficients *)

(* :Context: BinomialCoefficients` *)

(* :Author: Eric Rowland *)

(* :Date: {2014, 12, 6} *)

(* :Package Version: 1.13 *)

(* :Mathematica Version: 10 *)

(* :Discussion:
	BinomialCoefficients is a package containing implementations
	of several theorems on the residues and divisibility properties of binomial coefficients.
	Documentation can be found at  http://people.hofstra.edu/Eric_Rowland/packages.html .
*)


BeginPackage["BinomialCoefficients`"]

BinomialCoefficients`Private`$SymbolList = {
	BinomialComplementMod,
	BinomialExponent,
	BinomialMod,
	BinomialResidueCount,
	Carries,
	CoprimeFactorial
}


Unprotect["BinomialCoefficients`*"]

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



BinomialComplementMod::usage =
box[BinomialComplementMod["n", "m", "p"]] <> " gives the residue of " <> box[Binomial["n", "m"]] <> " modulo " <> box["p"] <> " after dividing by the largest power of " <> box["p"] <> " that divides " <> box[Binomial["n", "m"]] <> ".\n" <>
box[BinomialComplementMod["n", "m", "p"^"\[Alpha]"]] <> " gives the residue of " <> box[Binomial["n", "m"]] <> " modulo " <> box["p"^"\[Alpha]"] <> " after dividing by the largest power of " <> box["p"] <> " that divides " <> box[Binomial["n", "m"]] <> "."

BinomialExponent::usage =
box[BinomialExponent["n", "m", "k"]] <> " gives the exponent of the highest power of " <> box["k"] <> " that divides " <> box[Binomial["n", "m"]] <> "."

BinomialMod::usage =
box[BinomialMod["n", "m", "k"]] <> " gives the residue of " <> box[Binomial["n", "m"]] <> " modulo " <> box["k"] <> "."

BinomialResidueCount::usage =
box[BinomialResidueCount["n", "k", "r"]] <> " gives the number of binomial coefficients " <> box[Binomial["n", "m"]] <> " that are congruent to a nonzero residue " <> box["r"] <> " modulo " <> box["k"] <> ".\n" <>
box[BinomialResidueCount["n", "k"]] <> " gives the number of binomial coefficients " <> box[Binomial["n", "m"]] <> " that are not divisible by " <> box["k"] <> "."

Carries::usage =
box[Carries["m", "r", "b"]] <> " gives the number of carries involved in adding " <> box["m"] <> " and " <> box["r"] <> " in base " <> box["b"] <> ".\n" <>
box[Carries["m", "r", "b", "j"]] <> " gives the number of carries onto or beyond the " <> box["b"^"j"] <> " place."

CoprimeFactorial::usage =
box[CoprimeFactorial["n", "p"]] <> " computes the product of all natural numbers less than or equal to " <> box["n"] <> " that are not divisible by a prime " <> box["p"] <> "."


PositivePrimeQ[n_] := PrimeQ[n] && Positive[n]

PositivePrimePowerQ[n_] := PrimePowerQ[n] && Positive[n]

SetAttributes[Case, HoldRest]
Case[list : _[___], pattern_, alt_ : Null, n : (_Integer?Positive) : 1] :=
If[Length[#] >= n,
	Last[#],
	alt
] & @ Cases[list, pattern, {1}, n]

DigitList[0, b_Integer] /; b >= 2 =
	{}
DigitList[n_Integer?Positive, b_Integer] /; b >= 2 :=
	Reverse[IntegerDigits[n, b]]
DigitList[n_Integer?NonNegative, b_Integer /; b >= 2, length_Integer?NonNegative] :=
	Reverse[IntegerDigits[n, b, length]]

SetAttributes[Occurrence, HoldRest]
Occurrence[list : _[___], p_, alt_ : Null, n : (_Integer?Positive) : 1] :=
If[Length[#] >= n,
	#[[-1,1]],
	alt
] & @ Position[list, p, {1}, n, Heads -> False]

coefficient[p_, w_List] :=
	(p - First[w] - 1) Times @@ (p - Take[w, {2, -2}]) Last[w] / Times @@ (w + 1)

DisjointIntervalListQ[intervallist : {{_, _} ...}] :=
MatchQ[
	Apply[IntervalIntersection, Subsets[Interval /@ intervallist, {2}], {1}],
	{Interval[] ...}
]

NonOverlappingSubwordSum[f_, wordlengths : {___Integer?Positive}, word_List] :=
Total[(f @@ (word[[Span @@ #]] &) /@ # &) /@
	Select[
		Join @@@ Tuples[
			Replace[
				Tally[wordlengths],
				{length_, count_} :> Select[
					Subsets[Table[{i, i + length - 1}, {i, Length[word] - length + 1}], {count}],
					DisjointIntervalListQ
				],
				{1}
			]
		],
		DisjointIntervalListQ
	]
]

MyConnectedComponents[pairs_] :=
	(pairs[[#]] &) /@
		ConnectedComponents[AdjacencyGraph[Outer[Boole[Intersection[##] != {}] &, pairs, pairs, 1]]]

MyFindPath[edges : {{_, _} ..}] :=
Module[{edge, orderededges = {}, remainingedges = edges},
	edge = Case[Tally[Join @@ edges], {v_, 1} :> Case[edges, {v, _} | {_, v}], First[edges]];
	AppendTo[orderededges, edge];
	remainingedges = DeleteCases[remainingedges, edge, {1}, 1];
	While[remainingedges != {},
		edge = Case[remainingedges, _?(Intersection[#, Join @@ orderededges] != {} &), $Failed];
		AppendTo[orderededges, edge];
		remainingedges = DeleteCases[remainingedges, edge, {1}, 1]
	];
	orderededges
]

RestrictedClusters[subwordlengths_, requiredoverlaps_] :=
With[{wordindices = DeleteDuplicates[Join @@ MyFindPath[requiredoverlaps]]},
	(# + 1 - Min[#] &) /@ Fold[
		Function[{clumplist, newwordindex},
			Join @@ Function[clump,
				Function[i, Append[clump, Range[i, i + subwordlengths[[newwordindex]] - 1]]] /@ Replace[
					IntervalIntersection @@ Cases[
						requiredoverlaps,
						{newwordindex, overlappingwordindex_} | {overlappingwordindex_, newwordindex} /;
								Occurrence[wordindices, overlappingwordindex] < Occurrence[wordindices, newwordindex] :>
							Interval[
								{1 - subwordlengths[[newwordindex]], subwordlengths[[overlappingwordindex]] - 1} +
									First[clump[[Occurrence[wordindices, overlappingwordindex]]]]
							]
					],
					{Interval[interval_] :> Range @@ interval, Interval[] -> {}}
				]
			] /@ clumplist
		],
		{{Range[subwordlengths[[First[wordindices]]]]}},
		Rest[wordindices]
	]
]


SetAttributes[BinomialComplementMod, Listable]
BinomialComplementMod[n_Integer?NonNegative, m_Integer?NonNegative, p_?PositivePrimeQ] /; m <= n :=
	Mod[
		(-1)^BinomialExponent[n, m, p] Times @@
			(#1! PowerMod[#2! #3!, -1, p] &) @@@
				Transpose[PadLeft[IntegerDigits[{n, m, n - m}, p]]],
		p
	]
BinomialComplementMod[n_Integer?NonNegative, m_Integer?NonNegative, k_?PositivePrimePowerQ] /; m <= n :=
Module[{p, q, r = n - m},
	{p, q} = NumberTheory`PrimePower[k];
	Mod[
		If[p == 2 && q >= 3, 1, (-1)^Carries[m, r, p, q-1]]
		*
		Times @@
			(CoprimeFactorial[#1, p] PowerMod[CoprimeFactorial[#2, p] CoprimeFactorial[#3, p], -1, k] &) @@@
				Transpose[PadLeft[
					Mod[Floor[#/p^Range[IntegerLength[#, p] - 1, 0, -1]], k] & /@
						{n, m, r}
				]],
		k
	]
]
BinomialComplementMod[n_Integer?NonNegative, m_Integer?NonNegative, _?PositivePrimePowerQ] /; m > n := 0
BinomialComplementMod[_Integer?NonNegative, _Integer?Negative, _?PositivePrimePowerQ] := 0
SyntaxInformation[BinomialComplementMod] = {"ArgumentsPattern" -> {_, _, _}}

SetAttributes[BinomialExponent, Listable]
BinomialExponent[n_Integer?NonNegative, m_Integer?NonNegative, p_?PositivePrimeQ] /; m <= n :=
(* This isn't as fast as using Legendre's formula.
	Carries[m, n - m, p]
*)
	(Total[IntegerDigits[m, p]] + Total[IntegerDigits[n - m, p]] - Total[IntegerDigits[n, p]])/(p - 1)
BinomialExponent[n_Integer?NonNegative, m_Integer?NonNegative, k_Integer /; k >= 2] /; m <= n :=
With[{primepowers = FactorInteger[k]},
	Floor[Min[BinomialExponent[n, m, First /@ primepowers] / (Last /@ primepowers)]]
]
BinomialExponent[_Integer?NonNegative, _Integer, k_Integer /; k >= 2] := Infinity
SyntaxInformation[BinomialExponent] = {"ArgumentsPattern" -> {_, _, _}}

SetAttributes[BinomialMod, Listable]
BinomialMod[n_Integer?NonNegative, m_Integer?NonNegative, p_?PositivePrimeQ] :=
	Mod[Times @@ Binomial @@@ Transpose[PadLeft[IntegerDigits[{n, m}, p]]], p]
BinomialMod[n_Integer?NonNegative, m_Integer?NonNegative, k_?PositivePrimePowerQ] /; m <= n :=
With[{p = First[NumberTheory`PrimePower[k]]},
	Mod[
		p^BinomialExponent[n, m, p] BinomialComplementMod[n, m, k],
		k
	]
]
BinomialMod[n_Integer?NonNegative, m_Integer?NonNegative, k_Integer /; k >= 2] :=
With[{primepowers = Power @@@ FactorInteger[k]},
	ChineseRemainder[BinomialMod[n, m, primepowers], primepowers]
]
BinomialMod[_Integer?NonNegative, _Integer?Negative, k_Integer /; k >= 2] := 0
SyntaxInformation[BinomialMod] = {"ArgumentsPattern" -> {_, _, _}}

SetAttributes[BinomialResidueCount, Listable]
BinomialResidueCount[n_Integer?NonNegative, p_?PositivePrimeQ, r_Integer] /; !Divisible[r, p] :=
Module[{permutation, x},
	permutation = Ordering[PowerMod[PrimitiveRoot[p], Range[0, p - 2], p]] - 1;
	Coefficient[PolynomialMod[
		Product[
			Total[#2 x^permutation[[#1]] & @@@
				Tally[DeleteCases[Mod[Binomial[j, Range[0, j]], p], 0]]
			]^DigitCount[n, p, j],
			{j, p - 1}
		],
		x^(p - 1) - 1
	], x, permutation[[Mod[r, p]]]]
]
BinomialResidueCount[n_Integer?NonNegative, k_Integer /; k >= 2, r_Integer] /; 1 <= r <= k - 1 :=
	2 Count[BinomialMod[n, Range[0, (n - 1)/2], k], r] + Boole[EvenQ[n] && BinomialMod[n, n/2, k] == r]
BinomialResidueCount[n_Integer?NonNegative, 1] := 0
BinomialResidueCount[n_Integer?NonNegative, k_?PositivePrimePowerQ] :=
Module[{p, alpha, digits},
	{p, alpha} = NumberTheory`PrimePower[k];
	digits = DigitList[n, p];
	Times @@ (digits + 1)
	*
	Sum[
		Total[Function[partition,
			NonOverlappingSubwordSum[Times @@ (coefficient[p, #] &) /@ {##} &, partition, digits]
		] /@ IntegerPartitions[gamma, {Max[0, gamma - (alpha - 1)], Infinity}, Range[2, gamma]]],
		{gamma, 0, 2 (alpha - 1)}
	]
]
BinomialResidueCount[n_Integer?NonNegative, k_Integer /; k >= 2] :=
	2 Count[BinomialMod[n, Range[0, (n - 1)/2], k], Except[0]] + Boole[EvenQ[n] && BinomialMod[n, n/2, k] != 0]
BinomialResidueCount[n_ /; !NumericQ[n], k_?PositivePrimePowerQ] :=
Module[{p, alpha},
	{p, alpha} = NumberTheory`PrimePower[k];
	Product[(w + 1)^IntegerSequences`DigitsCount[n, p, w], {w, 0, p - 1}]
	*
	Expand[Sum[
		Total[Function[partition,
			Total[Function[pairs,
				With[{connectedcomponents = MyConnectedComponents[pairs]},
					(-1)^Length[pairs]
					*
					Times @@ (Total[Function[cluster,
							Total[Apply[
								Evaluate[
									IntegerSequences`DigitsCount[n, p, {##}]
									*
									Times @@ (coefficient[p, #] &) /@ (cluster /. i_Integer :> Slot[i])
								] &,
								Tuples[Range[0, p - 1], Max[cluster]],
								{1}
							]]
						] /@ #] &) /@
							Join[
								RestrictedClusters[partition, #] & /@ connectedcomponents,
								{{Range[#]}} & /@
									partition[[Complement[Range[Length[partition]], Flatten[connectedcomponents]]]]
							]
				]
			] /@
				Subsets[Subsets[Range[Length[partition]], {2}]]
			]
			/
			Times @@ (Last /@ Tally[partition]!)
		] /@ IntegerPartitions[gamma, {Max[0, gamma - (alpha - 1)], Infinity}, Range[2, gamma]]],
		{gamma, 0, 2 (alpha - 1)}
	]]
]
SyntaxInformation[BinomialResidueCount] = {"ArgumentsPattern" -> {_, _, _.}}

SetAttributes[Carries, Listable]
Carries[m_Integer?NonNegative, r_Integer?NonNegative, b_Integer /; b >= 2, j : (_Integer?NonNegative) : 0] :=
Module[{i = 0, count = 0, carry = 0},
	(
		If[# + carry < b,
			carry = 0
			,
			carry = 1;
			If[i >= j, count++]
		];
		i++
	) & /@ Reverse[Prepend[Total[PadLeft[IntegerDigits[{m, r}, b]]], 0]];
	count
]
SyntaxInformation[Carries] = {"ArgumentsPattern" -> {_, _, _, _.}}

SetAttributes[CoprimeFactorial, Listable]
CoprimeFactorial[n_Integer?NonNegative, p_?PositivePrimeQ] :=
	n!/(Floor[n/p]! p^Floor[n/p])
SyntaxInformation[CoprimeFactorial] = {"ArgumentsPattern" -> {_, _}}


End[]

Protect["BinomialCoefficients`*"]

EndPackage[]
