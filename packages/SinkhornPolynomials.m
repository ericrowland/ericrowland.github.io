(* :Title: Sinkhorn Polynomials *)

(* :Context: SinkhornPolynomials` *)

(* :Author: Eric Rowland and Jason Wu *)

(* :Date: {2025, 5, 20} *)

(* :Package Version: 2.00 *)

(* :Mathematica Version: 14 *)

(* :Discussion:
	SinkhornPolynomials is a package for computing the polynomial equation satisfied by an entry of the Sinkhorn limit of a matrix.
	Documentation can be found at  https://ericrowland.github.io/packages.html .
*)


BeginPackage["SinkhornPolynomials`"]

SinkhornPolynomials`Private`$SymbolList = {
	SinkhornFixedPoint,
	SinkhornPolynomial,
	SinkhornPolynomialCoefficient
}


Unprotect["SinkhornPolynomials`*"]

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


SinkhornFixedPoint::usage =
box[SinkhornFixedPoint["m"]] <> " iteratively scales the rows and columns of the matrix " <> box["m"] <> " until the result no longer changes. At each step, the rows are scaled so that each row sum is " <> box[1] <> ", and then the columns are scaled so that each column sum is " <> box[Divide @@ Dimensions["m"]] <> ".\n" <>
box[SinkhornFixedPoint["m", "r"]] <> " scales the rows so that each row sum is " <> box["r"] <> " and scales the columns accordingly."

SinkhornPolynomial::usage =
box[SinkhornPolynomial["m", "x"]] <> " gives the Sinkhorn polynomial in " <> box["x"] <> " with coefficients evaluated at the entries of the matrix " <> box["m"] <> ".\n" <>
box[SinkhornPolynomial["m", "x", "r"]] <> " scales the coefficients of the polynomial to correspond to the limit with row sum " <> box["r"] <> "."

SinkhornPolynomialCoefficient::usage =
box[SinkhornPolynomialCoefficient["m", "k"]] <> " gives the coefficient of " <> box["x"^"k"] <> " in the Sinkhorn polynomial in " <> box["x"] <> " for the matrix " <> box["m"] <> ".\n" <>
box[SinkhornPolynomialCoefficient["m", "k", "r"]] <> " scales the coefficient to correspond to the limit with row sum " <> box["r"] <> "."


DiscretePower[0, 0] = 1
DiscretePower[a_, b_] := a^b

FirstPositionLevel1[expression_, pattern_] :=
	First[FirstPosition[expression, pattern, {Missing["NotFound"]}, {1}, Heads -> False]]

LinkingStructureMatrix[topleftminorspecifications_, {rowcount_, columncount_}] :=
Module[{exponent, rowindices1, columnindices1, rowindices2, columnindices2, i, j},
	exponent = Length[topleftminorspecifications];
	Table[
		{rowindices1, columnindices1} = topleftminorspecifications[[i]];
		Table[
			If[i == j,
				(* diagonal entry *)
				Length[rowindices1] (rowcount + columncount) - rowcount columncount,
				(* off-diagonal entry *)
				{rowindices2, columnindices2} = topleftminorspecifications[[j]];
				Replace[
					{
						{Complement[rowindices1, rowindices2], Complement[rowindices2, rowindices1]},
						{Complement[columnindices1, columnindices2], Complement[columnindices2, columnindices1]}
					},
					{
						(* linked pair with different sizes ("type 1") *)
						{{{}, {s_}}, {{}, {t_}}} :> (-1)^(FirstPositionLevel1[rowindices2, s] + FirstPositionLevel1[columnindices2, t]) rowcount,
						{{{s_}, {}}, {{t_}, {}}} :> (-1)^(FirstPositionLevel1[rowindices1, s] + FirstPositionLevel1[columnindices1, t] + 1) columncount,
						(* linked pair with the same size ("type 2") *)
						{{{}, {}}, {{s_}, {t_}}} :> (-1)^(FirstPositionLevel1[columnindices1, s] + FirstPositionLevel1[columnindices2, t]) rowcount,
						{{{s_}, {t_}}, {{}, {}}} :> (-1)^(FirstPositionLevel1[rowindices1, s] + FirstPositionLevel1[rowindices2, t]) columncount,
						(* unlinked pair *)
						_ :> 0
					}
				]
			],
			{j, 1, exponent}
		],
		{i, 1, exponent}
	]
]
LinkingStructureMatrix[{rowcount_, columncount_}] := (
	LinkingStructureMatrix[{rowcount, columncount}] =
		LinkingStructureMatrix[
			MinorSpecifications[{rowcount, columncount}],
			{rowcount, columncount}
		]
)

ListScale[list_, total_] :=
	total/Total[list] list

MatrixScale[matrix_, rowtotal_, columntotal_] :=
	Transpose[Map[
		ListScale[#, columntotal] &,
		Transpose[Map[ListScale[#, rowtotal] &, matrix]]
	]]

MinorSpecifications[{rowcount_, columncount_}] := (
	MinorSpecifications[{rowcount, columncount}] =
		Module[{submatrixsize},
			Join @@ Table[
				Tuples[{
					Subsets[Range[2, rowcount], {submatrixsize}],
					Subsets[Range[2, columncount], {submatrixsize}]
				}],
				{submatrixsize, 0, Min[rowcount, columncount] - 1}
			]
		]
)

(* "Delta" *)
TopLeftMinor[matrix_, rowindices_, columnindices_] :=
	Det[matrix[[Prepend[rowindices, 1], Prepend[columnindices, 1]]]]

(* "Gamma" *)
MinorWithTopLeftFactor[matrix_, {}, {}] :=
	matrix[[1, 1]]
MinorWithTopLeftFactor[matrix_, rowindices_, columnindices_] :=
	matrix[[1, 1]] Det[matrix[[rowindices, columnindices]]]

(* not in use *)
MinorProductMonomial[matrix_, minorspecifications_, topleftminorspecifications_] :=
Module[{minorspecification},
	Times[
		Product[
			TopLeftMinor[matrix, Sequence @@ minorspecification],
			{minorspecification, topleftminorspecifications}
		],
		Product[
			MinorWithTopLeftFactor[matrix, Sequence @@ minorspecification],
			{minorspecification, DeleteCases[minorspecifications, Alternatives @@ topleftminorspecifications]}
		]
	]
]


SinkhornFixedPoint[
	matrix_ /; MatrixQ[matrix, NumericQ],
	rowtotal : Except[0 | 0. | _DirectedInfinity] : 1
] :=
With[{columntotal = rowtotal Divide @@ Dimensions[matrix]},
	FixedPoint[
		MatrixScale[#, rowtotal, columntotal] &,
		If[AllTrue[matrix, ExactNumberQ, 2],
			N[matrix, $MachinePrecision],
			matrix
		]
	]
]
SyntaxInformation[SinkhornFixedPoint] = {"ArgumentsPattern" -> {_, _.}}

SinkhornPolynomial[
	matrix_?MatrixQ,
	x_,
	rowtotal : Except[0 | 0. | _DirectedInfinity | _Rule | _RuleDelayed] : 1,
	OptionsPattern[]
] :=
Module[{rowcount, columncount, degree, minorspecifications, minorswithtopleftfactor, linkingstructurematrix, method, polynomial, exponent},
	{rowcount, columncount} = Dimensions[matrix];
	degree = Binomial[rowcount + columncount - 2, rowcount - 1];
	If[TrueQ[OptionValue[ProgressReporting]], Monitor, List][
		minorspecifications = MinorSpecifications[{rowcount, columncount}];
		minorswithtopleftfactor = Function[minorspecification,
			MinorWithTopLeftFactor[matrix, Sequence @@ minorspecification]
		] /@ minorspecifications;
		linkingstructurematrix = LinkingStructureMatrix[{rowcount, columncount}];
		method = OptionValue[Method];
		If[!MemberQ[{Automatic, "ExplicitSum", "FactoringOutLargeMinors", "FactoringOutSmallMinors"}, method],
			Message[SinkhornPolynomial::method, method];
			method = Automatic
		];
		polynomial = Sum[
			Times[
				sinkhornPolynomialCoefficient[
					matrix,
					exponent,
					rowcount rowtotal,
					minorspecifications,
					minorswithtopleftfactor,
					linkingstructurematrix,
					method
				],
				DiscretePower[x, exponent]
			],
			{exponent, 0, degree}
		],
		ProgressIndicator[exponent, {0, degree}]
	];
	polynomial
]
Options[SinkhornPolynomial] = {Method -> Automatic, ProgressReporting :> $ProgressReporting}
SyntaxInformation[SinkhornPolynomial] = {"ArgumentsPattern" -> {_, _, _., OptionsPattern[]}}

sinkhornPolynomialCoefficient[
	matrix_,
	exponent_,
	sumofentries_,
	minorspecifications_,
	minorswithtopleftfactor_,
	linkingstructurematrix_,
	mthd_
] :=
Module[{method, numericfactor, minorspecificationindices, topleftminors, minorratios, topleftminorspecificationindices, minorspecification},
	(* Treat the constant coefficient separately because Det[{}] doesn't evaluate to 1. *)
	If[exponent == 0,
		Times @@ minorswithtopleftfactor
		,
		method = mthd;
		If[method === Automatic,
			method = If[MemberQ[minorswithtopleftfactor, 0 | 0. | _?(Not@*NumberQ)],
				"ExplicitSum",
				"FactoringOutSmallMinors"
			]
		];
		numericfactor = sumofentries^-exponent;
		minorspecificationindices = Range[1, Length[minorspecifications]];
		Switch[method,
			"ExplicitSum",
			(* Use the explicit sum of monomials. *)
			Sum[
				Times[
					numericfactor,
					Det[linkingstructurematrix[[topleftminorspecificationindices, topleftminorspecificationindices]]],
					(* These comprise a slightly more efficient version of MinorProductMonomial. *)
					Product[
						TopLeftMinor[matrix, Sequence @@ minorspecification],
						{minorspecification, minorspecifications[[topleftminorspecificationindices]]}
					],
					Product[
						MinorWithTopLeftFactor[matrix, Sequence @@ minorspecification],
						{minorspecification, minorspecifications[[Complement[minorspecificationindices, topleftminorspecificationindices]]]}
					]
				],
				{topleftminorspecificationindices, Subsets[minorspecificationindices, {exponent}]}
			]
			,
			"FactoringOutLargeMinors",
			(* Factor out the product of TopLeftMinor[ ]s. *)
			topleftminors = Table[
				TopLeftMinor[matrix, Sequence @@ minorspecification],
				{minorspecification, minorspecifications}
			];
			minorratios = minorswithtopleftfactor/topleftminors;
			Times[
				Times @@ topleftminors,
				Sum[
					Times[
						numericfactor,
						Det[linkingstructurematrix[[topleftminorspecificationindices, topleftminorspecificationindices]]],
						Times @@ minorratios[[Complement[minorspecificationindices, topleftminorspecificationindices]]]
					],
					{topleftminorspecificationindices, Subsets[minorspecificationindices, {exponent}]}
				]
			]
			,
			"FactoringOutSmallMinors",
			(* Factor out the product of MinorWithTopLeftFactor[ ]s. *)
			topleftminors = Table[
				TopLeftMinor[matrix, Sequence @@ minorspecification],
				{minorspecification, minorspecifications}
			];
			minorratios = topleftminors/minorswithtopleftfactor;
			Times[
				Times @@ minorswithtopleftfactor,
				Sum[
					Times[
						numericfactor,
						Det[linkingstructurematrix[[topleftminorspecificationindices, topleftminorspecificationindices]]],
						Times @@ minorratios[[topleftminorspecificationindices]]
					],
					{topleftminorspecificationindices, Subsets[minorspecificationindices, {exponent}]}
				]
			]
		]
	]
]
SinkhornPolynomialCoefficient[
	matrix_?MatrixQ,
	exponent_Integer?NonNegative,
	rowtotal : Except[0 | 0. | _DirectedInfinity | _Rule | _RuleDelayed] : 1,
	OptionsPattern[]
] :=
Module[{rowcount, columncount, minorspecifications, method},
	{rowcount, columncount} = Dimensions[matrix];
	minorspecifications = MinorSpecifications[{rowcount, columncount}];
	method = OptionValue[Method];
	If[!MemberQ[{Automatic, "ExplicitSum", "FactoringOutLargeMinors", "FactoringOutSmallMinors"}, method],
		Message[SinkhornPolynomialCoefficient::method, method];
		method = Automatic
	];
	sinkhornPolynomialCoefficient[
		matrix,
		exponent,
		rowcount rowtotal,
		minorspecifications,
		Function[minorspecification,
			MinorWithTopLeftFactor[matrix, Sequence @@ minorspecification]
		] /@ minorspecifications,
		LinkingStructureMatrix[{rowcount, columncount}],
		method
	]
]
SinkhornPolynomialCoefficient[
	_?MatrixQ,
	_Integer?Negative,
	rowtotal : Except[0 | 0. | _DirectedInfinity | _Rule | _RuleDelayed] : 1,
	OptionsPattern[]
] :=
	0
Options[SinkhornPolynomialCoefficient] = {Method -> Automatic}
SyntaxInformation[SinkhornPolynomialCoefficient] = {"ArgumentsPattern" -> {_, _, _., OptionsPattern[]}}


End[]

Protect["SinkhornPolynomials`*"]

EndPackage[]
