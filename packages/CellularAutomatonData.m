(* :Title: Cellular Automaton Data *)

(* :Context: CellularAutomatonData` *)

(* :Author: Charles Brummitt and Eric Rowland *)

(* :Date: {2012, 4, 2} *)

(* :Package Version: 1.00 *)

(* :Mathematica Version: 8 *)

(* :Discussion:
	CellularAutomatonData is a source of data on boundaries of one-dimensional cellular automata.
	Documentation can be found at  http://people.hofstra.edu/Eric_Rowland/packages.html .
*)


BeginPackage["CellularAutomatonData`"]

CellularAutomatonData`Private`$SymbolList = {
	CellularAutomatonData,
	$ExponentlessAutomatonInitialCondition,
	$ExponentlessAutomatonRule
}


Unprotect["CellularAutomatonData`*"]

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


CellularAutomatonData::usage =
box[CellularAutomatonData[{{"n", "k", "r"}, "init"}, String["property"]]] <> " gives the value for the specified property for a cellular automaton."

$ExponentlessAutomatonInitialCondition::usage =
"$ExponentlessAutomatonInitialCondition gives the initial condition of a cellular automaton with no limiting growth exponent."

$ExponentlessAutomatonRule::usage =
"$ExponentlessAutomatonRule gives the rule of a cellular automaton with no limiting growth exponent."


EquivalentRuleRelationships[{n_, k_, r_}] :=
Module[{ruletable = RuleTable[{n, k, r}], permutedruletable},
	Sort[Join @@
		Function[permutation,
			permutedruletable = ruletable /. Thread[Range[0, k - 1] -> permutation];
			{
				{
					Last /@ Sort[permutedruletable] . k^Range[0, k^(2 r + 1) - 1],
					permutation,
					False
				},
				{
					Last /@ Sort[{Reverse[#1], #2} & @@@ permutedruletable] . k^Range[0, k^(2 r + 1) - 1],
					permutation,
					True
				}
			}
		] /@ Permutations[Range[0, k - 1]]
	]
]

RuleTable[{n_, k_, r_}] :=
	Thread[Tuples[Range[0, k - 1], 2 r + 1] -> Reverse[IntegerDigits[n, k, k^(2 r + 1)]]]


CellularAutomatonData["Properties"] = {
	"BestFits",
	"BoundaryWordCoding",
	"BoundaryWordMorphism",
	"BoundaryWordPeriodLength",
	"Diffusivity",
	"GrowthExponent",
	"GrowthRate",
	"GrowthRateLimInf",
	"GrowthRateLimSup",
	"PecletNumber",
	"Randomness"
}

CellularAutomatonData[
	{
		(* We don't check that n is small enough to be a valid rule number. *)
		{n_Integer?NonNegative, k_Integer /; k >= 2, r_?NonNegative /; IntegerQ[2r]},
		(* We also don't check that the cell values in the initial condition are in range. *)
		{foreground : {___Integer}, backgroundcolor_Integer}
	},
	property_String
] :=
Module[{minimaln, permutation, reversedQ, initialcondition, initialconditiondata, propertyvalue},
	{minimaln, permutation, reversedQ} = First[EquivalentRuleRelationships[{n, k, r}]];
	initialcondition = If[reversedQ,
		{Reverse[foreground], backgroundcolor},
		{foreground, backgroundcolor}
	];
	initialcondition = initialcondition /. Thread[Range[0, k - 1] -> permutation];
	initialconditiondata = Replace[
		initialcondition,
		Append[
			Replace[
				minimaln,
				data[k, 2 r + 1]
			],
			_ -> Missing["NotAvailable"]
		]
	];
	If[MatchQ[initialconditiondata, _Missing],
		initialconditiondata
		,
		propertyvalue = Replace[
			Replace[property, "Drift" -> "GrowthRate"],
			Append[
				initialconditiondata,
				_ -> Missing["NotAvailable"]
			]
		];
		If[MatchQ[propertyvalue, _Missing],
			Switch[{property, initialconditiondata},
				{"GrowthExponent", {___, "BoundaryWordPeriodLength" -> _Integer, ___, "GrowthRate" -> 0, ___}},
					0,
				{"GrowthExponent", {___, "GrowthRate" -> Except[0], ___}},
					1,
				{"Properties", _},
					CellularAutomatonData["Properties"],
				_,
					propertyvalue
			],
			propertyvalue
		]
	]
]
SyntaxInformation[CellularAutomatonData] = {"ArgumentsPattern" -> {_, _.}}


$ExponentlessAutomatonInitialCondition = {{2, 8, 9, 9, 0, 0, 3}, 0}

$ExponentlessAutomatonRule = {
	{0 | 9, 0, 9, 8} -> 9,
	{0, 9, 3, 0} -> 3,
	{0, 9, 8, 8} -> 3,
	{9, 9, 3, 0} -> 12,
	{9, 9, 9, 3} -> 1,
	{_, _, 3, 0} -> 3,
	{_?(Floor[#, 9] == 9 &), 9, y : 0 | 9, 1 | 10} -> 10 - y,
	{_?(Floor[#, 9] == 9 &), 9, y : 0 | 9, 8 | 17} -> 17 - y,
	{_?(Floor[#, 9] == 9 &), 9, y : 1 | 10, 0 | 9} -> 10 - y,
	{_?(Floor[#, 9] == 9 &), 9, y : 1 | 10, 3 | 12} -> 14 - y,
	{_?(Floor[#, 9] == 9 &), 9, y : 7 | 16, 1 | 10} -> 24 - y,
	{_?(Floor[#, 9] == 9 &), 16, y : 1 | 10, 1 | 10} -> 18 - y,
	{_?(Floor[#, 9] == 9 &), 17, y : 0 | 9, 1 | 10} -> 10 - y,
	{_?(Floor[#, 9] == 9 &), 17, y : 1 | 10, 3 | 12} -> 18 - y,
	{_?(Floor[#, 9] == 9 &), 17, y : 4 | 13, _} -> 20 - y,
	{_?(Floor[#, 9] == 9 &), 17, y : 8 | 17, 5 | 14} -> 24 - y,
	{_?(Floor[#, 9] == 9 &), 17, y : 8 | 17, 0 | 1 | 9 | 10} -> 17 - y,
	{_?(Floor[#, 9] == 9 &), 17, y : 5 | 6 | 14 | 15, 1 | 2 | 10 | 11} -> 17 - Floor[y, 9],
	{_?(Floor[#, 9] == 9 &), 9, y_, 3 | 12} -> 9 - Floor[y, 9],
	{_?(Floor[#, 9] == 9 &), _?(Floor[#, 9] == 9 &), y : 2 | 11, 3 | 12} -> 14 - y,
	{_?(Floor[#, 9] == 9 &), 10, y : 1 | 10, 3 | 12} -> 14 - y,
	{_?(Floor[#, 9] == 9 &), _?(Floor[#, 9] == 9 &), y : 1 | 10, 4 | 13} -> 14 - y,
	{_?(Floor[#, 9] == 9 &), 10 | 11, y : 3 | 12, _} -> 17 - y,
	{_?(Floor[#, 9] == 9 &), x : 9 | 10, y : 4 | 13, _} -> 29 - x - y,
	{_?(Floor[#, 9] == 9 &), 16, y : 2 | 11, 6 | 15} -> 14 - y,
	{_?(Floor[#, 9] == 9 &), 16, y_, _} -> 16 - Floor[y, 9],
	{_?(Floor[#, 9] == 9 &), _?(Floor[#, 9] == 9 &), y : 7 | 16, z : 1 | 2 | 10 | 11} -> 16 - y + Mod[z, 9],
	{_?(Floor[#, 9] == 9 &), _?(Floor[#, 9] == 9 &), y : 5 | 6 | 14 | 15, _} -> 16 - Floor[y, 9] - Mod[y, 9],
	{_?(Floor[#, 9] == 9 &), 14 | 15, y : 1 | 2 | 10 | 11, _} -> 16 - Floor[y, 9] - Mod[y, 9],
	{_?(Floor[#, 9] == 9 &), 14 | 15, y : 0 | 9, 0 | 9} -> 10 - y,
	{_?(Floor[#, 9] == 9 &), _?(Floor[#, 9] == 9 &), y : 1 | 2 | 10 | 11, _} -> 9 - Floor[y, 9] + Mod[y, 9],
	{_?(Floor[#, 9] == 9 &), _?(Floor[#, 9] == 9 &), y : 8 | 17, _} -> 25 - y,
	{_?(Floor[#, 9] == 9 &), _?(Floor[#, 9] == 9 &), y_, _} -> 9 - Floor[y, 9],
	{_, 0 | 9, y : 0 | 9, 1 | 10} -> 1 + y,
	{_, 0 | 9, y : 0 | 9, 8 | 17} -> 8 + y,
	{_, 0 | 9, y : 1 | 10, 0 | 9} -> -1 + y,
	{_, 0 | 9, y : 1 | 10, 3 | 12} -> 3 + y,
	{_, 0 | 9, y : 7 | 16, 1 | 10} -> 1 + y,
	{_, 7 | 16, y : 1 | 10, 1 | 10} -> 7 + y,
	{_, 8 | 17, y : 0 | 9, 1 | 10} -> 1 + y,
	{_, 8 | 17, y : 1 | 10, 3 | 12} -> 7 + y,
	{_, 8 | 17, y : 4 | 13, _} -> 3 + y,
	{_, 8 | 17, y : 8 | 17, 5 | 14} -> -1 + y,
	{_, 8 | 17, y : 8 | 17, 0 | 1 | 9 | 10} -> -8 + y,
	{_, 8 | 17, y : 5 | 6 | 14 | 15, 1 | 2 | 10 | 11} -> 8 + Floor[y, 9],
	{_, 0 | 9, y_, 3 | 12} -> Floor[y, 9],
	{_, _, y : 2 | 11, 3 | 12} -> 1 + y,
	{_, 1 | 10, y : 1 | 10, 3 | 12} -> 3 + y,
	{_, _, y : 1 | 10, 4 | 13} -> 3 + y,
	{_, 1 | 2 | 10 | 11, y : 3 | 12, _} -> 2 + y,
	{_, x : 0 | 1 | 9 | 10, y : 4 | 13, _} -> 3 + y - Mod[x, 9],
	{_, 7 | 16, y : 2 | 11, 6 | 15} -> 1 + y,
	{_, 7 | 16, y_, _} -> 7 + Floor[y, 9],
	{_, _, y : 7 | 16, z : 1 | 2 | 10 | 11} -> -7 + y + Mod[z, 9],
	{_, _, y : 5 | 6 | 14 | 15, _} -> 7 + Floor[y, 9] - Mod[y, 9],
	{_, 5 | 6 | 14 | 15, y : 1 | 2 | 10 | 11, _} -> 7 + Floor[y, 9] - Mod[y, 9],
	{_, 5 | 6 | 14 | 15, y : 0 | 9, 0 | 9} -> 1 + y,
	{_, _, y : 1 | 2 | 10 | 11, _} -> Floor[y, 9] + Mod[y, 9],
	{_, _, y : 8 | 17, _} -> y,
	{_, _, y_, _} -> Floor[y, 9]
}

data[2, 1] = {
	0 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	}
}

data[2, 2] = {
	0 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	8 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	10 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	}
}

data[2, 3] = {
	0 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	8 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	9 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	10 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	11 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	12 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	13 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	14 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	15 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	18 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	19 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	22 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	23 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	24 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	25 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	26 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	27 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	28 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	29 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	30 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	32 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	33 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	34 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	35 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	36 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	37 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	38 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	40 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	41 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	42 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	43 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	44 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	45 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	46 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	50 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	51 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	54 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	56 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	57 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	58 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	60 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	62 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	72 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	73 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	74 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	76 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	77 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	78 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	90 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	94 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	104 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	105 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	106 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{1, 1}, 0} -> {
			"BoundaryWordCoding" -> {
				"A" -> {1},
				"B" -> {1},
				"C" -> {0},
				"D" -> {1}
			},
			"BoundaryWordMorphism" -> {
				"A" -> "ABCD",
				"B" -> "CCAB",
				"C" -> "CCCC",
				"D" -> "CCCD"
			},
			"GrowthExponent" -> 1/2
		}
	},
	108 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	110 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	122 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	126 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	128 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	130 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	132 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	134 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	136 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	138 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	140 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	142 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	146 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	150 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	152 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	154 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	156 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	160 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	162 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	164 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	168 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	170 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	172 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	178 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	184 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	200 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	204 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	232 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	}
}

data[2, 4] = {
	0 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	8 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	9 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	10 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	11 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	12 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	13 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	14 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	15 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	18 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	19 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	20 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	21 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	22 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	23 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	24 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	25 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	26 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	27 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	28 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	29 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	30 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	31 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	32 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	33 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	34 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	35 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	36 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	37 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	38 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	39 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	40 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	41 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	42 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	43 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	44 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	45 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	46 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	47 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	48 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	49 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	50 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	51 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	52 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	53 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	54 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	55 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	56 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	57 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	58 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	59 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	60 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	61 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	62 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	63 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	64 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	65 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	66 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	67 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	68 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	69 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	70 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	71 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	72 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	73 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	74 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	75 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	76 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	77 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	78 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	79 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	82 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	83 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	84 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	85 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	86 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	87 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	88 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	89 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	90 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	91 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	92 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	93 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	94 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	95 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	96 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	97 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	98 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	99 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	100 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	101 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	102 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	103 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	104 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	105 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	106 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	107 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	108 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	109 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	110 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	111 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	112 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	113 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	114 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	115 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	116 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	117 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	118 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	119 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	120 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	121 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	122 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	123 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	124 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	125 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	126 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	127 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	128 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	129 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	130 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	131 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	132 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	133 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	134 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	135 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	136 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	137 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	138 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	139 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	140 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	141 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	142 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	143 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	144 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	145 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	146 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	147 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	148 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	149 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	150 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		}
	},
	151 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	152 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	153 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	154 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	155 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	156 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	157 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	158 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	159 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	160 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	161 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	162 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	163 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	164 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	165 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	166 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	167 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	168 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	169 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	170 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	171 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	172 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	173 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	174 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	175 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	176 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	177 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	178 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	179 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	180 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	181 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	182 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	183 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	184 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	185 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	186 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	187 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	188 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	189 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	190 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	191 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	192 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	193 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	194 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	195 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	196 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	197 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	198 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	199 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	200 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	201 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	202 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	203 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	204 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	205 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 1
		}
	},
	206 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	207 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	208 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	209 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	210 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	211 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	212 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	213 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	214 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	215 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	216 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	217 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	218 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	219 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	220 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	221 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	222 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	223 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	224 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	225 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	226 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	227 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	228 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	229 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	230 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	231 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	232 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	233 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 11/8
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 11/8
		}
	},
	234 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	235 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	236 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	237 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 1
		}
	},
	238 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	239 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	240 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	241 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	242 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	243 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	244 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	245 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	246 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	247 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	248 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	249 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	250 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	251 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	252 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	253 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	254 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	255 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	258 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	259 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	262 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	263 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	264 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	265 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	266 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	267 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	268 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	269 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	270 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	271 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	278 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	279 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	280 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	281 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	282 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	283 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	284 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	285 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	286 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	287 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	288 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	289 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	290 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	291 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	292 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	293 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	294 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	295 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	296 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	297 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	298 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	299 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	300 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	301 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	302 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	303 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	304 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	305 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	306 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	307 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	308 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	309 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	310 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	311 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	312 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	313 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	314 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	315 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	316 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	317 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	318 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	319 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	322 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	323 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	326 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	327 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	328 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	329 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	330 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	331 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	332 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	333 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	334 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	335 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	342 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	343 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	344 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	345 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	346 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	347 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	348 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	349 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	350 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	351 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	352 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	353 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	354 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	355 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	356 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (3.7949608161119985 + 1.782372730563723*#1 & ),
					"AdjustedRSquared" -> 0.9999991018076808,
					"AIC" -> 60071.613488446215,
					"ProbMinInfoLoss" -> 4.2344343488917717*^-85,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7827000000000002,
			"Diffusivity" -> 0.17005345263472135,
			"PecletNumber" -> 10.48317439240284,
			"Randomness" -> 0.09539095340479124
		}
	},
	357 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	358 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	359 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	360 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	361 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	362 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	363 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	364 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	365 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	366 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	367 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	368 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	369 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	370 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	371 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	372 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	373 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	374 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	375 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	376 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	377 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	378 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	379 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	380 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	381 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	382 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	383 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	384 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	385 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	386 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	387 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	388 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	389 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	390 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	391 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	392 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	393 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	394 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	395 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	396 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	397 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	398 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	399 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	400 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	401 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	402 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	403 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	404 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	405 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	406 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	407 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	408 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	409 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	410 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	411 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	412 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	413 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	414 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	415 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	416 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	417 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	418 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	419 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	420 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	421 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	422 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	423 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	424 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	425 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	426 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	427 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	428 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	429 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	430 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	431 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	432 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	433 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	434 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	435 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	436 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	437 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	438 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	439 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	440 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	441 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	442 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	443 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	444 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	445 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	446 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	447 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	448 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	449 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	450 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	451 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	452 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	453 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	454 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	455 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	456 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	457 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (2.081711251129746 + 1.2634225154982242*#1 & ),
					"AdjustedRSquared" -> 0.9999996982518404,
					"AIC" -> 42281.27002835551,
					"ProbMinInfoLoss" -> 0.06600899379606096,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.264,
			"Diffusivity" -> 0.6664303157661235,
			"PecletNumber" -> 1.896672420351878,
			"Randomness" -> 0.527239173865604
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.818594899508171 + 1.26342235878422*#1 & ),
					"AdjustedRSquared" -> 0.9999996983455464,
					"AIC" -> 42278.16162559571,
					"ProbMinInfoLoss" -> 0.05762652985264706,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2638,
			"Diffusivity" -> 0.6665359074415143,
			"PecletNumber" -> 1.8960718933374092,
			"Randomness" -> 0.5274061619255533
		}
	},
	458 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	459 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	460 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	461 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	462 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	463 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	464 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	465 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	466 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	467 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	468 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	469 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	470 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	471 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	472 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	473 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (31.776010932990555 + 0.3483913060146181*#1^1.0465480115506607 & ),
					"AdjustedRSquared" -> 0.9999606368382356,
					"AIC" -> 87538.9143275751,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0465480115506607
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.39842394094908945*#1^1.032453107349132 & ),
					"AdjustedRSquared" -> 0.9999534384207711,
					"AIC" -> 89217.36780416699,
					"ProbMinInfoLoss" -> 3.376435768934065462330315187177985826776`12.93223926712155*^-365,
					"Exponent" -> 1.032453107349132
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-48.11155235522777 + 0.5386950809629499*#1 & ),
					"AdjustedRSquared" -> 0.9996146889328814,
					"AIC" -> 96758.65737680274,
					"ProbMinInfoLoss" -> 9.083110075090316133429188703701084264836`12.29090094825662*^-2003,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.5367000000000001,
			"Diffusivity" -> 1.9012118855414246,
			"PecletNumber" -> 0.28229362759698895,
			"Randomness" -> 3.5424108171071818
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (31.272084877545282 + 0.34836809846803524*#1^1.046554216180158 & ),
					"AdjustedRSquared" -> 0.9999606216464504,
					"AIC" -> 87539.71422224937,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.046554216180158
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.39755869954648637*#1^1.0326806125257784 & ),
					"AdjustedRSquared" -> 0.9999536462239214,
					"AIC" -> 89169.57941685828,
					"ProbMinInfoLoss" -> 1.20024489535842109138963363318692978943064354858373`13.043468080259949*^-354,
					"Exponent" -> 1.0326806125257784
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-48.624968976890386 + 0.5386904447509038*#1 & ),
					"AdjustedRSquared" -> 0.9996146154773975,
					"AIC" -> 96760.39219597387,
					"ProbMinInfoLoss" -> 5.69138942116693078227574999095136738532`12.1436367873129*^-2003,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.5365,
			"Diffusivity" -> 1.9010264699204467,
			"PecletNumber" -> 0.28221595463762855,
			"Randomness" -> 3.543385778043703
		}
	},
	474 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	475 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	476 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	477 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	478 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	479 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	480 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	481 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	482 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	483 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	484 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (3.7949608161119985 + 1.782372730563723*#1 & ),
					"AdjustedRSquared" -> 0.9999991018076808,
					"AIC" -> 60071.613488446215,
					"ProbMinInfoLoss" -> 4.2344343488917717*^-85,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7827000000000002,
			"Diffusivity" -> 0.17005345263472135,
			"PecletNumber" -> 10.48317439240284,
			"Randomness" -> 0.09539095340479124
		}
	},
	485 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (12.1635840384051 + 0.758554947697548*#1 & ),
					"AdjustedRSquared" -> 0.999924970594813,
					"AIC" -> 87239.15627707055,
					"ProbMinInfoLoss" -> 6.669788131363921*^-237,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7606,
			"Diffusivity" -> 1.9722763634635119,
			"PecletNumber" -> 0.38564575132072837,
			"Randomness" -> 2.5930533308749824
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (11.402221542154733 + 0.7585551201795502*#1 & ),
					"AdjustedRSquared" -> 0.9999249694629547,
					"AIC" -> 87239.31169019478,
					"ProbMinInfoLoss" -> 2.3298475056464018*^-236,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7604000000000001,
			"Diffusivity" -> 1.9721805347168044,
			"PecletNumber" -> 0.38556307935023293,
			"Randomness" -> 2.593609330243036
		}
	},
	486 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	487 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	488 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	489 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.7353351335151823 + 1.006392613711926*#1 & ),
					"AdjustedRSquared" -> 0.9999679279070557,
					"AIC" -> 84394.03455577773,
					"ProbMinInfoLoss" -> 1.387073698726717737403481982016032070228254445547343`12.680759558054792*^-816,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0058,
			"Diffusivity" -> 1.5266716909738582,
			"PecletNumber" -> 0.6588187925056788,
			"Randomness" -> 1.5178680562476219
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.727115631568595 + 1.00639311756193*#1 & ),
					"AdjustedRSquared" -> 0.9999679286285513,
					"AIC" -> 84393.81959843794,
					"ProbMinInfoLoss" -> 4.08231675470890077937952407684716`12.681009183488785*^-816,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0056,
			"Diffusivity" -> 1.526673971658018,
			"PecletNumber" -> 0.6586868045623949,
			"Randomness" -> 1.518172207297154
		}
	},
	490 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	491 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	492 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	493 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 14,
			"GrowthRate" -> 3/7
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 14,
			"GrowthRate" -> 3/7
		}
	},
	494 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	495 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	496 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	497 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	498 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	499 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	500 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	501 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	502 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	503 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	504 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	505 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	506 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	507 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	508 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	509 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	510 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	512 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	513 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	514 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	515 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	516 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	517 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	518 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	519 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	520 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	521 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	522 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	523 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	524 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	525 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	526 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	527 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	530 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	531 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	532 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	533 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	534 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	535 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	536 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	537 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	538 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	539 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	540 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	541 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	542 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	543 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	544 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	545 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	546 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	547 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	548 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	549 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	550 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	551 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	552 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	553 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	554 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	555 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	556 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	557 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	558 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	559 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	560 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	561 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	562 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	563 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	564 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	565 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	566 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	567 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	568 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	569 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	570 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	571 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	572 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	573 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	574 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	575 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	576 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	577 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	578 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	579 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	580 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	581 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	582 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	583 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	584 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	585 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	586 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	587 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	588 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	589 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	590 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	591 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	594 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	595 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	596 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	597 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	598 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	599 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	600 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	601 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	602 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	603 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	604 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	605 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	606 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	607 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	608 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	609 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	610 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	611 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	612 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	613 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	614 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	615 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	616 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	617 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	618 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	619 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	620 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	621 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 1/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	622 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	623 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	624 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	625 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	626 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	627 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	628 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	629 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	630 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	631 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	632 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	633 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	634 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	635 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	636 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	637 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	638 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	640 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	641 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	642 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	643 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	644 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	645 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	646 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	647 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	648 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	649 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	650 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	651 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	652 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	653 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	654 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	655 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	656 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	657 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.5666586858441596 + 1.7938315085863124*#1 & ),
					"AdjustedRSquared" -> 0.9999994769735879,
					"AIC" -> 54792.254647652946,
					"ProbMinInfoLoss" -> 1.604864737232861368588962850529069`12.67131502338279*^-834,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7932000000000001,
			"Diffusivity" -> 1.5778864143665816,
			"PecletNumber" -> 1.1364569614599622,
			"Randomness" -> 0.8799277349802483
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-5.3592133813194245 + 1.7938313995363127*#1 & ),
					"AdjustedRSquared" -> 0.9999994769239426,
					"AIC" -> 54793.20258237915,
					"ProbMinInfoLoss" -> 1.38433233823349480575974197622722`12.525995655448993*^-835,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7929000000000002,
			"Diffusivity" -> 1.5780623271368945,
			"PecletNumber" -> 1.1361401696046374,
			"Randomness" -> 0.8801730866957969
		}
	},
	658 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	659 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	660 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	661 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	662 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 4/3
		}
	},
	663 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	664 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	665 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-94.74451425676489 + 1.4675882897696506*#1^0.9805338063753698 & ),
					"AdjustedRSquared" -> 0.9999749632538427,
					"AIC" -> 99639.91779246042,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9805338063753698
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-13.818024482444747 + 1.2225751873777522*#1 & ),
					"AdjustedRSquared" -> 0.9998570588613335,
					"AIC" -> 103231.35329357366,
					"ProbMinInfoLoss" -> 1.347999954496980906848150020021798633356909088487`12.7003516945461*^-780,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2165000000000001,
			"Diffusivity" -> 5.399302922890809,
			"PecletNumber" -> 0.2253068622696726,
			"Randomness" -> 4.438391223091498
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-95.90382497015561 + 1.4673733228140537*#1^0.9805495746960282 & ),
					"AdjustedRSquared" -> 0.9999749422375042,
					"AIC" -> 99645.32822566442,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9805495746960282
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-15.044062046191542 + 1.2225771146977689*#1 & ),
					"AdjustedRSquared" -> 0.999857075236544,
					"AIC" -> 103230.23900186327,
					"ProbMinInfoLoss" -> 3.5197830103870993851258482466565007620978201439087`12.503368876039612*^-779,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2162,
			"Diffusivity" -> 5.399132711830895,
			"PecletNumber" -> 0.22525840073073058,
			"Randomness" -> 4.439346087675461
		}
	},
	666 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	667 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	668 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	669 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	670 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	671 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	672 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	673 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	674 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	675 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	676 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	677 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	678 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	679 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	680 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	681 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	682 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	683 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	684 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	685 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	686 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	687 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	688 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	689 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	690 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	691 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	692 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	693 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	694 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	695 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	696 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	697 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	698 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	699 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	700 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	701 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	702 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	703 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	704 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	705 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	706 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	707 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	708 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	709 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	710 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	711 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	712 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	713 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	714 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	715 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	716 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	717 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 1
		}
	},
	718 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	719 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	720 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	721 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-2.9572741074039373 + 1.7978589089305874*#1 & ),
					"AdjustedRSquared" -> 0.9999998431302214,
					"AIC" -> 42794.944051881794,
					"ProbMinInfoLoss" -> 2.8421845521668095*^-45,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7977,
			"Diffusivity" -> 1.5662243159703049,
			"PecletNumber" -> 1.147792165955674,
			"Randomness" -> 0.8712378683708655
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-4.753276387644584 + 1.7978585894185866*#1 & ),
					"AdjustedRSquared" -> 0.9999998430790059,
					"AIC" -> 42798.204807185924,
					"ProbMinInfoLoss" -> 6.155917521705969*^-45,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7974,
			"Diffusivity" -> 1.5664029295508066,
			"PecletNumber" -> 1.147469764063475,
			"Randomness" -> 0.8714826580342754
		}
	},
	722 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	723 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	724 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	725 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	726 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 4/3
		}
	},
	727 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	728 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	729 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.8909844584704844 + 1.7479222108872183*#1 & ),
					"AdjustedRSquared" -> 0.9999992652285749,
					"AIC" -> 57673.01046908012,
					"ProbMinInfoLoss" -> 8.577375633613113*^-80,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7478,
			"Diffusivity" -> 1.6932778895012925,
			"PecletNumber" -> 1.0321991510293478,
			"Randomness" -> 0.9688052920822133
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.8573168916598662 + 1.7479223311452186*#1 & ),
					"AdjustedRSquared" -> 0.9999992652461754,
					"AIC" -> 57672.77230369496,
					"ProbMinInfoLoss" -> 1.0649587029235506*^-79,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7475,
			"Diffusivity" -> 1.6934265540976983,
			"PecletNumber" -> 1.0319313794693112,
			"Randomness" -> 0.9690566833177099
		}
	},
	730 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	731 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	732 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	733 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	734 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	735 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	736 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	737 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	738 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	739 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	740 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	741 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	742 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	743 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	744 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	745 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 3/2
		}
	},
	746 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	747 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	748 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	749 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (6.40606570657401 + 1.1912829785608285*#1 & ),
					"AdjustedRSquared" -> 0.9999841804084905,
					"AIC" -> 80699.67255808433,
					"ProbMinInfoLoss" -> 8.505421989899052*^-106,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1897,
			"Diffusivity" -> 3.9376978506012232,
			"PecletNumber" -> 0.30213085034402826,
			"Randomness" -> 3.3098241998833515
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (5.208171797192773 + 1.1912846371768433*#1 & ),
					"AdjustedRSquared" -> 0.9999841843886488,
					"AIC" -> 80697.18407983561,
					"ProbMinInfoLoss" -> 1.2618902427159078*^-105,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1894,
			"Diffusivity" -> 3.937511554716184,
			"PecletNumber" -> 0.3020689548391006,
			"Randomness" -> 3.310502400131313
		}
	},
	750 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	751 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	752 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	753 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	754 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	755 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	756 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	757 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	758 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	759 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	760 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	761 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	762 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	763 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	764 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	765 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	766 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	770 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	771 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	774 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	775 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	776 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	777 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	778 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	779 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	780 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	781 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	782 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	783 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	790 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	791 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	792 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	793 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	794 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	795 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	796 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	797 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	798 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	799 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	800 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	801 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	802 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	803 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	804 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	805 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	806 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	807 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	808 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	809 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	810 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	811 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	812 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	813 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	814 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	815 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	816 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	817 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	818 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	819 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	820 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	821 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	822 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	823 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	824 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	825 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	826 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	827 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	828 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	829 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	830 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	831 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	834 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	835 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	838 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	839 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	840 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	841 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	842 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	843 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	844 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	845 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	846 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	847 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	854 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	855 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	856 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	857 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	858 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	859 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	860 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	861 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	862 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	863 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	864 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	865 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	866 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	867 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	868 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.617996999709285 + 1.6205592246775913*#1 & ),
					"AdjustedRSquared" -> 0.9999994643358252,
					"AIC" -> 52999.358396409836,
					"ProbMinInfoLoss" -> 8.5565073782344007039472660764211522324762172676498`13.067241512445777*^-336,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6203,
			"Diffusivity" -> 0.2355365362501443,
			"PecletNumber" -> 6.87918751712987,
			"Randomness" -> 0.14536600398083335
		}
	},
	869 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	870 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	871 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	872 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	873 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	874 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	875 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	876 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	877 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	878 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	879 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	880 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	881 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	882 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	883 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	884 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	885 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	886 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	887 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	888 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	889 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	890 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	891 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	892 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	893 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	894 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	896 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	897 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	898 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	899 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	900 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	901 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	902 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	903 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	904 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	905 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	906 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	907 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	908 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	909 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	910 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	911 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	912 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	913 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	914 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	915 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	916 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	917 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	918 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	919 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	920 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	921 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	922 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	923 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	924 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	925 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	926 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	927 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	928 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	929 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	930 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	931 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	932 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	933 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	934 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	935 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	936 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	937 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	938 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	939 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	940 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	941 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	942 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	943 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	944 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	945 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	946 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	947 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	948 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	949 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	950 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	951 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	952 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	953 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	954 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	955 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	956 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	957 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	958 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	960 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	961 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	962 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	963 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	964 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	965 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	966 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	967 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	968 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	969 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 7/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 7/5
		}
	},
	970 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	971 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	972 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	973 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	974 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	975 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	976 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	977 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	978 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	979 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	980 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	981 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	982 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	983 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	984 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	985 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 44,
			"GrowthRate" -> 51/44
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 44,
			"GrowthRate" -> 51/44
		}
	},
	986 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	987 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	988 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	989 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	990 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	991 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	992 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	993 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	994 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	995 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	996 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 23,
			"GrowthRate" -> 38/23
		}
	},
	997 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	998 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	999 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1000 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1001 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1002 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1003 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1004 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1005 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	1006 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1007 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1008 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	1009 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	1010 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1011 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1012 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1013 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1014 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1015 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1016 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1017 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	1018 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1019 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1020 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1021 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1022 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1032 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1033 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1034 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1035 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1036 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1037 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1038 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1039 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1048 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1049 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1050 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1051 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1052 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1053 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1054 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1055 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1056 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1057 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1058 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1059 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1060 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1061 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1062 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1063 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1064 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1065 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 56,
			"GrowthRate" -> 15/14
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1066 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1067 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1068 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1069 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1070 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1071 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1074 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1075 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1076 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1077 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1078 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1079 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1080 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1081 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1082 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1083 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1084 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1085 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1086 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1096 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1097 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1098 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1099 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1100 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1101 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1102 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1103 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1112 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1113 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1114 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 9/5
		}
	},
	1115 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1116 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1117 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1118 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1119 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1120 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1121 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1122 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1123 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1124 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1125 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1126 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1127 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1128 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1129 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 9/10
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1130 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1131 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1132 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1133 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1134 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1135 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1138 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1139 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1140 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1141 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1142 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1143 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1144 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1145 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1146 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1147 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1148 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1149 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1150 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1152 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1153 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1154 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1155 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1156 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1157 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1158 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1159 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1160 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1161 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1162 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1163 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1164 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1165 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1166 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1167 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1168 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1169 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1170 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1171 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1172 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1173 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1174 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1175 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1176 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1177 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1178 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1179 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (34.843875527707844 + 0.4051415210447638*#1^1.0305344155809577 & ),
					"AdjustedRSquared" -> 0.9998526257388706,
					"AIC" -> 100929.960402556,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0305344155809577
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.46745692038425696*#1^1.015524462309473 & ),
					"AdjustedRSquared" -> 0.9998442972541957,
					"AIC" -> 101478.69433865945,
					"ProbMinInfoLoss" -> 6.98135558329125*^-120,
					"Exponent" -> 1.015524462309473
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-18.431912031200486 + 0.539299812424999*#1 & ),
					"AdjustedRSquared" -> 0.9993141783546262,
					"AIC" -> 102549.76918752969,
					"ProbMinInfoLoss" -> 1.832278449996560833248704089993144`13.04615601583838*^-352,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.5354,
			"Diffusivity" -> 1.8230898704993523,
			"PecletNumber" -> 0.29367723921001854,
			"Randomness" -> 3.4050987495318497
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (34.3195932906678 + 0.4051161587996175*#1^1.030541118451569 & ),
					"AdjustedRSquared" -> 0.9998525926189115,
					"AIC" -> 100929.22071387287,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.030541118451569
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.46643283182059275*#1^1.0157546224353007 & ),
					"AdjustedRSquared" -> 0.9998445092245458,
					"AIC" -> 101462.0845068563,
					"ProbMinInfoLoss" -> 1.950282620358402*^-116,
					"Exponent" -> 1.0157546224353007
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-18.967553555342025 + 0.5392998807229975*#1 & ),
					"AdjustedRSquared" -> 0.9993141804043678,
					"AIC" -> 102549.74181243045,
					"ProbMinInfoLoss" -> 1.283259666314932827337267892651732`12.9328099620608*^-352,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.5353,
			"Diffusivity" -> 1.8230969326178468,
			"PecletNumber" -> 0.2936212498758059,
			"Randomness" -> 3.4057480527140798
		}
	},
	1180 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1181 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1182 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1183 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1184 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1185 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1186 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1187 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1188 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1189 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1190 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1191 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1192 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1193 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1194 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1195 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1196 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1197 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1198 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1199 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1200 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1201 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	1202 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1203 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		}
	},
	1204 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1205 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1206 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1207 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1208 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1209 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1210 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1211 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (18.92690600916398 + 0.3823013748239512*#1^1.0263263523671444 & ),
					"AdjustedRSquared" -> 0.9999204434693276,
					"AIC" -> 92777.75338596143,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0263263523671444
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.41659880705902447*#1^1.0173107617246873 & ),
					"AdjustedRSquared" -> 0.9999175020573356,
					"AIC" -> 93139.80872624395,
					"ProbMinInfoLoss" -> 2.4026017321933038*^-79,
					"Exponent" -> 1.0173107617246873
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-22.916224962482524 + 0.48924306068642964*#1 & ),
					"AdjustedRSquared" -> 0.9996113567695497,
					"AIC" -> 94918.99322146067,
					"ProbMinInfoLoss" -> 1.085619175204963079889465825207514807`12.924954451479598*^-465,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.4929,
			"Diffusivity" -> 0.5000238771626713,
			"PecletNumber" -> 0.9857529260340628,
			"Randomness" -> 1.014452986737008
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (18.437201109543697 + 0.38234715049005186*#1^1.026312469299222 & ),
					"AdjustedRSquared" -> 0.9999204365546426,
					"AIC" -> 92775.53458678043,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.026312469299222
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.4157282676097956*#1^1.0175289265819405 & ),
					"AdjustedRSquared" -> 0.9999176443481791,
					"AIC" -> 93119.45811464005,
					"ProbMinInfoLoss" -> 2.0794803790619905*^-75,
					"Exponent" -> 1.0175289265819405
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-23.384000840069206 + 0.4892380563623795*#1 & ),
					"AdjustedRSquared" -> 0.9996114975601438,
					"AIC" -> 94915.16396368104,
					"ProbMinInfoLoss" -> 2.428757456794051588654082779111419915`12.925281213770617*^-465,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.4927,
			"Diffusivity" -> 0.4998209362844666,
			"PecletNumber" -> 0.9857530251985808,
			"Randomness" -> 1.0144528846853391
		}
	},
	1212 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1213 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1214 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1216 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1217 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1218 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1219 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1220 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1221 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1222 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	1223 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1224 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1225 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1226 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1227 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1228 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1229 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1230 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1231 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1232 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1233 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1234 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (3.7949608161119985 + 1.782372730563723*#1 & ),
					"AdjustedRSquared" -> 0.9999991018076808,
					"AIC" -> 60071.613488446215,
					"ProbMinInfoLoss" -> 4.2344343488917717*^-85,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7827000000000002,
			"Diffusivity" -> 0.17005345263472135,
			"PecletNumber" -> 10.48317439240284,
			"Randomness" -> 0.09539095340479124
		}
	},
	1235 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-21.833551815171965 + 1.3928023501280202*#1 & ),
					"AdjustedRSquared" -> 0.999978610770086,
					"AIC" -> 86841.85078843457,
					"ProbMinInfoLoss" -> 1.2099782202576441*^-24,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3887,
			"Diffusivity" -> 0.6305233043808481,
			"PecletNumber" -> 2.2024562618881394,
			"Randomness" -> 0.4540385283940722
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-23.221059885985454 + 1.3928021317640193*#1 & ),
					"AdjustedRSquared" -> 0.9999786098172773,
					"AIC" -> 86842.29311436853,
					"ProbMinInfoLoss" -> 7.265114275186506*^-25,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3885,
			"Diffusivity" -> 0.6306787910237313,
			"PecletNumber" -> 2.2015961528469306,
			"Randomness" -> 0.4542159099918842
		}
	},
	1236 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1237 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1238 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1239 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1240 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1241 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1242 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-2.45033675366547 + 1.6857750098497475*#1 & ),
					"AdjustedRSquared" -> 0.9999887782266,
					"AIC" -> 84209.58552086246,
					"ProbMinInfoLoss" -> 2.4597450284377036586533029184939297852640721244673`12.703454262505597*^-510,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.681,
			"Diffusivity" -> 0.29885238973987416,
			"PecletNumber" -> 5.6248504536409065,
			"Randomness" -> 0.17778250430688528
		}
	},
	1243 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1244 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1245 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1246 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1247 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1248 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1249 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1250 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1251 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	1252 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1253 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1254 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1255 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1256 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1257 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 4/3
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 4/3
		}
	},
	1258 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1259 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1260 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1261 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1262 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1263 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1264 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1265 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	1266 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1267 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1268 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1269 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1270 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1271 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1272 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1273 -> {
		{{1}, 0} -> {
			"BoundaryWordCoding" -> Missing["Unknown"],
			"BoundaryWordMorphism" -> Missing["Unknown"],
			"GrowthRate" -> 6/5
		},
		{{0}, 1} -> {
			"BoundaryWordCoding" -> Missing["Unknown"],
			"BoundaryWordMorphism" -> Missing["Unknown"],
			"GrowthRate" -> 6/5
		}
	},
	1274 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1275 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-14.175835883588881 + 0.4898886183148862*#1 & ),
					"AdjustedRSquared" -> 0.9997749502510064,
					"AIC" -> 89480.32668018909,
					"ProbMinInfoLoss" -> 7.176229816701569*^-104,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.4872,
			"Diffusivity" -> 0.6043307271315249,
			"PecletNumber" -> 0.8061810828526135,
			"Randomness" -> 1.2404161065917998
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-14.6621969996937 + 0.48988847055288326*#1 & ),
					"AdjustedRSquared" -> 0.999774946682671,
					"AIC" -> 89480.47923976825,
					"ProbMinInfoLoss" -> 3.7064282067192555*^-104,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.4872,
			"Diffusivity" -> 0.6043307271315249,
			"PecletNumber" -> 0.8061810828526135,
			"Randomness" -> 1.2404161065917998
		}
	},
	1276 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1277 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1278 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1288 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1289 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1290 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1291 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1292 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1293 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1294 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1295 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1304 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 20,
			"GrowthRate" -> 23/20
		}
	},
	1305 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1306 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1307 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1308 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1309 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1310 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1311 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1314 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1315 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1318 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1319 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1320 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1321 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1322 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1323 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1324 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1325 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1326 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1327 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1334 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1335 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1336 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/4
		}
	},
	1337 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1338 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1339 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1340 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1341 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1342 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1352 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1353 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1354 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1355 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1356 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1357 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1358 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1359 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1368 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1369 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1370 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1371 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1372 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1373 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1374 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1375 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1378 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1379 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1382 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1383 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1384 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1385 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1386 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1387 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1388 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1389 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1390 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1391 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1398 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1399 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1400 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1401 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1402 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1403 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1404 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1405 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1406 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1408 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1409 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1410 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1411 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1412 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1413 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1414 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1415 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1416 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1417 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1418 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1419 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1420 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1421 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1422 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1423 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1424 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1425 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1426 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1427 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1428 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1429 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1430 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1431 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1432 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 20,
			"GrowthRate" -> 5/4
		}
	},
	1433 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1434 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1435 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1436 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1437 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1438 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1439 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1440 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1441 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1442 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1443 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1444 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 7/4
		}
	},
	1445 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1446 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1447 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1448 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1449 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1450 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1451 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1452 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1453 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1454 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1455 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1456 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1457 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1458 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1459 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1460 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1461 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1462 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1463 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1464 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 9,
			"GrowthRate" -> 11/9
		}
	},
	1465 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1466 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1467 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1468 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1469 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1470 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1472 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1473 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1474 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1475 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1476 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1477 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1478 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1479 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1480 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1481 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-10.215278779456439 + 1.5801101448524597*#1^0.9889171116721693 & ),
					"AdjustedRSquared" -> 0.9999988718593011,
					"AIC" -> 71817.62014698845,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9889171116721693
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (42.99743168319286 + 1.4240842252408386*#1 & ),
					"AdjustedRSquared" -> 0.99998174052102,
					"AIC" -> 85704.01093141352,
					"ProbMinInfoLoss" -> 4.06026506126966865480510419845373706629264694348`12.028172623337257*^-3016,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4267,
			"Diffusivity" -> 0.39128715832175337,
			"PecletNumber" -> 3.6461712827969484,
			"Randomness" -> 0.2742602918074951
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-11.673541393719155 + 1.5801564485173194*#1^0.9889142532113734 & ),
					"AdjustedRSquared" -> 0.9999988711469211,
					"AIC" -> 71820.94888679916,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9889142532113734
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (41.55317953796069 + 1.4240877553168771*#1 & ),
					"AdjustedRSquared" -> 0.999981731858983,
					"AIC" -> 85708.8033275858,
					"ProbMinInfoLoss" -> 1.95310434147190522077937183403226165312003727282`12.112984609858287*^-3016,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4265,
			"Diffusivity" -> 0.39145784952570073,
			"PecletNumber" -> 3.6440704962957824,
			"Randomness" -> 0.2744184013499479
		}
	},
	1482 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1483 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1484 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1485 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1486 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1487 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1488 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	1489 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1490 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1491 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1492 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1493 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1494 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1495 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1496 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1497 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-13.014004680453802 + 0.6683966812679653*#1 & ),
					"AdjustedRSquared" -> 0.9998687977336012,
					"AIC" -> 90297.65031175387,
					"ProbMinInfoLoss" -> 1.1272627340424584*^-71,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6687000000000001,
			"Diffusivity" -> 1.6192531835700072,
			"PecletNumber" -> 0.4129681551872578,
			"Randomness" -> 2.4214942179901406
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-13.673585358516723 + 0.6683948775839463*#1 & ),
					"AdjustedRSquared" -> 0.9998687986743305,
					"AIC" -> 90297.52463087032,
					"ProbMinInfoLoss" -> 7.508800963866582*^-72,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6685,
			"Diffusivity" -> 1.619120583792726,
			"PecletNumber" -> 0.4128784518532061,
			"Randomness" -> 2.4220203198096124
		}
	},
	1498 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1499 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1500 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1501 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1502 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1504 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1505 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1506 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1507 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1508 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 7/4
		}
	},
	1509 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 7/6
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 7/6
		}
	},
	1510 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1511 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1512 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1513 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (2.996642664290849 + 1.04652137932921*#1 & ),
					"AdjustedRSquared" -> 0.9999919759990112,
					"AIC" -> 71320.2915884676,
					"ProbMinInfoLoss" -> 6.4439482112141795694590706646681747695036`12.719120029263735*^-730,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0474,
			"Diffusivity" -> 1.157984612223975,
			"PecletNumber" -> 0.9045025201055212,
			"Randomness" -> 1.105580114783249
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.9504808881110518 + 1.0465211517072084*#1 & ),
					"AdjustedRSquared" -> 0.9999919763192441,
					"AIC" -> 71319.88813340604,
					"ProbMinInfoLoss" -> 7.18154935125144661493161827678835242316718`12.730156936383464*^-729,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0472000000000001,
			"Diffusivity" -> 1.1580035379012996,
			"PecletNumber" -> 0.904315026444467,
			"Randomness" -> 1.1058093371861148
		}
	},
	1514 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1515 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1516 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1517 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 11/10
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 11/10
		}
	},
	1518 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1519 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1520 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	1521 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1522 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1523 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1524 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1525 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1526 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1527 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1528 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1529 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-22.031803201727467 + 0.3754813715322904*#1^0.9831272642254233 & ),
					"AdjustedRSquared" -> 0.9998826083297938,
					"AIC" -> 88315.54711644008,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9831272642254233
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.6915729372968786 + 0.32050506408105045*#1 & ),
					"AdjustedRSquared" -> 0.9994999697528856,
					"AIC" -> 88980.94869337016,
					"ProbMinInfoLoss" -> 3.235068230577757*^-145,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.3155,
			"Diffusivity" -> 1.3131755263944078,
			"PecletNumber" -> 0.24025729512814623,
			"Randomness" -> 4.162204521059929
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-22.322415859346286 + 0.37536496892709603*#1^0.9831611214549735 & ),
					"AdjustedRSquared" -> 0.9998826038158298,
					"AIC" -> 88313.01490695363,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9831611214549735
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-4.019475967598993 + 0.32050756443707523*#1 & ),
					"AdjustedRSquared" -> 0.9995002259051367,
					"AIC" -> 88975.97810850914,
					"ProbMinInfoLoss" -> 1.0948885895481159*^-144,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.3154,
			"Diffusivity" -> 1.3131385953158228,
			"PecletNumber" -> 0.24018789876794627,
			"Randomness" -> 4.163407087241036
		}
	},
	1530 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1531 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1532 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1533 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1534 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1544 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1545 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (34.09604536745554 + 0.7132500943693836*#1^1.0132006608436894 & ),
					"AdjustedRSquared" -> 0.9999888425722198,
					"AIC" -> 83284.59415221763,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0132006608436894
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.9682513651408957 + 0.8071921710559208*#1 & ),
					"AdjustedRSquared" -> 0.9999362569607629,
					"AIC" -> 86851.77288183694,
					"ProbMinInfoLoss" -> 2.4944849143397476540209472891109723`12.703294896117745*^-775,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8042,
			"Diffusivity" -> 6.170292584369459,
			"PecletNumber" -> 0.13033417605466452,
			"Randomness" -> 7.672584660991618
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1546 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1547 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1548 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1549 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1550 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1551 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1560 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1561 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1562 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1563 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1564 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1565 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1566 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1567 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1568 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1569 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1570 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1571 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1572 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1573 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1574 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1575 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1576 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1577 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-3.523626997101413 + 1.1472246743952996*#1^0.9867609519562036 & ),
					"AdjustedRSquared" -> 0.999993692114063,
					"AIC" -> 82255.36072376046,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9867609519562036
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.138846081443929*#1^0.9875284347099507 & ),
					"AdjustedRSquared" -> 0.9999936709531968,
					"AIC" -> 82287.85151570344,
					"ProbMinInfoLoss" -> 8.804692099050227*^-8,
					"Exponent" -> 0.9875284347099507
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (41.8016774677625 + 1.0132311813883101*#1 & ),
					"AdjustedRSquared" -> 0.999954835951191,
					"AIC" -> 87952.75955836823,
					"ProbMinInfoLoss" -> 6.692100645894943054364618592743751`12.499943143448235*^-1238,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0183,
			"Diffusivity" -> 4.703705817671185,
			"PecletNumber" -> 0.2164888790821877,
			"Randomness" -> 4.619174916695655
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1578 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1579 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1580 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1581 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1582 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1583 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1586 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1587 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1588 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1589 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1590 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1591 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1592 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1593 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1594 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1595 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1596 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1597 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1598 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1608 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1609 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-35.872009766278495 + 0.8026412841342779*#1^0.9706112252864773 & ),
					"AdjustedRSquared" -> 0.9999695618083614,
					"AIC" -> 87820.02135202619,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9706112252864773
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.7105306209802663*#1^0.9833619972292096 & ),
					"AdjustedRSquared" -> 0.9999634011338316,
					"AIC" -> 89662.21297308855,
					"ProbMinInfoLoss" -> 9.400959508435881972802831013998278809754541`12.948674978207379*^-401,
					"Exponent" -> 0.9833619972292096
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (25.624211221127776 + 0.6091356841873563*#1 & ),
					"AdjustedRSquared" -> 0.9997780258145224,
					"AIC" -> 93699.9517220554,
					"ProbMinInfoLoss" -> 1.546475914454627065378638650843509`12.486247582651492*^-1277,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6066,
			"Diffusivity" -> 7.237268415779366,
			"PecletNumber" -> 0.08381615343676273,
			"Randomness" -> 11.930874407813
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1610 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1611 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1612 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1613 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1614 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1615 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1624 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1625 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1626 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1627 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1628 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1629 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1630 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1632 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1633 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1634 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1635 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1636 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1637 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1638 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1639 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1640 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1641 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-155.76615379343667 + 1.0227916874723575*#1^1.0398379433711218 & ),
					"AdjustedRSquared" -> 0.9999712564503703,
					"AIC" -> 104242.07761709589,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0398379433711218
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.8039811498596832*#1^1.0651172441825667 & ),
					"AdjustedRSquared" -> 0.9999464596004737,
					"AIC" -> 110461.30905626029,
					"ProbMinInfoLoss" -> 3.243785632212372638367118803441448649`12.461883047137334*^-1351,
					"Exponent" -> 1.0651172441825667
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-345.48110885085373 + 1.4852911726529057*#1 & ),
					"AdjustedRSquared" -> 0.999717968946432,
					"AIC" -> 113921.61461925578,
					"ProbMinInfoLoss" -> 1.30390602414909166555929938951986404`12.26976518150279*^-2102,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4555,
			"Diffusivity" -> 2.483895779055801,
			"PecletNumber" -> 0.585974666196855,
			"Randomness" -> 1.7065584191383036
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1642 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1643 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1644 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1645 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1646 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1647 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1650 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1651 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1652 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1653 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1654 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1655 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1656 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1657 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (60.64244920491795 + 0.582825707588257*#1 & ),
					"AdjustedRSquared" -> 0.999806673674776,
					"AIC" -> 91434.79278351988,
					"ProbMinInfoLoss" -> 1.820967973696132*^-36,
					"Exponent" -> 1
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.7185526393431202*#1^0.9781581111967087 & ),
					"AdjustedRSquared" -> 0.9999275905903258,
					"AIC" -> 95786.84637530637,
					"ProbMinInfoLoss" -> 1.674450747415840561847267528344382425781`12.4616167102365*^-981,
					"Exponent" -> 0.9781581111967087
				}
			},
			"GrowthRate" -> 0.5918,
			"Diffusivity" -> 8.29421493859728,
			"PecletNumber" -> 0.07135093608993033,
			"Randomness" -> 14.015233083131598
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1658 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1659 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1660 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1661 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1662 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1664 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1665 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1666 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1667 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1668 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1669 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1670 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1671 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	1672 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1673 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1674 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1675 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1676 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1677 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1678 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1679 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1680 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1681 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1682 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1683 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1684 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1685 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1686 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1687 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1688 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1689 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-20.90308934894158 + 1.7196411337564124*#1 & ),
					"AdjustedRSquared" -> 0.9999944919908956,
					"AIC" -> 77490.80570658507,
					"ProbMinInfoLoss" -> 9.4784710552069837175032671773192462715608380656`12.648868059549846*^-879,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.719,
			"Diffusivity" -> 2.0798032593817495,
			"PecletNumber" -> 0.8265204856496844,
			"Randomness" -> 1.209891366714223
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-22.611070026985256 + 1.719638950110386*#1 & ),
					"AdjustedRSquared" -> 0.9999944908838758,
					"AIC" -> 77492.78995581459,
					"ProbMinInfoLoss" -> 2.8250815797633847000174023655857625728033089851`12.648608108060195*^-879,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7187000000000001,
			"Diffusivity" -> 2.079934638792945,
			"PecletNumber" -> 0.8263240430465733,
			"Randomness" -> 1.2101789950502966
		}
	},
	1690 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (28.918006094612963 + 0.4235148738512104*#1^0.9589702242166787 & ),
					"AdjustedRSquared" -> 0.9998131762521802,
					"AIC" -> 91585.67960213825,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9589702242166787
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.5174942750883573*#1^0.9380285000806508 & ),
					"AdjustedRSquared" -> 0.9997975643288353,
					"AIC" -> 92387.24500666946,
					"ProbMinInfoLoss" -> 8.755560711044964*^-175,
					"Exponent" -> 0.9380285000806508
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (70.01412391239604 + 0.28809468574894653*#1 & ),
					"AdjustedRSquared" -> 0.9990077503235963,
					"AIC" -> 93706.75820259935,
					"ProbMinInfoLoss" -> 2.5919944562752976404083080174241735522153`12.929063003460989*^-461,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.2904,
			"Diffusivity" -> 1.3794933804242597,
			"PecletNumber" -> 0.21051206487898347,
			"Randomness" -> 4.750321557934779
		}
	},
	1691 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1692 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1693 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1694 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1695 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1696 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1697 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1698 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1699 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1700 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1701 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-12.089138853874758 + 1.5971127964911263*#1 & ),
					"AdjustedRSquared" -> 0.9999820377207812,
					"AIC" -> 87833.27492303216,
					"ProbMinInfoLoss" -> 6.138713198578376855414276132505416554359662872`12.618070388084154*^-803,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5974000000000002,
			"Diffusivity" -> 2.6940163510249806,
			"PecletNumber" -> 0.5929436914487339,
			"Randomness" -> 1.686500783163253
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-13.6780228622671 + 1.5971111134611076*#1 & ),
					"AdjustedRSquared" -> 0.9999820379310901,
					"AIC" -> 87833.1367606804,
					"ProbMinInfoLoss" -> 9.961675550148242990326214551055066385270149434`12.688198810175109*^-803,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5971000000000002,
			"Diffusivity" -> 2.694074748543068,
			"PecletNumber" -> 0.5928194831504574,
			"Randomness" -> 1.6868541409699251
		}
	},
	1702 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1703 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1704 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1705 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1706 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1707 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1708 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1709 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1710 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1711 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1712 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1713 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1714 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1715 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		}
	},
	1716 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1717 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1718 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1719 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1720 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1721 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1722 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1723 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (35.32929927693072 + 0.7024312312720894*#1^0.9803955411766889 & ),
					"AdjustedRSquared" -> 0.9999320403541212,
					"AIC" -> 95276.3711453623,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9803955411766889
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.796279636937889*#1^0.9672713680742709 & ),
					"AdjustedRSquared" -> 0.9999258594959514,
					"AIC" -> 96145.8504978986,
					"ProbMinInfoLoss" -> 1.5665978721995785*^-189,
					"Exponent" -> 0.9672713680742709
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (74.29153663367006 + 0.5844017924940159*#1 & ),
					"AdjustedRSquared" -> 0.9996750714148239,
					"AIC" -> 96682.37883006597,
					"ProbMinInfoLoss" -> 4.8900185862247525*^-306,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.5905,
			"Diffusivity" -> 0.4644858764732244,
			"PecletNumber" -> 1.2712980736542154,
			"Randomness" -> 0.7865975892857314
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (34.6541442072108 + 0.702627609557599*#1^0.9803667190173276 & ),
					"AdjustedRSquared" -> 0.9999320069104622,
					"AIC" -> 95278.34223456979,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9803667190173276
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.7946074141069538*#1^0.9674917727240898 & ),
					"AdjustedRSquared" -> 0.9999260573812071,
					"AIC" -> 96116.17543589187,
					"ProbMinInfoLoss" -> 1.1663582221718723*^-182,
					"Exponent" -> 0.9674917727240898
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (73.67515553555687 + 0.5844069881940689*#1 & ),
					"AdjustedRSquared" -> 0.999674894869074,
					"AIC" -> 96687.99030302263,
					"ProbMinInfoLoss" -> 7.921569241508772*^-307,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.5904,
			"Diffusivity" -> 0.4645039618984903,
			"PecletNumber" -> 1.271033292346863,
			"Randomness" -> 0.7867614530800987
		}
	},
	1724 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1725 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1726 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1728 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1729 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1730 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1731 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1732 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1733 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1734 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	1735 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	1736 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1737 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (44.14851926289246 + 0.9306063189214663*#1^1.0139366595062729 & ),
					"AdjustedRSquared" -> 0.9999852782758373,
					"AIC" -> 91505.8185815549,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0139366595062729
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-4.450852565236857 + 1.06046340417263*#1 & ),
					"AdjustedRSquared" -> 0.9999198385063022,
					"AIC" -> 94601.75978095042,
					"ProbMinInfoLoss" -> 5.3077493131046011176689759252036282326031`12.764827062235781*^-673,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0641,
			"Diffusivity" -> 5.28824842876366,
			"PecletNumber" -> 0.2012197449371296,
			"Randomness" -> 4.9696912214675875
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (43.062342161050786 + 0.9306949750973375*#1^1.0139262115645675 & ),
					"AdjustedRSquared" -> 0.9999852701421797,
					"AIC" -> 91508.31763102881,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0139262115645675
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-5.500969816980652 + 1.060460627900606*#1 & ),
					"AdjustedRSquared" -> 0.9999198555541857,
					"AIC" -> 94599.58033225659,
					"ProbMinInfoLoss" -> 5.50596405357908302104763217987124366961282`12.76548385207421*^-672,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0638,
			"Diffusivity" -> 5.287986750265345,
			"PecletNumber" -> 0.20117297002429513,
			"Randomness" -> 4.970846728957834
		}
	},
	1738 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1739 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1740 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1741 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1742 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1743 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1744 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1745 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-20.33682742273552 + 1.2785523502495224*#1 & ),
					"AdjustedRSquared" -> 0.9999934521919925,
					"AIC" -> 73292.34386094777,
					"ProbMinInfoLoss" -> 2.5174811623559567*^-25,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2751000000000001,
			"Diffusivity" -> 4.44890220168246,
			"PecletNumber" -> 0.2866100314629956,
			"Randomness" -> 3.489061408267948
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-21.609683228309738 + 1.2785519214535168*#1 & ),
					"AdjustedRSquared" -> 0.9999934503239211,
					"AIC" -> 73295.18973790765,
					"ProbMinInfoLoss" -> 7.318107812495966*^-25,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2748000000000002,
			"Diffusivity" -> 4.448767161173008,
			"PecletNumber" -> 0.2865512969808636,
			"Randomness" -> 3.4897765619493315
		}
	},
	1746 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.08195553557481619 + 1.609836865206364*#1 & ),
					"AdjustedRSquared" -> 0.9999997762241566,
					"AIC" -> 44137.96070052548,
					"ProbMinInfoLoss" -> 2.491993457666913904824437605999110101332240053189`12.456347527683612*^-1068,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6094000000000002,
			"Diffusivity" -> 0.2380421078715193,
			"PecletNumber" -> 6.76098869393585,
			"Randomness" -> 0.14790736166988894
		}
	},
	1747 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 14,
			"GrowthRate" -> 15/14
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 14,
			"GrowthRate" -> 15/14
		}
	},
	1748 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1749 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1750 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1751 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1752 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1753 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (11.185693189354499 + 1.575684772884843*#1 & ),
					"AdjustedRSquared" -> 0.9999893776159833,
					"AIC" -> 82309.9458174102,
					"ProbMinInfoLoss" -> 1.1892748662413838*^-135,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5774000000000001,
			"Diffusivity" -> 2.4318622700437675,
			"PecletNumber" -> 0.6486387076401374,
			"Randomness" -> 1.541690294182685
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (9.607127812808033 + 1.5756850259348476*#1 & ),
					"AdjustedRSquared" -> 0.9999893772901409,
					"AIC" -> 82310.2557786121,
					"ProbMinInfoLoss" -> 3.058449850644076*^-135,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5771000000000002,
			"Diffusivity" -> 2.431908663961015,
			"PecletNumber" -> 0.6485029735579256,
			"Randomness" -> 1.5420129756902003
		}
	},
	1754 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (15.499846204640932 + 1.2848124095181221*#1 & ),
					"AdjustedRSquared" -> 0.999973013440198,
					"AIC" -> 87552.31964554683,
					"ProbMinInfoLoss" -> 7.911175818682209*^-265,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2851000000000001,
			"Diffusivity" -> 0.8757850179896965,
			"PecletNumber" -> 1.467369244280814,
			"Randomness" -> 0.6814917267058567
		}
	},
	1755 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 14,
			"GrowthRate" -> 15/14
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 14,
			"GrowthRate" -> 15/14
		}
	},
	1756 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1757 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1758 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1760 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1761 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1762 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1763 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	1764 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1765 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1766 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1767 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1768 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1769 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1770 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1771 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1772 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1773 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1774 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1775 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1776 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1777 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1778 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1779 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1780 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1781 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1782 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1783 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1784 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1785 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	1786 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1787 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (4.395363542384138 + 0.5268708625003364*#1^1.0130245678185028 & ),
					"AdjustedRSquared" -> 0.9999848113397195,
					"AIC" -> 80175.50405132303,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0130245678185028
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.5354426547293375*#1^1.0113323399729923 & ),
					"AdjustedRSquared" -> 0.9999847071602277,
					"AIC" -> 80242.86044998019,
					"ProbMinInfoLoss" -> 2.364524787732354*^-15,
					"Exponent" -> 1.0113323399729923
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-21.12302478248283 + 0.5952820367528198*#1 & ),
					"AdjustedRSquared" -> 0.9999212338125164,
					"AIC" -> 82877.6320215964,
					"ProbMinInfoLoss" -> 1.7392682013528446054964539510676709694627707684738`12.796125461114485*^-587,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.5944,
			"Diffusivity" -> 0.6612044281043428,
			"PecletNumber" -> 0.8989655464107078,
			"Randomness" -> 1.1123896838902132
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (3.819043764925379 + 0.5268492793402957*#1^1.0130285699512005 & ),
					"AdjustedRSquared" -> 0.9999848067078001,
					"AIC" -> 80175.5300507091,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0130285699512005
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.5342900697508897*#1^1.0115579990238655 & ),
					"AdjustedRSquared" -> 0.9999847283878449,
					"AIC" -> 80225.94692545416,
					"ProbMinInfoLoss" -> 1.1274953299155363*^-11,
					"Exponent" -> 1.0115579990238655
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-21.70699633962941 + 0.5952799712707972*#1 & ),
					"AdjustedRSquared" -> 0.9999212218304706,
					"AIC" -> 82879.08384743762,
					"ProbMinInfoLoss" -> 8.526136399151198537266821360545809372037968192752`12.823684750038444*^-588,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.5944,
			"Diffusivity" -> 0.6612044281043428,
			"PecletNumber" -> 0.8989655464107078,
			"Randomness" -> 1.1123896838902132
		}
	},
	1788 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1789 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1790 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1800 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1801 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1802 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1803 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1804 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1805 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1806 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1807 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1816 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1817 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1818 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1819 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1820 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1821 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1822 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1823 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1826 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1827 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1830 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1831 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1832 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1833 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.2531938793978771 + 0.7706615750666144*#1 & ),
					"AdjustedRSquared" -> 0.9999561837059759,
					"AIC" -> 82176.78259114994,
					"ProbMinInfoLoss" -> 9.675141141978794*^-38,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7712,
			"Diffusivity" -> 2.0788610967518037,
			"PecletNumber" -> 0.3709723565489734,
			"Randomness" -> 2.6956186420536876
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1834 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1835 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1836 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1837 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1838 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1839 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1846 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1847 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1848 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1849 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1850 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1851 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1852 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1853 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1854 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1864 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1865 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1866 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1867 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1868 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1869 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1870 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1871 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1880 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1881 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1882 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1883 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1884 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1885 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1886 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1890 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1891 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1894 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1895 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1896 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1897 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1898 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1899 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1900 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1901 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1902 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1903 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1910 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1911 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1912 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1913 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1914 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1915 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1916 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1917 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1918 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1920 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1921 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1922 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1923 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	1924 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1925 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1926 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1927 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1928 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1929 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1930 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1931 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1932 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1933 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1934 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1935 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1936 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1937 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 7/10
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 7/10
		}
	},
	1938 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1939 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1940 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1941 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1942 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1943 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1944 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1945 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1946 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1947 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1948 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1949 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1950 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1952 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1953 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1954 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1955 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	1956 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 5/3
		}
	},
	1957 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1958 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1959 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1960 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1961 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1962 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1963 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1964 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1965 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1966 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1967 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1968 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1969 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1970 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1971 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1972 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1973 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1974 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1975 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1976 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1977 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1978 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1979 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1980 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1981 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1982 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1984 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1985 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1986 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1987 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	1988 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1989 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1990 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1991 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1992 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	1993 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1994 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1995 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	1996 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	1997 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	1998 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	1999 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2000 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-32.081132853276806 + 0.6006265239182639*#1 & ),
					"AdjustedRSquared" -> 0.9999633648836974,
					"AIC" -> 75401.2052788963,
					"ProbMinInfoLoss" -> 2.271957074468488*^-154,
					"Exponent" -> 1
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.5293795951091569*#1^1.0133168017951126 & ),
					"AdjustedRSquared" -> 0.9999885699274262,
					"AIC" -> 77456.12320490016,
					"ProbMinInfoLoss" -> 1.369752519497533105647660207904069467`12.71164336355906*^-600,
					"Exponent" -> 1.0133168017951126
				}
			},
			"GrowthRate" -> 0.5968,
			"Diffusivity" -> 0.41069564047823065,
			"PecletNumber" -> 1.4531442293983492,
			"Randomness" -> 0.6881629364581613
		}
	},
	2001 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (14.64583594360651 + 0.7797101817931003*#1 & ),
					"AdjustedRSquared" -> 0.9999712741060304,
					"AIC" -> 78188.022656482,
					"ProbMinInfoLoss" -> 5.502786773792577*^-196,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7838,
			"Diffusivity" -> 0.16948678264505787,
			"PecletNumber" -> 4.6245494059642835,
			"Randomness" -> 0.21623728329300568
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (13.86591947195557 + 0.7797094251630933*#1 & ),
					"AdjustedRSquared" -> 0.999971283982831,
					"AIC" -> 78184.5642667277,
					"ProbMinInfoLoss" -> 5.730532169925328*^-195,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7838,
			"Diffusivity" -> 0.16948678264505787,
			"PecletNumber" -> 4.6245494059642835,
			"Randomness" -> 0.21623728329300568
		}
	},
	2002 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2003 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2004 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2005 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2006 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2007 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2008 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2009 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 24,
			"GrowthRate" -> 29/24
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 24,
			"GrowthRate" -> 29/24
		}
	},
	2010 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2011 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2012 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2013 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2014 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2016 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2017 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2018 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2019 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.8144039004039952 + 0.9715944797719425*#1 & ),
					"AdjustedRSquared" -> 0.9999907762495974,
					"AIC" -> 71227.9799661097,
					"ProbMinInfoLoss" -> 2.0092723551102757*^-142,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9732000000000001,
			"Diffusivity" -> 0.02608690554992687,
			"PecletNumber" -> 37.30607289306218,
			"Randomness" -> 0.026805287248178034
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.15406726672023072 + 0.9715935540979347*#1 & ),
					"AdjustedRSquared" -> 0.999990779185776,
					"AIC" -> 71224.77709462901,
					"ProbMinInfoLoss" -> 4.161168438497555*^-142,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9731000000000001,
			"Diffusivity" -> 0.026181553942551686,
			"PecletNumber" -> 37.167388999721105,
			"Randomness" -> 0.026905306692582145
		}
	},
	2020 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.049536453658948 + 1.660649907718497*#1 & ),
					"AdjustedRSquared" -> 0.9999998510341337,
					"AIC" -> 40690.207145860804,
					"ProbMinInfoLoss" -> 1.2037752161754164*^-48,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6609,
			"Diffusivity" -> 0.22411232921651836,
			"PecletNumber" -> 7.411015742892838,
			"Randomness" -> 0.13493427010447248
		}
	},
	2021 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2022 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2023 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2024 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2025 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2026 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2027 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2028 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2029 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 7/6
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 7/6
		}
	},
	2030 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2031 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2032 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	2033 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2034 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2035 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2036 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2037 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2038 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2039 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2040 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2041 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2042 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2043 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2044 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2045 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2046 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2048 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2049 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2050 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2051 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2052 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2053 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2054 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2055 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2056 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2057 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2058 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2059 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2060 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2061 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2062 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2063 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2064 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2065 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2066 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2067 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2068 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2069 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2070 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2071 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2072 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2073 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2074 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2075 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2076 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2077 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2078 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2080 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2081 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2082 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2083 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2084 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2085 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2086 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2087 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2088 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2089 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2090 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2091 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2092 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2093 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2094 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2095 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2096 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2097 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2098 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2099 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2100 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2101 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2102 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2103 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2104 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2105 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1/2
		}
	},
	2106 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2107 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2108 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2109 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2110 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2112 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2113 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2114 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2115 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2116 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2117 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2118 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2119 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2120 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2121 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2122 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2123 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2124 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2125 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2126 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2127 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2128 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2129 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2130 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2131 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2132 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2133 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 14,
			"GrowthRate" -> 15/14
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 14,
			"GrowthRate" -> 15/14
		}
	},
	2134 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2135 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2136 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2137 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2138 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2139 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2140 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2141 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2142 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2144 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2145 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2146 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2147 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2148 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2149 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2150 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2151 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2152 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2153 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2154 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2155 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2156 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2157 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2158 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2159 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2160 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2161 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2162 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2163 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2164 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2165 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2166 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2167 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2168 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2169 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2170 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2171 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2172 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2173 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2174 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2176 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2177 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2178 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2179 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2180 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2181 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2182 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2183 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2184 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2185 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2186 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2187 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2188 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2189 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2190 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2191 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2192 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2193 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2194 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2195 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2196 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2197 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2198 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-27.228205400540904 + 0.8881442866514425*#1 & ),
					"AdjustedRSquared" -> 0.9999569763192426,
					"AIC" -> 84831.92148862462,
					"ProbMinInfoLoss" -> 2.322229935362281*^-39,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8869,
			"Diffusivity" -> 1.818670844880047,
			"PecletNumber" -> 0.48766383565053345,
			"Randomness" -> 2.0505929021085207
		}
	},
	2199 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2200 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2201 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2202 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2203 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2204 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2205 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2206 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2208 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2209 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2210 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2211 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2212 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2213 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2214 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2215 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2216 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2217 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 4/3
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2218 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2219 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2220 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2221 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2222 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2223 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2224 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2225 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2226 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2227 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2228 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2229 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2230 -> {
		{{1}, 0} -> {
			"BoundaryWordCoding" -> {
				"A" -> {},
				"B" -> {2},
				"C" -> {0}
			},
			"BoundaryWordMorphism" -> {
				"A" -> "ABCB",
				"B" -> "BB",
				"C" -> "CC"
			},
			"GrowthRate" -> Missing["Nonexistent"],
			"GrowthRateLimInf" -> 6/5,
			"GrowthRateLimSup" -> 3/2
		}
	},
	2231 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2232 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2233 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2234 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2235 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2236 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2237 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2238 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2240 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2241 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2242 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2243 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2244 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2245 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2246 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2247 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2248 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2249 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2250 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2251 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2252 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2253 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2254 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2255 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2256 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2257 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2258 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2259 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2260 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2261 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2262 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (25.332987518754095 + 1.19696804569168*#1 & ),
					"AdjustedRSquared" -> 0.999986027912115,
					"AIC" -> 79552.99627180115,
					"ProbMinInfoLoss" -> 7.295908834742469884718196110566517580682615`12.240358186726612*^-2250,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.197,
			"Diffusivity" -> 0.3716614510020716,
			"PecletNumber" -> 3.220672998968968,
			"Randomness" -> 0.31049411111284175
		}
	},
	2263 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (29.04948955153008 + 0.6557063583300988*#1^1.0163230716828768 & ),
					"AdjustedRSquared" -> 0.9999921348075747,
					"AIC" -> 78647.59984517367,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0163230716828768
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-11.868059045898265 + 0.7640958622229573*#1 & ),
					"AdjustedRSquared" -> 0.9999396674927363,
					"AIC" -> 85204.47909496896,
					"ProbMinInfoLoss" -> 1.5551119333042629188906293980471126538987`12.247995912841107*^-1424,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7675000000000001,
			"Diffusivity" -> 0.9898363110966028,
			"PecletNumber" -> 0.7753807285062269,
			"Randomness" -> 1.2896890046861273
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (29.8245797639251 + 0.6556478467034478*#1^1.0163330785226161 & ),
					"AdjustedRSquared" -> 0.9999921363824535,
					"AIC" -> 78648.63727768346,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0163330785226161
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-11.117834563453219 + 0.7640992969829921*#1 & ),
					"AdjustedRSquared" -> 0.999939629179821,
					"AIC" -> 85210.91766022296,
					"ProbMinInfoLoss" -> 1.04452918870251874647829570950078808899`12.377680688711553*^-1425,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7675000000000001,
			"Diffusivity" -> 0.9898363110966028,
			"PecletNumber" -> 0.7753807285062269,
			"Randomness" -> 1.2896890046861273
		}
	},
	2264 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2265 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2266 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2267 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2268 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2269 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2270 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2272 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2273 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2274 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2275 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2276 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2277 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2278 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2279 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2280 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2281 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2282 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2283 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2284 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2285 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2286 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2287 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2288 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2289 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2290 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2291 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2292 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2293 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2294 -> {
		{{1}, 0} -> {
			"BoundaryWordCoding" -> {
				"A" -> {},
				"B" -> {2},
				"C" -> {0}
			},
			"BoundaryWordMorphism" -> {
				"A" -> "ABCB",
				"B" -> "BB",
				"C" -> "CC"
			},
			"GrowthRate" -> Missing["Nonexistent"],
			"GrowthRateLimInf" -> 6/5,
			"GrowthRateLimSup" -> 3/2
		}
	},
	2295 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-21.921576657658665 + 0.22058617671386146*#1 & ),
					"AdjustedRSquared" -> 0.9969068347841707,
					"AIC" -> 99757.54740847251,
					"ProbMinInfoLoss" -> 0.10949137516097406,
					"Exponent" -> 1
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.17611510359732752*#1^1.0236679591207463 & ),
					"AdjustedRSquared" -> 0.9991871640217056,
					"AIC" -> 99934.19116410015,
					"ProbMinInfoLoss" -> 4.804804752987117*^-40,
					"Exponent" -> 1.0236679591207463
				}
			},
			"GrowthRate" -> 0.2155,
			"Diffusivity" -> 1.4076797357671353,
			"PecletNumber" -> 0.15308879891103935,
			"Randomness" -> 6.532156546483226
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-21.704240084000563 + 0.22058578943785745*#1 & ),
					"AdjustedRSquared" -> 0.9969067419064359,
					"AIC" -> 99757.81348976475,
					"ProbMinInfoLoss" -> 0.1184044930066859,
					"Exponent" -> 1
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.1765186050688195*#1^1.0234269263908102 & ),
					"AdjustedRSquared" -> 0.999187653708807,
					"AIC" -> 99931.11202023432,
					"ProbMinInfoLoss" -> 2.767390400385909*^-39,
					"Exponent" -> 1.0234269263908102
				}
			},
			"GrowthRate" -> 0.2155,
			"Diffusivity" -> 1.4076797357671353,
			"PecletNumber" -> 0.15308879891103935,
			"Randomness" -> 6.532156546483226
		}
	},
	2296 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2297 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2298 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2299 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2300 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2301 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2302 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2304 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2305 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2306 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2307 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2308 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2309 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2310 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2311 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2312 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2313 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2314 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2315 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2316 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2317 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2318 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2319 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2320 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2321 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2322 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2323 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2324 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2325 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2326 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2327 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2328 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2329 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2330 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2331 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2332 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2333 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2334 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2336 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2337 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2338 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2339 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2340 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2341 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2342 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2343 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2344 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2345 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2346 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2347 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2348 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2349 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2350 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2351 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2352 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2353 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2354 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2355 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2356 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2357 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2358 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2359 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2360 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	2361 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2362 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2363 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2364 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2365 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2366 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2368 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2369 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2370 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2371 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2372 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2373 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2374 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2375 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2376 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2377 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2378 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2379 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2380 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2381 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2382 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2383 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2384 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2385 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2386 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2387 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2388 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2389 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2390 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2391 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2392 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2393 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2394 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2395 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2396 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2397 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2398 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2400 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2401 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2402 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2403 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2404 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.746212601271109 + 1.656435173962349*#1 & ),
					"AdjustedRSquared" -> 0.999993928559716,
					"AIC" -> 77715.78119777076,
					"ProbMinInfoLoss" -> 2.775558358245837*^-6,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6556000000000002,
			"Diffusivity" -> 0.5418540253705306,
			"PecletNumber" -> 3.0554354539820348,
			"Randomness" -> 0.32728559155021175
		}
	},
	2405 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2406 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2407 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2408 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2409 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2410 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2411 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2412 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2413 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2414 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2415 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2416 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2417 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2418 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2419 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2420 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2421 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2422 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2423 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2424 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2425 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2426 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2427 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2428 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2429 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2430 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2432 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2433 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2434 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2435 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2436 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2437 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		}
	},
	2438 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2439 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2440 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2441 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2442 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2443 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2444 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2445 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2446 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2447 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2448 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2449 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2450 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2451 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2452 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2453 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2454 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2455 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2456 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2457 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2458 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2459 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2460 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2461 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2462 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2464 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2465 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2466 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2467 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2468 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2469 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (13.535305721722294 + 0.979412567922447*#1^1.0162241457933527 & ),
					"AdjustedRSquared" -> 0.9999950064089512,
					"AIC" -> 82033.21765992575,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0162241457933527
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.0052787630681717*#1^1.013490187536391 & ),
					"AdjustedRSquared" -> 0.9999947325198192,
					"AIC" -> 82566.18595184112,
					"ProbMinInfoLoss" -> 1.8509977714573093*^-116,
					"Exponent" -> 1.013490187536391
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-47.161122772268726 + 1.14025415913854*#1 & ),
					"AdjustedRSquared" -> 0.9999514782622555,
					"AIC" -> 91032.03362458815,
					"ProbMinInfoLoss" -> 8.549514281560279636250383982170438755390102718435`12.124249920577837*^-1955,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1424,
			"Diffusivity" -> 1.293378887798762,
			"PecletNumber" -> 0.8832678581481123,
			"Randomness" -> 1.1321593905801486
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (37.97442232225615 + 1.1281101045250974*#1 & ),
					"AdjustedRSquared" -> 0.9999796525287183,
					"AIC" -> 82127.05083493446,
					"ProbMinInfoLoss" -> 1.8907369920024495*^-246,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1341,
			"Diffusivity" -> 1.3467847484888518,
			"PecletNumber" -> 0.8420796279973524,
			"Randomness" -> 1.1875361506823487
		}
	},
	2470 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2471 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2472 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2473 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 7/6
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2474 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2475 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2476 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2477 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2478 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2479 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2480 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2481 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2482 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2483 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2484 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2485 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2486 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2487 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2488 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	2489 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2490 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2491 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2492 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2493 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-6.906696369618295 + 1.25337344192973*#1 & ),
					"AdjustedRSquared" -> 0.9999980338375354,
					"AIC" -> 60864.035384466486,
					"ProbMinInfoLoss" -> 1.6581798190208482*^-75,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2527000000000001,
			"Diffusivity" -> 0.6833729982320096,
			"PecletNumber" -> 1.8331131069575863,
			"Randomness" -> 0.5455200752231257
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-5.655968436836848 + 1.2533738363037366*#1 & ),
					"AdjustedRSquared" -> 0.9999980341770293,
					"AIC" -> 60862.314843019856,
					"ProbMinInfoLoss" -> 6.863949190071975*^-76,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2528000000000001,
			"Diffusivity" -> 0.6832224130594696,
			"PecletNumber" -> 1.8336634982303381,
			"Randomness" -> 0.5453563322633058
		}
	},
	2494 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2496 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2497 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2498 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2499 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2500 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2501 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	2502 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2503 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2504 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2505 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2506 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2507 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2508 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2509 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2510 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2511 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2512 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2513 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2514 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2515 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2516 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2517 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	2518 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2519 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2520 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2521 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2522 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2523 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2524 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2525 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2526 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2528 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2529 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2530 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2531 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2532 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-5.514225442535827 + 1.7259162134671608*#1 & ),
					"AdjustedRSquared" -> 0.9999985311930011,
					"AIC" -> 64346.086476639786,
					"ProbMinInfoLoss" -> 4.743297529993349*^-171,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.724,
			"Diffusivity" -> 0.1998115394656089,
			"PecletNumber" -> 8.628130310245325,
			"Randomness" -> 0.11589996488724413
		}
	},
	2533 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (18.213741554157465 + 1.121031908498319*#1 & ),
					"AdjustedRSquared" -> 0.9999932185506235,
					"AIC" -> 71013.37425865201,
					"ProbMinInfoLoss" -> 7.351112480285316*^-203,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1216000000000002,
			"Diffusivity" -> 0.9349989609883173,
			"PecletNumber" -> 1.1995735255303823,
			"Randomness" -> 0.8336296014517807
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (6.215148694873789 + 1.1265652337376517*#1 & ),
					"AdjustedRSquared" -> 0.9999983130409963,
					"AIC" -> 57199.16541562063,
					"ProbMinInfoLoss" -> 7.183121487584548*^-39,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1259000000000001,
			"Diffusivity" -> 0.9146305308666494,
			"PecletNumber" -> 1.2309888659994375,
			"Randomness" -> 0.8123550323000704
		}
	},
	2534 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2535 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		}
	},
	2536 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2537 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2538 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2539 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2540 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2541 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2542 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2544 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	2545 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2546 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2547 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2548 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2549 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2550 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2551 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		}
	},
	2552 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2553 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2554 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2555 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2556 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2557 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2558 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2560 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2561 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2562 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2563 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2564 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2565 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2566 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2567 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2568 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2569 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2570 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2571 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2572 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2573 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2574 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2575 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2576 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2577 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-19.950275367530416 + 1.3137340016733399*#1 & ),
					"AdjustedRSquared" -> 0.9999899519432146,
					"AIC" -> 78117.7681687814,
					"ProbMinInfoLoss" -> 6.857530252283403013283751909898492157582592099691`12.823614785145978*^-588,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3127,
			"Diffusivity" -> 2.9649019112753443,
			"PecletNumber" -> 0.44274651886724503,
			"Randomness" -> 2.2586287127868854
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-21.253706630662787 + 1.3137321681093224*#1 & ),
					"AdjustedRSquared" -> 0.9999899495074271,
					"AIC" -> 78120.16412349303,
					"ProbMinInfoLoss" -> 6.076917353209300956703372365182002041868057832735`12.773398830032082*^-588,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3124,
			"Diffusivity" -> 2.964789437535472,
			"PecletNumber" -> 0.442662127496971,
			"Randomness" -> 2.2590593093077356
		}
	},
	2578 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2579 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2580 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2581 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2582 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2583 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2584 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2585 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 5/6
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 5/6
		}
	},
	2586 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2587 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2588 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2589 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2590 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2592 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2593 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2594 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2595 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2596 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2597 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2598 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2599 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2600 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2601 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2602 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2603 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2604 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2605 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2606 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2607 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2608 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2609 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2610 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2611 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2612 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2613 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2614 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2615 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2616 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2617 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 16,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 16,
			"GrowthRate" -> 5/4
		}
	},
	2618 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2619 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2620 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2621 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2622 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2624 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2625 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2626 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2627 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2628 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2629 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2630 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2631 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2632 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2633 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2634 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2635 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2636 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2637 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2638 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2639 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2640 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2641 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (7.577806240632782 + 1.233147963955478*#1 & ),
					"AdjustedRSquared" -> 0.9999707281316295,
					"AIC" -> 87544.37218296404,
					"ProbMinInfoLoss" -> 1.5706933752905539327371999319876994495166484810987`12.888352269895*^-317,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2338,
			"Diffusivity" -> 3.3083937719637135,
			"PecletNumber" -> 0.3729302147935286,
			"Randomness" -> 2.681466827657411
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (6.341815601582058 + 1.23314842203748*#1 & ),
					"AdjustedRSquared" -> 0.9999707278209098,
					"AIC" -> 87544.48576453493,
					"ProbMinInfoLoss" -> 3.6201544260574341411842561521818431069473222390357`13.092080958672419*^-317,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2335,
			"Diffusivity" -> 3.308233944018527,
			"PecletNumber" -> 0.3728575490346556,
			"Randomness" -> 2.6819894154994137
		}
	},
	2642 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2643 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2644 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2645 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2646 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2647 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2648 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2649 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2650 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2651 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2652 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2653 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2654 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2656 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2657 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2658 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2659 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2660 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2661 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2662 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2663 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2664 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2665 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2666 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2667 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2668 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2669 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2670 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2672 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2673 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2674 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2675 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2676 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2677 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2678 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2679 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2680 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2681 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2682 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2683 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2684 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2685 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2686 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2688 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2689 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		}
	},
	2690 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2691 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2692 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2693 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 18,
			"GrowthRate" -> 5/6
		}
	},
	2694 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2695 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2696 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2697 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2698 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2699 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2700 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2701 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2702 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2703 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2704 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2705 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-6.585417461716571 + 1.7897653869536505*#1 & ),
					"AdjustedRSquared" -> 0.9999991336795392,
					"AIC" -> 59793.10137081239,
					"ProbMinInfoLoss" -> 3.06567977760761361522656030675294916412508445285`12.384038711205305*^-1089,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7894,
			"Diffusivity" -> 1.587702859103674,
			"PecletNumber" -> 1.1270370836330124,
			"Randomness" -> 0.8872822505329574
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (7.196879447976245 + 1.78824723938647*#1 & ),
					"AdjustedRSquared" -> 0.9999985557757485,
					"AIC" -> 64886.86237532927,
					"ProbMinInfoLoss" -> 1.058004079431669463720869536685343883537`12.456613346596631*^-1367,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7878,
			"Diffusivity" -> 1.5912273363763663,
			"PecletNumber" -> 1.123535248,
			"Randomness" -> 0.890047732619066
		}
	},
	2706 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2707 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2708 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2709 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2710 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 4/3
		}
	},
	2711 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2712 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2713 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 32,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 32,
			"GrowthRate" -> 3/2
		}
	},
	2714 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2715 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2716 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2717 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-2.599390038986458 + 1.729186919315864*#1 & ),
					"AdjustedRSquared" -> 0.9999984041245676,
					"AIC" -> 65213.67237795206,
					"ProbMinInfoLoss" -> 2.244511934456362*^-74,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7301000000000002,
			"Diffusivity" -> 1.7377482297139495,
			"PecletNumber" -> 0.9955987699580575,
			"Randomness" -> 1.004420686500173
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-4.323990639057594 + 1.7291858795398554*#1 & ),
					"AdjustedRSquared" -> 0.9999984045750409,
					"AIC" -> 65210.83721552349,
					"ProbMinInfoLoss" -> 1.9598799519805603*^-74,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7298,
			"Diffusivity" -> 1.7378862711236116,
			"PecletNumber" -> 0.9953470654219603,
			"Randomness" -> 1.0046746855842361
		}
	},
	2718 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2720 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2721 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		}
	},
	2722 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2723 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2724 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2725 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 16,
			"GrowthRate" -> 7/8
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (15.86529204923078 + 1.4871515064395122*#1 & ),
					"AdjustedRSquared" -> 0.9999861504842752,
					"AIC" -> 83806.29791352953,
					"ProbMinInfoLoss" -> 2.311609039411541884850830273610901`12.328587494862782*^-1836,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4862,
			"Diffusivity" -> 2.91196831225431,
			"PecletNumber" -> 0.5103764329253477,
			"Randomness" -> 1.9593381188630805
		}
	},
	2726 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2727 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2728 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2729 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2730 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2731 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2732 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2733 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2734 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2735 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2736 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2737 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2738 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2739 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2740 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2741 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2742 -> {
		{{1}, 0} -> {
			"BoundaryWordCoding" -> {
				"A" -> {},
				"B" -> {2},
				"C" -> {0}
			},
			"BoundaryWordMorphism" -> {
				"A" -> "ABCB",
				"B" -> "BB",
				"C" -> "CC"
			},
			"GrowthRate" -> Missing["Nonexistent"],
			"GrowthRateLimInf" -> 6/5,
			"GrowthRateLimSup" -> 3/2
		}
	},
	2743 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2744 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2745 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2746 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2747 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2748 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2749 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 214,
			"GrowthRate" -> 189/107
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 214,
			"GrowthRate" -> 189/107
		}
	},
	2750 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2752 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2753 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2754 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2755 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2756 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2757 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2758 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2759 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2760 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2761 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2762 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2763 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2764 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2765 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2766 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2767 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2768 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2769 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-19.696320011967334 + 1.7754911948829062*#1 & ),
					"AdjustedRSquared" -> 0.9999987125484169,
					"AIC" -> 63594.60840658764,
					"ProbMinInfoLoss" -> 1.8721487660313993*^-32,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.774,
			"Diffusivity" -> 1.6896020068100028,
			"PecletNumber" -> 1.0499514044430749,
			"Randomness" -> 0.9524250320236768
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-9.903975277506982 + 1.7721299220632944*#1 & ),
					"AdjustedRSquared" -> 0.9999982798492151,
					"AIC" -> 66454.18588142341,
					"ProbMinInfoLoss" -> 2.061073190697491114583293434330908`12.922981928325832*^-429,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7717,
			"Diffusivity" -> 1.7002596038759707,
			"PecletNumber" -> 1.0420173460342006,
			"Randomness" -> 0.9596769226595759
		}
	},
	2770 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2771 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2772 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2773 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2774 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 58,
			"GrowthRate" -> 65/58
		}
	},
	2775 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2776 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2777 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2778 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2779 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2780 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2781 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2782 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2784 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2785 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		}
	},
	2786 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2787 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2788 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2789 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2790 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2791 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2792 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2793 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2794 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2795 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2796 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2797 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2798 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2800 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2801 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2802 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2803 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2804 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2805 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2806 -> {
		{{1}, 0} -> {
			"BoundaryWordCoding" -> {
				"A" -> {},
				"B" -> {2},
				"C" -> {0}
			},
			"BoundaryWordMorphism" -> {
				"A" -> "ABCB",
				"B" -> "BB",
				"C" -> "CC"
			},
			"GrowthRate" -> Missing["Nonexistent"],
			"GrowthRateLimInf" -> 6/5,
			"GrowthRateLimSup" -> 3/2
		}
	},
	2807 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2808 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2809 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2810 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2811 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2812 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2813 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	2814 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2816 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2817 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2818 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2819 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2820 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2821 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2822 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2823 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2824 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2825 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2826 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2827 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2828 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2829 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2830 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2831 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2832 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2833 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2834 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2835 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2836 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2837 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2838 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2839 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2840 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2841 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2842 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2843 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2844 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2845 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2846 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2848 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2849 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2850 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2851 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2852 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2853 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2854 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2855 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2856 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2857 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2858 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2859 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2860 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2861 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2862 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2863 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2864 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2865 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2866 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2867 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2868 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2869 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2870 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2871 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2872 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2873 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2874 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2875 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2876 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2877 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2878 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2880 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2881 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2882 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2883 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2884 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2885 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2886 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2887 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2888 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2889 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2890 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2891 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2892 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2893 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2894 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2895 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2896 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2897 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2898 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2899 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2900 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2901 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2902 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2903 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2904 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2905 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	2906 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2907 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2908 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2909 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2910 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2912 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2913 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2914 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2915 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2916 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (15.709323060032448 + 0.6649212355248327*#1^1.0281658703402685 & ),
					"AdjustedRSquared" -> 0.9999839503024057,
					"AIC" -> 88103.40083428509,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0281658703402685
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.6923689566915252*#1^1.0239209466005534 & ),
					"AdjustedRSquared" -> 0.9999832885335577,
					"AIC" -> 88506.45197638213,
					"ProbMinInfoLoss" -> 3.009930939934888*^-88,
					"Exponent" -> 1.0239209466005534
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-63.361043204320325 + 0.8656987787629872*#1 & ),
					"AdjustedRSquared" -> 0.9998508049873583,
					"AIC" -> 96756.07505794408,
					"ProbMinInfoLoss" -> 1.24642307130339107507781933962730910263250291834`12.17206360584327*^-1879,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8598,
			"Diffusivity" -> 3.4390298001594517,
			"PecletNumber" -> 0.25001237266398074,
			"Randomness" -> 3.9998020471731235
		}
	},
	2917 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2918 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2919 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2920 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2921 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2922 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2923 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2924 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2925 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	2926 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2928 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2929 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2930 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2931 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2932 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2933 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2934 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2935 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2936 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2937 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	2938 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2939 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2940 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2941 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2942 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2944 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2945 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2946 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2947 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2948 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2949 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2950 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2951 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2952 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2953 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2954 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2955 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2956 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2957 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 5/6
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 5/6
		}
	},
	2958 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2959 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2960 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2961 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	2962 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2963 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2964 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2965 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2966 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2967 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2968 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2969 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/4
		}
	},
	2970 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2971 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2972 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2973 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 4/3
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 4/3
		}
	},
	2974 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2976 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2977 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2978 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2979 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2980 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	2981 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2982 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2983 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2984 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2985 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/4
		}
	},
	2986 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2987 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2988 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	2989 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	2990 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2992 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2993 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		}
	},
	2994 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2995 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	2996 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	2997 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	2998 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	2999 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3000 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3001 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/4
		}
	},
	3002 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3003 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3004 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3005 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 4/3
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 4/3
		}
	},
	3006 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3008 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3009 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3010 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3011 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3012 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3013 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3014 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3015 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3016 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3017 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3018 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3019 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3020 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3021 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3022 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3023 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3024 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3025 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3026 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3027 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3028 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3029 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3030 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3031 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3032 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3033 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3034 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3035 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3036 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3037 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3038 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3040 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3041 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3042 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3043 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3044 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 38,
			"GrowthRate" -> 61/38
		}
	},
	3045 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3046 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3047 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3048 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3049 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3050 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3051 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3052 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3053 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3054 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3056 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3057 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		}
	},
	3058 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3059 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3060 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3061 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3062 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3063 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3064 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3065 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3066 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3067 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3068 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3069 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3070 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3072 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3073 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3074 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3075 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3076 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3077 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3078 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3079 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3080 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3081 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3082 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3083 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3084 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3085 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3086 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3087 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3088 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3089 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3090 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3091 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3092 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3093 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3094 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3095 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3096 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3097 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3098 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3099 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3100 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3101 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3102 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3104 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3105 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3106 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3107 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3108 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3109 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3110 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3111 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3112 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3113 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 56,
			"GrowthRate" -> 15/14
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 56,
			"GrowthRate" -> 15/14
		}
	},
	3114 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3115 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3116 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3117 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3118 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3120 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3121 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3122 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3123 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3124 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3125 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3126 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3127 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3128 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3129 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3130 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3131 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3132 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3133 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3134 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3136 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3137 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3138 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3139 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3140 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3141 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3142 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3143 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3144 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3145 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3146 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3147 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3148 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3149 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3150 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3151 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3152 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3153 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3154 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (4.98218716649465 + 1.3786960441923373*#1^1.0111626858772218 & ),
					"AdjustedRSquared" -> 0.9999988427999762,
					"AIC" -> 73325.56638470177,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0111626858772218
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.3885139180494133*#1^1.0104187186799414 & ),
					"AdjustedRSquared" -> 0.999998822415527,
					"AIC" -> 73499.18632540548,
					"ProbMinInfoLoss" -> 1.9902558173786111*^-38,
					"Exponent" -> 1.0104187186799414
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-51.36144884485578 + 1.530773212447727*#1 & ),
					"AdjustedRSquared" -> 0.9999816648748957,
					"AIC" -> 87190.23486533851,
					"ProbMinInfoLoss" -> 2.115888220396156636047433560642068`11.968551550374332*^-3011,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5263,
			"Diffusivity" -> 0.24933047415563722,
			"PecletNumber" -> 6.121594262269168,
			"Randomness" -> 0.16335613847581554
		}
	},
	3155 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3156 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3157 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3158 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3159 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3160 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3161 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3162 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 5/6
		}
	},
	3163 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3164 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3165 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3166 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3168 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3169 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3170 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3171 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3172 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3173 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3174 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3175 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3176 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3177 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3178 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3179 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3180 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3181 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3182 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3184 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3185 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3186 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3187 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3188 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3189 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3190 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3191 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3192 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3193 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3194 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3195 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3196 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3197 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3198 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3200 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3201 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3202 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3203 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3204 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3205 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3206 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3207 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3208 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3209 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (87.72992831590575 + 0.9467806699996923*#1^1.0237531706296876 & ),
					"AdjustedRSquared" -> 0.9999786424232978,
					"AIC" -> 97413.17584944019,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0237531706296876
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.7703137113340204 + 1.1827862641158566*#1 & ),
					"AdjustedRSquared" -> 0.9998532258801692,
					"AIC" -> 102834.27944836712,
					"ProbMinInfoLoss" -> 6.642179074497036158981838911320060493`12.521532058996385*^-1178,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1860000000000002,
			"Diffusivity" -> 6.029606461346274,
			"PecletNumber" -> 0.1966960874815026,
			"Randomness" -> 5.083985211927718
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (91.37972707011649 + 0.9464803976200435*#1^1.0237877380732658 & ),
					"AdjustedRSquared" -> 0.9999786990006038,
					"AIC" -> 97395.70559428222,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0237877380732658
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.2511610560980626 + 1.1827938728239384*#1 & ),
					"AdjustedRSquared" -> 0.9998531955129477,
					"AIC" -> 102836.47717157743,
					"ProbMinInfoLoss" -> 3.56010938800126178822027292200521`12.3524133919393*^-1182,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1864000000000001,
			"Diffusivity" -> 6.025456656487814,
			"PecletNumber" -> 0.19689793946531223,
			"Randomness" -> 5.078773311267542
		}
	},
	3210 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3211 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3212 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3213 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3214 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3215 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3216 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3217 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3218 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3219 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (15.724363576370529 + 0.8041945878259444*#1 & ),
					"AdjustedRSquared" -> 0.9999756841315993,
					"AIC" -> 77139.66020311916,
					"ProbMinInfoLoss" -> 2.6155139733868737530306630543348942391`12.777622800908873*^-444,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.802,
			"Diffusivity" -> 2.5811083008680944,
			"PecletNumber" -> 0.31071923627934034,
			"Randomness" -> 3.2183395272669504
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-35.26274065237592 + 0.8808829704105409*#1^0.9891105819425312 & ),
					"AdjustedRSquared" -> 0.9999754239029001,
					"AIC" -> 90866.36407365502,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9891105819425312
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-6.067785838583078 + 0.7953439427734383*#1 & ),
					"AdjustedRSquared" -> 0.999888491321411,
					"AIC" -> 92148.93253166495,
					"ProbMinInfoLoss" -> 3.1174393396518982*^-279,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7945,
			"Diffusivity" -> 2.6279911247776107,
			"PecletNumber" -> 0.3023221777688588,
			"Randomness" -> 3.307729546604922
		}
	},
	3220 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3221 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3222 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3223 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-10.648894149418341 + 0.9001821206178213*#1 & ),
					"AdjustedRSquared" -> 0.9999234562938127,
					"AIC" -> 90862.62657212182,
					"ProbMinInfoLoss" -> 7.988300286158958*^-99,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.897,
			"Diffusivity" -> 0.7811461682275449,
			"PecletNumber" -> 1.1483126161078567,
			"Randomness" -> 0.8708429969091916
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-9.748797659764243 + 0.9001815013818143*#1 & ),
					"AdjustedRSquared" -> 0.999923451325813,
					"AIC" -> 90863.26188363155,
					"ProbMinInfoLoss" -> 3.909657945549122*^-99,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8971,
			"Diffusivity" -> 0.7810667444019858,
			"PecletNumber" -> 1.1485574138569346,
			"Randomness" -> 0.8706573898138287
		}
	},
	3224 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3225 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3226 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3227 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3228 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3229 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3230 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3232 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3233 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3234 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3235 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3236 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3237 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3238 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3239 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3240 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3241 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3242 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3243 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3244 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3245 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3246 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3248 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3249 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3250 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3251 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-24.9413998742925 + 1.1815180071017735*#1^1.0125398102554801 & ),
					"AdjustedRSquared" -> 0.9999981695368046,
					"AIC" -> 75002.6504086963,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0125398102554801
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.1339459338212199*#1^1.0168489897447708 & ),
					"AdjustedRSquared" -> 0.9999974753638643,
					"AIC" -> 78216.92966527226,
					"ProbMinInfoLoss" -> 1.0669100018599348219350476368464685`12.687896365297583*^-698,
					"Exponent" -> 1.0168489897447708
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-79.81328826881074 + 1.3288821294408182*#1 & ),
					"AdjustedRSquared" -> 0.999975406764945,
					"AIC" -> 87298.12745298845,
					"ProbMinInfoLoss" -> 1.1778328098363142271936525225893065592891578507`12.165874382541567*^-2670,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3223,
			"Diffusivity" -> 0.5739271066534539,
			"PecletNumber" -> 2.303951119699292,
			"Randomness" -> 0.4340369860496513
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 4/3
		}
	},
	3252 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3253 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3254 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3255 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 62,
			"GrowthRate" -> 47/62
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 62,
			"GrowthRate" -> 47/62
		}
	},
	3256 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3257 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3258 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3259 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3260 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3261 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3262 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3264 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3265 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3266 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3267 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3268 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3269 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3270 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3271 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3272 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3273 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3274 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3275 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3276 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3277 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3278 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3279 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3280 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3281 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3282 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (4.98218716649465 + 1.3786960441923373*#1^1.0111626858772218 & ),
					"AdjustedRSquared" -> 0.9999988427999762,
					"AIC" -> 73325.56638470177,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0111626858772218
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.3885139180494133*#1^1.0104187186799414 & ),
					"AdjustedRSquared" -> 0.999998822415527,
					"AIC" -> 73499.18632540548,
					"ProbMinInfoLoss" -> 1.9902558173786111*^-38,
					"Exponent" -> 1.0104187186799414
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-51.36144884485578 + 1.530773212447727*#1 & ),
					"AdjustedRSquared" -> 0.9999816648748957,
					"AIC" -> 87190.23486533851,
					"ProbMinInfoLoss" -> 2.115888220396156636047433560642068`11.968551550374332*^-3011,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5263,
			"Diffusivity" -> 0.24933047415563722,
			"PecletNumber" -> 6.121594262269168,
			"Randomness" -> 0.16335613847581554
		}
	},
	3283 -> {
		{{1}, 0} -> {
			"BoundaryWordCoding" -> {
				"A" -> {2, 1},
				"B" -> {2, -1, 2, 1},
				"C" -> {2, -2}
			},
			"BoundaryWordMorphism" -> {
				"A" -> "ABCB",
				"B" -> "BB",
				"C" -> "CC"
			},
			"GrowthRate" -> Missing["Nonexistent"],
			"GrowthRateLimInf" -> 3/4,
			"GrowthRateLimSup" -> 6/7
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.6893148514942735 + 0.9723090261270889*#1 & ),
					"AdjustedRSquared" -> 0.9999601283205476,
					"AIC" -> 85881.83535940012,
					"ProbMinInfoLoss" -> 1.26852972878372246070420103511111678`12.943139823896878*^-446,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9705,
			"Diffusivity" -> 1.8221941017866539,
			"PecletNumber" -> 0.5325996824643592,
			"Randomness" -> 1.8775827942160266
		}
	},
	3284 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3285 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3286 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3287 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 22,
			"GrowthRate" -> 14/11
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 22,
			"GrowthRate" -> 14/11
		}
	},
	3288 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3289 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3290 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3291 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3292 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3293 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3294 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3296 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3297 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3298 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3299 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.9211852385301615 + 1.3149437885734374*#1 & ),
					"AdjustedRSquared" -> 0.999999634708057,
					"AIC" -> 44991.70378575763,
					"ProbMinInfoLoss" -> 1.5971220048706969154047809735074243365299563601`12.603460048174185*^-975,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3148,
			"Diffusivity" -> 0.5862082907630631,
			"PecletNumber" -> 2.2428887832489273,
			"Randomness" -> 0.4458535828742494
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.3395518751948843 + 1.3149454150834523*#1 & ),
					"AdjustedRSquared" -> 0.9999996351691897,
					"AIC" -> 44979.09686648464,
					"ProbMinInfoLoss" -> 4.43207354437584219214160272291799251293951207591997`12.465923682877134*^-971,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3146,
			"Diffusivity" -> 0.5863342085358766,
			"PecletNumber" -> 2.242066010923465,
			"Randomness" -> 0.4460171980342892
		}
	},
	3300 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3301 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3302 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3303 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3304 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3305 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3306 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3307 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3308 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3309 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3310 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3312 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3313 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3314 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3315 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3316 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3317 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3318 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3319 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3320 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3321 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3322 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3323 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3324 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3325 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3326 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3328 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3329 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3330 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3331 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3332 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3333 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3334 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3335 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3336 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3337 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3338 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3339 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3340 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3341 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3342 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3343 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3344 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3345 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3346 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3347 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3348 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3349 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3350 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3351 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3352 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 20,
			"GrowthRate" -> 23/20
		}
	},
	3353 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3354 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3355 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3356 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3357 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3358 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3360 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3361 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3362 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3363 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3364 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3365 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3366 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3367 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3368 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3369 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (4.690642424252584 + 0.8670738841267377*#1 & ),
					"AdjustedRSquared" -> 0.9999979734966328,
					"AIC" -> 53796.92257169008,
					"ProbMinInfoLoss" -> 1.1902547631586972646443680410780792218695239934`12.471494196754563*^-802,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.867,
			"Diffusivity" -> 1.3817855880407004,
			"PecletNumber" -> 0.6274490105439301,
			"Randomness" -> 1.5937550035071517
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (3.8210060606175107 + 0.8670744313447428*#1 & ),
					"AdjustedRSquared" -> 0.9999979737527398,
					"AIC" -> 53795.67132388212,
					"ProbMinInfoLoss" -> 2.0894715911501867691105894647206403108386853149`12.688373052125701*^-802,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8668,
			"Diffusivity" -> 1.3817323320649728,
			"PecletNumber" -> 0.6273284484156086,
			"Randomness" -> 1.5940612967985381
		}
	},
	3370 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3371 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3372 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3373 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3374 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3376 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3377 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3378 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3379 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3380 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3381 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3382 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3383 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3384 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/4
		}
	},
	3385 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3386 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3387 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3388 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3389 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3390 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3392 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3393 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3394 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3395 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3396 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3397 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3398 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3399 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3400 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3401 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3402 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3403 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3404 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3405 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3406 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3407 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3408 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3409 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3410 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3411 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3412 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3413 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3414 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3415 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3416 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3417 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3418 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3419 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3420 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3421 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3422 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3424 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3425 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3426 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3427 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3428 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3429 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3430 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3431 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3432 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3433 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3434 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3435 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3436 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3437 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3438 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3440 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3441 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3442 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3443 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3444 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3445 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3446 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3447 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3448 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3449 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3450 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3451 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3452 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3453 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3454 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3456 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3457 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3458 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3459 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3460 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3461 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3462 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3463 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-26.2400100810043 + 0.6993552064955518*#1 & ),
					"AdjustedRSquared" -> 0.999966987821347,
					"AIC" -> 77403.57126465198,
					"ProbMinInfoLoss" -> 4.413562389113381*^-29,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6954,
			"Diffusivity" -> 0.21185193134236407,
			"PecletNumber" -> 3.282481285838251,
			"Randomness" -> 0.30464758605459313
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-25.54867044704123 + 0.6993560184875601*#1 & ),
					"AdjustedRSquared" -> 0.9999670010325049,
					"AIC" -> 77399.59164843334,
					"ProbMinInfoLoss" -> 1.5136347759236987*^-29,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6955,
			"Diffusivity" -> 0.21181283961562788,
			"PecletNumber" -> 3.283559208507419,
			"Randomness" -> 0.3045475767298747
		}
	},
	3464 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3465 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3466 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3467 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3468 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3469 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3470 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3471 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3472 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3473 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3474 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3475 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3476 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3477 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3478 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3479 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3480 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 13,
			"GrowthRate" -> 16/13
		}
	},
	3481 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3482 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3483 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3484 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3485 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3486 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3488 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3489 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3490 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3491 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3492 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 7/4
		}
	},
	3493 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.4436285628558836 + 1.390666859026665*#1 & ),
					"AdjustedRSquared" -> 0.9999988929972794,
					"AIC" -> 57198.645693486505,
					"ProbMinInfoLoss" -> 9.6354690731344187520640234678789`12.797874792719247*^-624,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3909,
			"Diffusivity" -> 0.45637318282738454,
			"PecletNumber" -> 3.0477250906438216,
			"Randomness" -> 0.3281135831672906
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.1585860785871046 + 1.3950574714685722*#1 & ),
					"AdjustedRSquared" -> 0.9999971337370744,
					"AIC" -> 66775.23733573526,
					"ProbMinInfoLoss" -> 3.77692375668917558316039445283243`12.85564074374642*^-546,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3938000000000001,
			"Diffusivity" -> 0.4509962498550315,
			"PecletNumber" -> 3.090491329912442,
			"Randomness" -> 0.3235731452540045
		}
	},
	3494 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3495 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3496 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3497 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-11.116625322504554 + 1.44585253981052*#1 & ),
					"AdjustedRSquared" -> 0.9999959005511454,
					"AIC" -> 71068.95496733816,
					"ProbMinInfoLoss" -> 3.42657969081774885151207830410289318981`12.695632592391288*^-521,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4456,
			"Diffusivity" -> 0.35589196047030186,
			"PecletNumber" -> 4.061906872213909,
			"Randomness" -> 0.24618979003202954
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-9.476571197115701 + 1.4487237218672373*#1 & ),
					"AdjustedRSquared" -> 0.9999959075512239,
					"AIC" -> 71091.54137396422,
					"ProbMinInfoLoss" -> 2.3538703978123798*^-230,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4465000000000001,
			"Diffusivity" -> 0.35398860950307875,
			"PecletNumber" -> 4.086289674773898,
			"Randomness" -> 0.2447207808524568
		}
	},
	3498 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3499 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3500 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3501 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3502 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3504 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3505 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3506 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3507 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3508 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3509 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3510 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3511 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3512 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/4
		}
	},
	3513 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-10.390277647759651 + 1.1308953459949518*#1 & ),
					"AdjustedRSquared" -> 0.9999935812965192,
					"AIC" -> 70638.82464110768,
					"ProbMinInfoLoss" -> 5.811323485254071160150878668455117546362`13.007776339844215*^-385,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1300000000000001,
			"Diffusivity" -> 1.1247232544818795,
			"PecletNumber" -> 1.004691594574126,
			"Randomness" -> 0.9953303137007782
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-9.263747854785763 + 1.1308959799729592*#1 & ),
					"AdjustedRSquared" -> 0.9999935824680252,
					"AIC" -> 70637.01053071527,
					"ProbMinInfoLoss" -> 1.9872866321897601997088938913557030846223`13.008380313440796*^-384,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1299000000000001,
			"Diffusivity" -> 1.1250493122927017,
			"PecletNumber" -> 1.0043115334184005,
			"Randomness" -> 0.9957069760976206
		}
	},
	3514 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3515 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3516 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3517 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3518 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3520 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3521 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3522 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3523 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3524 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3525 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3526 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3527 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	3528 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3529 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3530 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3531 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3532 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3533 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3534 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3536 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3537 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3538 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3539 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3540 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3541 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3542 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3543 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	3544 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3545 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3546 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3547 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3548 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3549 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3550 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3552 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3553 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3554 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3555 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3556 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 7/4
		}
	},
	3557 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 7/6
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 7/6
		}
	},
	3558 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3559 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3560 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3561 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3562 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3563 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3564 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3565 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3566 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3568 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3569 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3570 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3571 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3572 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3573 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3574 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3575 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3576 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3577 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3578 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3579 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3580 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3581 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3582 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3584 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3585 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3586 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3587 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3588 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3589 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3590 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3591 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3592 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3593 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-10.029107456254234 + 1.0165021704065047*#1^0.9768355005915107 & ),
					"AdjustedRSquared" -> 0.9999897686280697,
					"AIC" -> 82884.92541655876,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9768355005915107
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.9909214506976417*#1^0.9795024552253611 & ),
					"AdjustedRSquared" -> 0.9999895051697493,
					"AIC" -> 83138.16665978995,
					"ProbMinInfoLoss" -> 1.0217925625149314*^-55,
					"Exponent" -> 0.9795024552253611
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (54.63856903691108 + 0.817892216970921*#1 & ),
					"AdjustedRSquared" -> 0.9998976250780206,
					"AIC" -> 91853.3529728626,
					"ProbMinInfoLoss" -> 3.393911192635886022283918370070091089`12.21006078970773*^-1948,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8218000000000001,
			"Diffusivity" -> 5.963834351028622,
			"PecletNumber" -> 0.1377972545227147,
			"Randomness" -> 7.257038635955976
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-10.899886344159677 + 1.0166008395080464*#1^0.9768257069188838 & ),
					"AdjustedRSquared" -> 0.9999897668594381,
					"AIC" -> 82883.68514019874,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9768257069188838
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.9888232877779778*#1^0.9797246220791688 & ),
					"AdjustedRSquared" -> 0.999989455318406,
					"AIC" -> 83182.58629389762,
					"ProbMinInfoLoss" -> 1.242908496992819*^-65,
					"Exponent" -> 0.9797246220791688
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (53.79610831084604 + 0.8178963687009609*#1 & ),
					"AdjustedRSquared" -> 0.9998975788834957,
					"AIC" -> 91857.96622862731,
					"ProbMinInfoLoss" -> 1.81811823811807005973093139362798225`12.241582520939087*^-1949,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8215,
			"Diffusivity" -> 5.963427248906127,
			"PecletNumber" -> 0.137756354812694,
			"Randomness" -> 7.259193242734177
		}
	},
	3594 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3595 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3596 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3597 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3598 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3599 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3600 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3601 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3602 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	3603 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3604 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3605 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3606 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3607 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3608 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3609 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3610 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	3611 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 20,
			"GrowthRate" -> 9/10
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 20,
			"GrowthRate" -> 9/10
		}
	},
	3612 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3613 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3614 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3616 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3617 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3618 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3619 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3620 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3621 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3622 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3623 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3624 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3625 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 18,
			"GrowthRate" -> 13/18
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 18,
			"GrowthRate" -> 13/18
		}
	},
	3626 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3627 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3628 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3629 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3630 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3632 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3633 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3634 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3635 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3636 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3637 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3638 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3639 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3640 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3641 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3642 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3643 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3644 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3645 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3646 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3648 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3649 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3650 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3651 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3652 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3653 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3654 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3655 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3656 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3657 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3658 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3659 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3660 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3661 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3662 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3664 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3665 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3666 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3667 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3668 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3669 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3670 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3671 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3672 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3673 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3674 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3675 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3676 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3677 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3678 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3680 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3681 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3682 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3683 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3684 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3685 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3686 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3687 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3688 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3689 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3690 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3691 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3692 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3693 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3694 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3696 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3697 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (31.218283468350428 + 1.1446339599103368*#1 & ),
					"AdjustedRSquared" -> 0.9999807294146525,
					"AIC" -> 81874.09504973101,
					"ProbMinInfoLoss" -> 1.72830694225163766224224263118760813121912595`12.496590392462185*^-1247,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1453,
			"Diffusivity" -> 3.7099277841366853,
			"PecletNumber" -> 0.3087122086034124,
			"Randomness" -> 3.2392628866992803
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (30.056649144900735 + 1.144637246446373*#1 & ),
					"AdjustedRSquared" -> 0.9999807266936332,
					"AIC" -> 81875.5644088536,
					"ProbMinInfoLoss" -> 4.7675800831226632117415511564200994714143142`12.46844562579607*^-1248,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.145,
			"Diffusivity" -> 3.7097148402577806,
			"PecletNumber" -> 0.3086490604545864,
			"Randomness" -> 3.2399256246792847
		}
	},
	3698 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3699 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3700 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3701 -> {
		{{1}, 0} -> {
			"BoundaryWordCoding" -> {
				"A" -> {},
				"B" -> {3, 0},
				"C" -> {3, -1}
			},
			"BoundaryWordMorphism" -> {
				"A" -> "AB",
				"B" -> "BCCCCCC",
				"C" -> "CCCCC"
			},
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordCoding" -> {
				"A" -> {0},
				"B" -> {3, 0},
				"C" -> {3, -1}
			},
			"BoundaryWordMorphism" -> {
				"A" -> "AB",
				"B" -> "BCCCCCC",
				"C" -> "CCCCC"
			},
			"GrowthRate" -> 1
		}
	},
	3702 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3703 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3704 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3705 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3706 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3707 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3708 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3709 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3710 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3712 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3713 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		}
	},
	3714 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3715 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3716 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3717 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3718 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3719 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3720 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3721 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 30,
			"GrowthRate" -> 7/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 30,
			"GrowthRate" -> 7/5
		}
	},
	3722 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3723 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3724 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3725 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3726 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3727 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3728 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3729 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-34.17943810379075 + 1.2835280148192774*#1 & ),
					"AdjustedRSquared" -> 0.9999590027883516,
					"AIC" -> 91714.10723343314,
					"ProbMinInfoLoss" -> 9.108843602767233*^-56,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2738,
			"Diffusivity" -> 5.331092281062473,
			"PecletNumber" -> 0.23893790106108143,
			"Randomness" -> 4.185187848219872
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-21.48184692467389 + 1.283537355649369*#1 & ),
					"AdjustedRSquared" -> 0.9999798189203825,
					"AIC" -> 84626.45920594697,
					"ProbMinInfoLoss" -> 2.28543368811227395916542726869464970972258416165689`12.512937487492412*^-817,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2809000000000001,
			"Diffusivity" -> 5.259239146559185,
			"PecletNumber" -> 0.24355233985471425,
			"Randomness" -> 4.105893626793025
		}
	},
	3730 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	3731 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3732 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3733 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3734 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3735 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3736 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3737 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 44,
			"GrowthRate" -> 21/11
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 44,
			"GrowthRate" -> 21/11
		}
	},
	3738 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3739 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3740 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3741 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3742 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3744 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3745 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		}
	},
	3746 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3747 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3748 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3749 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (5.667193579372834 + 1.7482097803060945*#1 & ),
					"AdjustedRSquared" -> 0.9999994059281344,
					"AIC" -> 55550.70753784682,
					"ProbMinInfoLoss" -> 3.050939587721326184387166619104839734938`12.368484892370718*^-1675,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7483000000000002,
			"Diffusivity" -> 1.692029515013914,
			"PecletNumber" -> 1.0332562077001497,
			"Randomness" -> 0.9678141709168413
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-2.0574057605495915 + 1.748486832468864*#1 & ),
					"AdjustedRSquared" -> 0.9999998410158065,
					"AIC" -> 42371.91736878602,
					"ProbMinInfoLoss" -> 1.2614567657125615*^-39,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7482,
			"Diffusivity" -> 1.6916791098993875,
			"PecletNumber" -> 1.0334111178472696,
			"Randomness" -> 0.9676690938676282
		}
	},
	3750 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3751 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 3/4
		}
	},
	3752 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3753 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-29.06265742573131 + 1.6396230491802288*#1 & ),
					"AdjustedRSquared" -> 0.9999757903188294,
					"AIC" -> 91343.50121403647,
					"ProbMinInfoLoss" -> 4.9879403567235585*^-28,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6421000000000001,
			"Diffusivity" -> 2.755517460127689,
			"PecletNumber" -> 0.5959316258238865,
			"Randomness" -> 1.6780448572728148
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-16.141704050384583 + 1.6519075500550713*#1 & ),
					"AdjustedRSquared" -> 0.9999882033545724,
					"AIC" -> 84303.2900059341,
					"ProbMinInfoLoss" -> 1.6856368527549129510982014143928172142531`12.805062219150088*^-403,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.647,
			"Diffusivity" -> 2.7410973543843684,
			"PecletNumber" -> 0.6008542518074499,
			"Randomness" -> 1.6642971186304603
		}
	},
	3754 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3755 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3756 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3757 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3758 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3760 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3761 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3762 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3763 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-21.51624092408631 + 1.3322463035544614*#1 & ),
					"AdjustedRSquared" -> 0.9999952941666751,
					"AIC" -> 70811.81090306032,
					"ProbMinInfoLoss" -> 9.47062111010665837193596570778740234`12.103115587785409*^-3086,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3318,
			"Diffusivity" -> 0.5582093916533082,
			"PecletNumber" -> 2.385843054441392,
			"Randomness" -> 0.4191390536516805
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.8118365436332535 + 1.3400882584828802*#1 & ),
					"AdjustedRSquared" -> 0.9999988435785118,
					"AIC" -> 56894.42999709179,
					"ProbMinInfoLoss" -> 0.002146028150561146,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.34,
			"Diffusivity" -> 0.5442972983035451,
			"PecletNumber" -> 2.4618898608839053,
			"Randomness" -> 0.406192013659362
		}
	},
	3764 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3765 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3766 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3767 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3768 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3769 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3770 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3771 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3772 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3773 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3774 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3776 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3777 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3778 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3779 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3780 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3781 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3782 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3783 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3784 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3785 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3786 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3787 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3788 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3789 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3790 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3792 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3793 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 1
		}
	},
	3794 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3795 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3796 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3797 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3798 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3799 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		}
	},
	3800 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3801 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3802 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3803 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3804 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3805 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3806 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3808 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3809 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3810 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3811 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3812 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3813 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3814 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3815 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3816 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3817 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3818 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3819 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3820 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3821 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3822 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3824 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3825 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3826 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3827 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3828 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3829 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3830 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3831 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3832 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3833 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3834 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3835 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3836 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3837 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	3838 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3840 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3841 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3842 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3843 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3844 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3845 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3846 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3847 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3848 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3849 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3850 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3851 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3852 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3853 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3854 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3855 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3856 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3857 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3858 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3859 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3860 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3861 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3862 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3863 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3864 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3865 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3866 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3867 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3868 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3869 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3870 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3872 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3873 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3874 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3875 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3876 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3877 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3878 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3879 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3880 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3881 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3882 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3883 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3884 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3885 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3886 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3888 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3889 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3890 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3891 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3892 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3893 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3894 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3895 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3896 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3897 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3898 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3899 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3900 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3901 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3902 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3904 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3905 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3906 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3907 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3908 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3909 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3910 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3911 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3912 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3913 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3914 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3915 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3916 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3917 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3918 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3920 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3921 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3922 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3923 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3924 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3925 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3926 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3927 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3928 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3929 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3930 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3931 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3932 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3933 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3934 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3936 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3937 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3938 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3939 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3940 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3941 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3942 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3943 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3944 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3945 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3946 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3947 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3948 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3949 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	3950 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3952 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	3953 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3954 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3955 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3956 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3957 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3958 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3959 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3960 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3961 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3962 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3963 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3964 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3965 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3966 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3968 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3969 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3970 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3971 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	3972 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3973 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3974 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3975 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1/2
		}
	},
	3976 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	3977 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3978 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3979 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3980 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3981 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3982 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3984 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3985 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	3986 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3987 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3988 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3989 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3990 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3991 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3992 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3993 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3994 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	3995 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	3996 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	3997 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	3998 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4000 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4001 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4002 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4003 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4004 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 5/3
		}
	},
	4005 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4006 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4007 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	4008 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4009 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4010 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4011 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4012 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4013 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4014 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4016 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4017 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 1
		}
	},
	4018 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4019 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4020 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4021 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4022 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4023 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4024 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4025 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4026 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4027 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4028 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4029 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4030 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4032 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4033 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4034 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4035 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4036 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4037 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4038 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4039 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	4040 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4041 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4042 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4043 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4044 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4045 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4046 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4048 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 5,
			"GrowthRate" -> 2/5
		}
	},
	4049 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4050 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4051 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4052 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4053 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4054 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4055 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	4056 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4057 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4058 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4059 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4060 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4061 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4062 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4064 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4065 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4066 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4067 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4068 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 5/3
		}
	},
	4069 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4070 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4071 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	4072 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4073 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4074 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4075 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4076 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4077 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4078 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4080 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4081 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 1
		}
	},
	4082 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4083 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4084 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4085 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4086 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4087 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4088 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4089 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4090 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4091 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4092 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4093 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4094 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4104 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4105 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4106 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4107 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4108 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4109 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4110 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4122 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4123 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4124 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4125 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4126 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4136 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4137 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4138 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4139 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4140 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4141 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4142 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4152 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4153 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4154 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4155 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4156 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4157 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4158 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4168 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4169 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4170 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4171 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4172 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4173 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4174 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (12.898018121818899 + 1.3852614702286135*#1 & ),
					"AdjustedRSquared" -> 0.9999612579135876,
					"AIC" -> 92673.83647877244,
					"ProbMinInfoLoss" -> 1.7136244967775927*^-29,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3848,
			"Diffusivity" -> 2.136541459707083,
			"PecletNumber" -> 0.6481503055830493,
			"Randomness" -> 1.5428520072985865
		}
	},
	4186 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4187 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4188 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4189 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4190 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4200 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4201 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4202 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4203 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4204 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4205 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4206 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-11.161181518134548 + 1.657785717731855*#1 & ),
					"AdjustedRSquared" -> 0.9999947427589172,
					"AIC" -> 76292.17828408921,
					"ProbMinInfoLoss" -> 4.180672885177071915238398415882509595578131722`12.29027774961574*^-1361,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6588,
			"Diffusivity" -> 0.3712133965947105,
			"PecletNumber" -> 4.46858872879276,
			"Randomness" -> 0.22378429985212833
		}
	},
	4216 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4217 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4218 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4219 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4220 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4221 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4222 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4224 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4225 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4226 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4227 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4228 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4229 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4230 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4231 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4232 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4233 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4234 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4235 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4236 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4237 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	4238 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4240 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4241 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4242 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4243 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4244 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4245 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4246 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4247 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4248 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4249 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4250 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4251 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4252 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4253 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4254 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4256 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4257 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4258 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4259 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	4260 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4261 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4262 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.5033989798917903 + 1.0661275470412748*#1 & ),
					"AdjustedRSquared" -> 0.9999328836262473,
					"AIC" -> 92932.01661328155,
					"ProbMinInfoLoss" -> 1.7911366356402221185612114587734442509603`13.008329233827292*^-384,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0638,
			"Diffusivity" -> 0.8178927314615838,
			"PecletNumber" -> 1.300659559718763,
			"Randomness" -> 0.7688406951133518
		}
	},
	4263 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 14,
			"GrowthRate" -> 6/7
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 14,
			"GrowthRate" -> 6/7
		}
	},
	4264 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4265 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4266 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4267 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	4268 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4269 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	4270 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4272 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4273 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4274 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4275 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	4276 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4277 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4278 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4279 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4280 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4281 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4282 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4283 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	4284 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4285 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4286 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4288 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4289 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4290 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4291 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4292 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4293 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4294 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4295 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4296 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4297 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4298 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4299 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4300 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4301 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4302 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4304 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4305 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4306 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4307 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4308 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4309 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4310 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4311 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4312 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4313 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4314 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4315 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4316 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4317 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4318 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4320 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4321 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4322 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4323 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	4324 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4325 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4326 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4327 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-4.242770512903095 + 0.4946660358048978*#1^1.0145003802245776 & ),
					"AdjustedRSquared" -> 0.9999397984742885,
					"AIC" -> 92903.28234047157,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0145003802245776
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.4866281148470207*#1^1.0162180686738547 & ),
					"AdjustedRSquared" -> 0.9999396933965875,
					"AIC" -> 92919.72170080294,
					"ProbMinInfoLoss" -> 0.00026930118289313103,
					"Exponent" -> 1.0162180686738547
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-31.247672787280763 + 0.566676566900766*#1 & ),
					"AdjustedRSquared" -> 0.9997398015820569,
					"AIC" -> 93844.12136241392,
					"ProbMinInfoLoss" -> 5.004978377643246*^-205,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.5584,
			"Diffusivity" -> 1.6961091588254644,
			"PecletNumber" -> 0.329224093328218,
			"Randomness" -> 3.037444768670244
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-4.755128838793065 + 0.49453662333270837*#1^1.0145285281863692 & ),
					"AdjustedRSquared" -> 0.9999398189314436,
					"AIC" -> 92896.922122882,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0145285281863692
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.48553773155739033*#1^1.0164539889303636 & ),
					"AdjustedRSquared" -> 0.9999396853233039,
					"AIC" -> 92918.09878990392,
					"ProbMinInfoLoss" -> 0.00002520839432043931,
					"Exponent" -> 1.0164539889303636
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-31.811756975703474 + 0.5666777236227782*#1 & ),
					"AdjustedRSquared" -> 0.9997398629694317,
					"AIC" -> 93841.80204240758,
					"ProbMinInfoLoss" -> 6.636398315640608*^-206,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.5583,
			"Diffusivity" -> 1.6961208223242807,
			"PecletNumber" -> 0.32916287133067157,
			"Randomness" -> 3.0380097122054104
		}
	},
	4328 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4329 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4330 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4331 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	4332 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4333 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 12,
			"GrowthRate" -> 11/12
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 12,
			"GrowthRate" -> 11/12
		}
	},
	4334 -> {
		{{1}, 0} -> {
			"BoundaryWordCoding" -> {
				"A" -> {1, 2, 2},
				"B" -> {2, 2},
				"C" -> {0, 0},
				"D" -> {1, 2},
				"E" -> {1, 0}
			},
			"BoundaryWordMorphism" -> {
				"A" -> "AEDBB",
				"B" -> "BB",
				"C" -> "CC",
				"D" -> "DB",
				"E" -> "EC"
			},
			"GrowthRate" -> Missing["Nonexistent"],
			"GrowthRateLimInf" -> 6/5,
			"GrowthRateLimSup" -> 3/2
		}
	},
	4336 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4337 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4338 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4339 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	4340 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4341 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4342 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4343 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4344 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4345 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4346 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4347 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	4348 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4349 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4350 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4362 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4363 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4366 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4382 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4392 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4393 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4394 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4395 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4396 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4397 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4398 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4408 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4410 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4412 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4414 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4426 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4427 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4430 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4446 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4456 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4457 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4458 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4459 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4460 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4461 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4462 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4472 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 7/4
		}
	},
	4474 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4476 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4478 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4480 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4481 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4482 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4483 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4484 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4485 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4486 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4487 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4488 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4489 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4490 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4491 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4492 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4493 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4494 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4496 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4498 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4500 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 5/3
		}
	},
	4502 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4504 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4506 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4508 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4510 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4512 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4513 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4514 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4515 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4516 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	4517 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	4518 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4519 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4520 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4521 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4522 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4523 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		}
	},
	4524 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4525 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4526 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4528 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4530 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4532 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	4534 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4536 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4538 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4540 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4542 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4544 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4545 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4546 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4547 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4548 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4549 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4550 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4551 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4552 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4553 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4554 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4555 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4556 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4557 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4558 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4560 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4562 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4564 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4566 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4568 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4570 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4572 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4574 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4576 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4577 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4578 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4579 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4580 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 18,
			"GrowthRate" -> 5/3
		}
	},
	4581 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (39.951799663306424 + 0.88260264258996*#1^1.012713520506362 & ),
					"AdjustedRSquared" -> 0.9999934202232282,
					"AIC" -> 82171.64752620031,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.012713520506362
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-1.666760036000051 + 0.994301761831016*#1 & ),
					"AdjustedRSquared" -> 0.9999560071930803,
					"AIC" -> 87312.81638307814,
					"ProbMinInfoLoss" -> 4.067873720036423655470717836940086399835`12.54455789775804*^-1117,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0007000000000001,
			"Diffusivity" -> 2.0211037306971344,
			"PecletNumber" -> 0.49512550236836733,
			"Randomness" -> 2.0196899477337205
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (38.923574009558465 + 0.8827216819044612*#1^1.0126986860379898 & ),
					"AdjustedRSquared" -> 0.9999934209830093,
					"AIC" -> 82167.45250314295,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0126986860379898
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-2.646861326121726 + 0.9942976624989736*#1 & ),
					"AdjustedRSquared" -> 0.9999560590790937,
					"AIC" -> 87300.93224305466,
					"ProbMinInfoLoss" -> 1.90124461550639513360527818778788845231826`12.545207913505248*^-1115,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0005,
			"Diffusivity" -> 2.0211039707691514,
			"PecletNumber" -> 0.4950264877364274,
			"Randomness" -> 2.0200939238072477
		}
	},
	4582 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4583 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4584 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4585 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4586 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4587 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4588 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4589 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4590 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4592 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4594 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4596 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4598 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4600 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4602 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4604 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4606 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4616 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4617 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4618 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4619 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4620 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4621 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4622 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4634 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4635 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4636 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4637 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4638 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4648 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4649 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (14.450024878421791 + 1.2547663705255838*#1^1.0134220752745169 & ),
					"AdjustedRSquared" -> 0.9999941436332216,
					"AIC" -> 88079.1398557394,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0134220752745169
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.2829250547524815*#1^1.0110949523814075 & ),
					"AdjustedRSquared" -> 0.9999939441994141,
					"AIC" -> 88413.0119016089,
					"ProbMinInfoLoss" -> 3.1666962557446646*^-73,
					"Exponent" -> 1.0110949523814075
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-48.386882448224945 + 1.4229801984697983*#1 & ),
					"AdjustedRSquared" -> 0.9999569802801265,
					"AIC" -> 94258.49013569804,
					"ProbMinInfoLoss" -> 1.482981841565735568140942131516979314064587133`12.464676951714784*^-1342,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4205,
			"Diffusivity" -> 4.251512368680356,
			"PecletNumber" -> 0.3341163983114354,
			"Randomness" -> 2.992968932545129
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4650 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4651 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4652 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4653 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 46,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4654 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4664 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4665 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4666 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4667 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4668 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4669 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4670 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4680 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4681 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4682 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4683 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4684 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4685 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4686 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-7.874694689453466 + 1.7164188170561852*#1 & ),
					"AdjustedRSquared" -> 0.9999995910130618,
					"AIC" -> 51450.49001376608,
					"ProbMinInfoLoss" -> 3.0420737655229475269519891292837950349879458316762`12.824093602663476*^-587,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7157,
			"Diffusivity" -> 0.20346297482318745,
			"PecletNumber" -> 8.432492454663903,
			"Randomness" -> 0.11858889947146208
		}
	},
	4698 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4699 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4700 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4701 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4702 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4712 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4713 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4714 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4715 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4716 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4717 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4718 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (2.2579470147285616 + 1.7470563449625578*#1 & ),
					"AdjustedRSquared" -> 0.9999999399770791,
					"AIC" -> 32614.764272134464,
					"ProbMinInfoLoss" -> 1.5270590253387996977666487509443189559959652147335`12.99854949948189*^-375,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7473,
			"Diffusivity" -> 0.1888246236105907,
			"PecletNumber" -> 9.253560084427454,
			"Randomness" -> 0.10806651611663179
		}
	},
	4728 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4729 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 5/6
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4730 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4731 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4732 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4733 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4734 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4736 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4737 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4738 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4739 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4740 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4741 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4742 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4743 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4744 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4745 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4746 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4747 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4748 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4749 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	4750 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4752 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4753 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4754 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4755 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4756 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4757 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4758 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4759 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4760 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4761 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	4762 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4763 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4764 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4765 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4766 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4768 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4769 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4770 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4771 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	4772 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4773 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		}
	},
	4774 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4775 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4776 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4777 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		}
	},
	4778 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4779 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	4780 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4781 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-1.8300729072937978 + 0.6591513394475141*#1 & ),
					"AdjustedRSquared" -> 0.9999630876106721,
					"AIC" -> 77336.2049443045,
					"ProbMinInfoLoss" -> 1.2686293015147983*^-15,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6633,
			"Diffusivity" -> 6.653852542685755,
			"PecletNumber" -> 0.0996866094859785,
			"Randomness" -> 10.031437573776202
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-2.4794262826198255 + 0.6591485703994842*#1 & ),
					"AdjustedRSquared" -> 0.9999631389261486,
					"AIC" -> 77322.20877461637,
					"ProbMinInfoLoss" -> 7.779783547517738*^-16,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.663,
			"Diffusivity" -> 6.6533503120266015,
			"PecletNumber" -> 0.0996490443020204,
			"Randomness" -> 10.03521917349412
		}
	},
	4782 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4784 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4785 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4786 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4787 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	4788 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4789 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4790 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4791 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4792 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4793 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 2
		}
	},
	4794 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4795 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	4796 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4797 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4798 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4800 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4801 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4802 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4803 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4804 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4805 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4806 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4807 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4808 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4809 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4810 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4811 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4812 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4813 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (4.282369516975015 + 1.392644901606445*#1 & ),
					"AdjustedRSquared" -> 0.999906418541047,
					"AIC" -> 101599.75921856129,
					"ProbMinInfoLoss" -> 8.26258137013*^-16,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3962,
			"Diffusivity" -> 2.7407580125886164,
			"PecletNumber" -> 0.5094211140082755,
			"Randomness" -> 1.963012471414279
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (2.894667266735342 + 1.3926432222244307*#1 & ),
					"AdjustedRSquared" -> 0.9999064242998691,
					"AIC" -> 101599.11964348286,
					"ProbMinInfoLoss" -> 7.246980354019632*^-16,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3959000000000001,
			"Diffusivity" -> 2.7406956538822516,
			"PecletNumber" -> 0.5093232435431783,
			"Randomness" -> 1.963389679692135
		}
	},
	4814 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 4/3
		}
	},
	4816 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4817 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4818 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4819 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4820 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4821 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4822 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4823 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4824 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4825 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4826 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4827 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4828 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4829 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4830 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4832 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4833 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4834 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4835 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	4836 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4837 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4838 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4839 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4840 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4841 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4842 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4843 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	4844 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4845 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (7.8672877888032255 + 1.3779884635958821*#1 & ),
					"AdjustedRSquared" -> 0.9999957770904504,
					"AIC" -> 70404.1875872407,
					"ProbMinInfoLoss" -> 1.6786954726399542*^-145,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3784,
			"Diffusivity" -> 2.831565432998591,
			"PecletNumber" -> 0.4867978623896013,
			"Randomness" -> 2.0542407378109337
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (6.485801800203627 + 1.3779891007298881*#1 & ),
					"AdjustedRSquared" -> 0.9999957768854868,
					"AIC" -> 70404.68218618023,
					"ProbMinInfoLoss" -> 1.5462760567092876*^-145,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3781,
			"Diffusivity" -> 2.8314923910874783,
			"PecletNumber" -> 0.48670446875921836,
			"Randomness" -> 2.054634925685711
		}
	},
	4846 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	4848 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4849 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	4850 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4851 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	4852 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4853 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4854 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4856 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4857 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 7/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 7/4
		}
	},
	4858 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4859 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	4860 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	4861 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	4862 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4874 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4875 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4878 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4894 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4904 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4905 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4906 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4907 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4908 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4909 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4910 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4920 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 7,
			"GrowthRate" -> 10/7
		}
	},
	4922 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4924 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4926 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4938 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4939 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4942 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4958 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4968 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4969 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4970 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4971 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4972 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4973 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4974 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4984 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-7.874694689453466 + 1.7164188170561852*#1 & ),
					"AdjustedRSquared" -> 0.9999995910130618,
					"AIC" -> 51450.49001376608,
					"ProbMinInfoLoss" -> 3.0420737655229475269519891292837950349879458316762`12.824093602663476*^-587,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7157,
			"Diffusivity" -> 0.20346297482318745,
			"PecletNumber" -> 8.432492454663903,
			"Randomness" -> 0.11858889947146208
		}
	},
	4986 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4988 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4990 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4992 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	4993 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4994 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4995 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4996 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	4997 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	4998 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	4999 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5000 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5001 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5002 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5003 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5004 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5005 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5006 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5008 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5010 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5012 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 5/3
		}
	},
	5014 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5016 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5018 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5020 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5022 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5024 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5025 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5026 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5027 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5028 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-34.500065444710174 + 0.8425131616588829*#1^0.9742527987034062 & ),
					"AdjustedRSquared" -> 0.9999633067338407,
					"AIC" -> 91324.68505863758,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9742527987034062
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.7560579901741873*#1^0.9855794918938509 & ),
					"AdjustedRSquared" -> 0.9999584194570859,
					"AIC" -> 92574.07615476748,
					"ProbMinInfoLoss" -> 4.990805050079143*^-272,
					"Exponent" -> 0.9855794918938509
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (23.802647824799063 + 0.661649845450497*#1 & ),
					"AdjustedRSquared" -> 0.9997756715944504,
					"AIC" -> 95459.38388436679,
					"ProbMinInfoLoss" -> 1.4506339155703939665339634187253976250549552087`12.487427806115315*^-898,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.657,
			"Diffusivity" -> 2.8317055750384,
			"PecletNumber" -> 0.23201564660940804,
			"Randomness" -> 4.310054147699239
		}
	},
	5029 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5030 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5031 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5032 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5033 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5034 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5035 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5036 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5037 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5038 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5040 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5042 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5044 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5046 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5048 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-48.95156098721592 + 1.6742401547835764*#1^0.979986129362557 & ),
					"AdjustedRSquared" -> 0.9999840812297075,
					"AIC" -> 97775.50349630567,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.979986129362557
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.5551678900985146*#1^0.9877069368817909 & ),
					"AdjustedRSquared" -> 0.9999818311286209,
					"AIC" -> 99096.61206080996,
					"ProbMinInfoLoss" -> 1.3332764874700828*^-287,
					"Exponent" -> 0.9877069368817909
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (45.533325592570485 + 1.387572357645721*#1 & ),
					"AdjustedRSquared" -> 0.9998901603064502,
					"AIC" -> 103128.83813701425,
					"ProbMinInfoLoss" -> 3.4526525744736798383710972018602`12.526995373569887*^-1163,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.379,
			"Diffusivity" -> 0.23539171280600754,
			"PecletNumber" -> 5.858320089358753,
			"Randomness" -> 0.17069739869906275
		}
	},
	5050 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5052 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5054 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5056 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5057 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5058 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5059 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5060 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5061 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5062 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5063 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5064 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5065 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5066 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5067 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5068 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5069 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5070 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5072 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5074 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5076 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 5,
			"GrowthRate" -> 8/5
		}
	},
	5078 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5080 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5082 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5084 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5086 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5088 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5089 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5090 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5091 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5092 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	5093 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5094 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5095 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5096 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5097 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5098 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5099 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5100 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5101 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5102 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5104 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5106 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5108 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5110 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5112 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5114 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5116 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5118 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5160 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5161 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5162 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5163 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5164 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5165 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5166 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	5178 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5179 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5180 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5181 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5182 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5224 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5225 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5226 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5227 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 16,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5228 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5229 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5230 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 128,
			"GrowthRate" -> 3/2
		}
	},
	5242 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5243 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5244 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5245 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5246 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5248 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5249 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5250 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5251 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5252 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5253 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	5254 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5255 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 44,
			"GrowthRate" -> 14/11
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 44,
			"GrowthRate" -> 14/11
		}
	},
	5256 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5257 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5258 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5259 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5260 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5261 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	5262 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5264 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5265 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5266 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5267 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (4.9034586859017155 + 1.82032659560326*#1 & ),
					"AdjustedRSquared" -> 0.9999980186628594,
					"AIC" -> 68404.46365295119,
					"ProbMinInfoLoss" -> 3.0460913080344274305382794927931607433930598685859`12.910778076468343*^-355,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.8210000000000002,
			"Diffusivity" -> 0.14692097335358661,
			"PecletNumber" -> 12.394418294639934,
			"Randomness" -> 0.08068147905194212
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (3.0819369337114044 + 1.820326719941264*#1 & ),
					"AdjustedRSquared" -> 0.9999980186200982,
					"AIC" -> 68404.6808373661,
					"ProbMinInfoLoss" -> 1.03992214606601618358545422268054381853669067851906`13.010395255072627*^-354,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.8208000000000002,
			"Diffusivity" -> 0.14724943188457673,
			"PecletNumber" -> 12.365412733322167,
			"Randomness" -> 0.08087073368001797
		}
	},
	5268 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5269 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5270 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5271 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5272 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5273 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5274 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5275 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.9822171017335501 + 1.6945674798316719*#1 & ),
					"AdjustedRSquared" -> 0.9999892025910331,
					"AIC" -> 83928.12637130692,
					"ProbMinInfoLoss" -> 2.2828755830041697*^-53,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6974,
			"Diffusivity" -> 0.21102680382061012,
			"PecletNumber" -> 8.043527974971973,
			"Randomness" -> 0.12432355592117952
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.29252691270376097 + 1.6945659580216592*#1 & ),
					"AdjustedRSquared" -> 0.9999892054689292,
					"AIC" -> 83925.44266823803,
					"ProbMinInfoLoss" -> 3.4540187806178306*^-53,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6973,
			"Diffusivity" -> 0.2112663356753759,
			"PecletNumber" -> 8.033934959746777,
			"Randomness" -> 0.12447200593611966
		}
	},
	5276 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5277 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5278 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5280 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5281 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5282 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5283 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (8.828918331843454 + 1.5557253637972526*#1 & ),
					"AdjustedRSquared" -> 0.9999974477651664,
					"AIC" -> 67794.96327804342,
					"ProbMinInfoLoss" -> 9.481522384406221*^-153,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5566,
			"Diffusivity" -> 0.4576569879432432,
			"PecletNumber" -> 3.4012372606731467,
			"Randomness" -> 0.2940106565227054
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (7.270044884499513 + 1.5557258384392574*#1 & ),
					"AdjustedRSquared" -> 0.9999974474629599,
					"AIC" -> 67796.15339836357,
					"ProbMinInfoLoss" -> 5.154691176039597*^-153,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5564,
			"Diffusivity" -> 0.4578796547388286,
			"PecletNumber" -> 3.399146443595009,
			"Randomness" -> 0.2941915026592319
		}
	},
	5284 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5285 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	5286 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (11.674937053704637 + 1.2934018324060188*#1 & ),
					"AdjustedRSquared" -> 0.9999954651684857,
					"AIC" -> 69849.84696083664,
					"ProbMinInfoLoss" -> 5.7667070475895010142134598854941583755378`12.630297424764468*^-885,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2954,
			"Diffusivity" -> 0.2081717473607733,
			"PecletNumber" -> 6.222746440971163,
			"Randomness" -> 0.1607007467660748
		}
	},
	5287 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.3499060306034525 + 1.1315667845276676*#1 & ),
					"AdjustedRSquared" -> 0.9999802405795271,
					"AIC" -> 81894.97113544651,
					"ProbMinInfoLoss" -> 1.2271151996596996*^-74,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1317000000000002,
			"Diffusivity" -> 1.21919721478049,
			"PecletNumber" -> 0.9282337478139308,
			"Randomness" -> 1.0773148491477333
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-4.478796159609921 + 1.131566242607661*#1 & ),
					"AdjustedRSquared" -> 0.9999802405889481,
					"AIC" -> 81894.95678932012,
					"ProbMinInfoLoss" -> 1.1323610265276875*^-74,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1316000000000002,
			"Diffusivity" -> 1.2193235726853342,
			"PecletNumber" -> 0.9280555427201829,
			"Randomness" -> 1.0775217149923417
		}
	},
	5288 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5289 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5290 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5291 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.3446799279935659 + 1.4013344625393462*#1 & ),
					"AdjustedRSquared" -> 0.9999877128260518,
					"AIC" -> 81420.5875382706,
					"ProbMinInfoLoss" -> 9.814003152031005*^-113,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4028,
			"Diffusivity" -> 0.6778715078949383,
			"PecletNumber" -> 2.069418737418621,
			"Randomness" -> 0.48322747925216586
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-1.742475607542438 + 1.401333481773332*#1 & ),
					"AdjustedRSquared" -> 0.9999877141734507,
					"AIC" -> 81419.4768771755,
					"ProbMinInfoLoss" -> 8.109705444432761*^-113,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4026,
			"Diffusivity" -> 0.6780326362302164,
			"PecletNumber" -> 2.068631987684686,
			"Randomness" -> 0.48341126210624297
		}
	},
	5292 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5293 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	5294 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 13/10
		}
	},
	5296 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5297 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5298 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5299 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	5300 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5301 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5302 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5304 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5305 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5306 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5307 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5308 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5309 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5310 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5312 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5313 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5314 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5315 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5316 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5317 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	5318 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5319 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		}
	},
	5320 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5321 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5322 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5323 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5324 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5325 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	5326 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5328 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5329 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5330 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5331 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 7/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 7/5
		}
	},
	5332 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5333 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5334 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5335 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5336 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5337 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5338 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5339 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (44.14725964021989 + 1.2077658602397983*#1^1.0206945745833458 & ),
					"AdjustedRSquared" -> 0.9999926705224876,
					"AIC" -> 90911.28839918703,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0206945745833458
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.290629675923117*#1^1.0137336335205682 & ),
					"AdjustedRSquared" -> 0.999990899687239,
					"AIC" -> 93074.3341456646,
					"ProbMinInfoLoss" -> 1.99794762949203040271267050243332271369311052296412`12.920554061379976*^-470,
					"Exponent" -> 1.0137336335205682
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-54.97068286826311 + 1.4662296136122932*#1 & ),
					"AdjustedRSquared" -> 0.9999242976081492,
					"AIC" -> 100509.14465940725,
					"ProbMinInfoLoss" -> 7.1120375818015321502778779430040064`12.273445524307409*^-2085,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4609,
			"Diffusivity" -> 0.7544008251595313,
			"PecletNumber" -> 1.9365037143100514,
			"Randomness" -> 0.5163945685259301
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (42.7323483186771 + 1.2076935316143522*#1^1.0207007180565892 & ),
					"AdjustedRSquared" -> 0.99999267074609,
					"AIC" -> 90907.97139935184,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0207007180565892
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.2878233117404696*#1^1.0139618111550104 & ),
					"AdjustedRSquared" -> 0.9999910107734212,
					"AIC" -> 92948.50253540973,
					"ProbMinInfoLoss" -> 8.0222045079511776043009327997460533365`12.83054181034091*^-444,
					"Exponent" -> 1.0139618111550104
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-56.41418919889025 + 1.4662261552242577*#1 & ),
					"AdjustedRSquared" -> 0.9999242797884108,
					"AIC" -> 100511.45130676116,
					"ProbMinInfoLoss" -> 4.274000530077730561243201017260734`12.27319113378053*^-2086,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4607,
			"Diffusivity" -> 0.7545852004684365,
			"PecletNumber" -> 1.9357655028129588,
			"Randomness" -> 0.5165914975480499
		}
	},
	5340 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5341 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5342 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5344 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5345 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5346 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5347 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.9727909390965948 + 1.590844717340447*#1 & ),
					"AdjustedRSquared" -> 0.9999998920663438,
					"AIC" -> 36609.324383696585,
					"ProbMinInfoLoss" -> 2.76760734228783754455392595676403474917350355369`12.823324395454428*^-434,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.591,
			"Diffusivity" -> 0.24193245489782025,
			"PecletNumber" -> 6.576215665946746,
			"Randomness" -> 0.15206313947066014
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.3814730873261579 + 1.5908448009024452*#1 & ),
					"AdjustedRSquared" -> 0.9999998920627069,
					"AIC" -> 36609.66238858515,
					"ProbMinInfoLoss" -> 4.13439948844289806807555707738689975538022754813`12.955501621130558*^-434,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5908,
			"Diffusivity" -> 0.242168885822369,
			"PecletNumber" -> 6.568969397525546,
			"Randomness" -> 0.15223088120591463
		}
	},
	5348 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5349 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	5350 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5351 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	5352 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5353 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5354 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5355 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-13.103246384642555 + 1.2035266966072666*#1 & ),
					"AdjustedRSquared" -> 0.9999912440409582,
					"AIC" -> 74988.96155575039,
					"ProbMinInfoLoss" -> 3.1135932422873405*^-82,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2024000000000001,
			"Diffusivity" -> 0.6939689368016617,
			"PecletNumber" -> 1.73264239396878,
			"Randomness" -> 0.5771531410526128
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-14.300764416430614 + 1.2035257403092543*#1 & ),
					"AdjustedRSquared" -> 0.9999912424077853,
					"AIC" -> 74990.81071961448,
					"ProbMinInfoLoss" -> 7.339254369124498*^-82,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2022000000000002,
			"Diffusivity" -> 0.6940498810833273,
			"PecletNumber" -> 1.7321521590400857,
			"Randomness" -> 0.5773164873426445
		}
	},
	5356 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5357 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	5358 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (12.998219981996812 + 1.2038652494786528*#1 & ),
					"AdjustedRSquared" -> 0.9999802422975642,
					"AIC" -> 83132.78588770631,
					"ProbMinInfoLoss" -> 4.075692150774513*^-165,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2017,
			"Diffusivity" -> 0.16104525035420125,
			"PecletNumber" -> 7.461877934040237,
			"Randomness" -> 0.1340145213898654
		}
	},
	5360 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5361 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5362 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5363 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	5364 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5365 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5366 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5368 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5369 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5370 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5371 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-52.735463648631786 + 1.4148675000229383*#1^0.9703644500548728 & ),
					"AdjustedRSquared" -> 0.9999889342602298,
					"AIC" -> 89024.13494384875,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9703644500548728
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.2779622558034502*#1^0.9810097509241843 & ),
					"AdjustedRSquared" -> 0.9999846610813972,
					"AIC" -> 92288.52989552391,
					"ProbMinInfoLoss" -> 1.398436875286315638659290745418947774959475`12.656054401728536*^-709,
					"Exponent" -> 0.9810097509241843
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (56.35206552655903 + 1.071275779316757*#1 & ),
					"AdjustedRSquared" -> 0.9998548869620929,
					"AIC" -> 100739.99207839073,
					"ProbMinInfoLoss" -> 8.589103790736581814857402057096908618`12.186845698685167*^-2545,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0718,
			"Diffusivity" -> 1.0404523348914207,
			"PecletNumber" -> 1.0301288815040726,
			"Randomness" -> 0.9707523184282708
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-53.833927236767984 + 1.4148555050204992*#1^0.9703659868151034 & ),
					"AdjustedRSquared" -> 0.9999889276497032,
					"AIC" -> 89027.15109511332,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9703659868151034
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.2752261208860909*#1^0.9812346422926029 & ),
					"AdjustedRSquared" -> 0.9999844721825848,
					"AIC" -> 92407.97185443329,
					"ProbMinInfoLoss" -> 7.31307389351153587042538116850866644`12.548371997616512*^-735,
					"Exponent" -> 0.9812346422926029
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (55.24842388239283 + 1.0712821670068216*#1 & ),
					"AdjustedRSquared" -> 0.9998548840064532,
					"AIC" -> 100740.31503784981,
					"ProbMinInfoLoss" -> 3.3019236028769188084586880258584311025`12.186945543944692*^-2544,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0716,
			"Diffusivity" -> 1.0404810234974287,
			"PecletNumber" -> 1.0299082595451567,
			"Randomness" -> 0.9709602682880073
		}
	},
	5372 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5373 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5374 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5418 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5419 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5422 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5438 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5482 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5483 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5486 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5502 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5504 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5505 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5506 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5507 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (8.237169216942277 + 1.2924711190447078*#1 & ),
					"AdjustedRSquared" -> 0.999997079218719,
					"AIC" -> 65436.066047939465,
					"ProbMinInfoLoss" -> 1.210601634535948846857089161907862908328539916`12.45854244275894*^-1361,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2928000000000002,
			"Diffusivity" -> 0.20710100615982782,
			"PecletNumber" -> 6.242364650813414,
			"Randomness" -> 0.16019570402214403
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (6.940813261324657 + 1.2924718501627193*#1 & ),
					"AdjustedRSquared" -> 0.9999970790219768,
					"AIC" -> 65436.750935860364,
					"ProbMinInfoLoss" -> 2.517233369169600637351805020566316738603639564`12.458643909635848*^-1361,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2927,
			"Diffusivity" -> 0.20725959373292802,
			"PecletNumber" -> 6.237105731596464,
			"Randomness" -> 0.16033077568881257
		}
	},
	5508 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5509 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5510 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5511 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5512 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5513 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5514 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5515 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5516 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5517 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5518 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5520 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5522 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5524 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 5/3
		}
	},
	5526 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5528 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5530 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5532 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5534 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5536 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5537 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5538 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5539 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (10.012482928292014 + 1.2301704863657044*#1 & ),
					"AdjustedRSquared" -> 0.9999917454133702,
					"AIC" -> 74837.23365569295,
					"ProbMinInfoLoss" -> 4.0779594951194685*^-57,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2319,
			"Diffusivity" -> 0.17815264222961605,
			"PecletNumber" -> 6.914856746341364,
			"Randomness" -> 0.14461615571849668
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (8.780164416442279 + 1.2301705900577051*#1 & ),
					"AdjustedRSquared" -> 0.9999917451914428,
					"AIC" -> 74837.50419319278,
					"ProbMinInfoLoss" -> 2.3317122889821876*^-57,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2318,
			"Diffusivity" -> 0.17829904614786343,
			"PecletNumber" -> 6.908618002243647,
			"Randomness" -> 0.14474674959235542
		}
	},
	5540 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 9/5
		}
	},
	5541 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 3/2
		}
	},
	5542 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5543 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5544 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5545 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (71.22159831400397 + 0.5101121392482416*#1^1.0573270497106946 & ),
					"AdjustedRSquared" -> 0.9999653604639014,
					"AIC" -> 95872.0099264186,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0573270497106946
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.6156835134805976*#1^1.0375579370142023 & ),
					"AdjustedRSquared" -> 0.9999513824208304,
					"AIC" -> 99260.90502929491,
					"ProbMinInfoLoss" -> 1.2905609972923886851881518448822095`12.531192519651558*^-736,
					"Exponent" -> 1.0375579370142023
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-86.48577347733402 + 0.8723558591095564*#1 & ),
					"AdjustedRSquared" -> 0.9995181412974923,
					"AIC" -> 108636.57740952275,
					"ProbMinInfoLoss" -> 1.61953039471832608315334189795844399139375`12.026386271823833*^-2772,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8682000000000001,
			"Diffusivity" -> 1.128052633228916,
			"PecletNumber" -> 0.7696449389199874,
			"Randomness" -> 1.2993004298881778
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (70.41014489062063 + 0.5100738900460289*#1^1.0573341003260555 & ),
					"AdjustedRSquared" -> 0.999965345637459,
					"AIC" -> 95873.22795265628,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0573341003260555
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.6143375465683071*#1^1.0377870377873262 & ),
					"AdjustedRSquared" -> 0.9999516772960173,
					"AIC" -> 99197.00711470001,
					"ProbMinInfoLoss" -> 1.780432157294935655016424505529913654108213099553`12.733987605102685*^-722,
					"Exponent" -> 1.0377870377873262
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-87.31414689469123 + 0.8723479145874801*#1 & ),
					"AdjustedRSquared" -> 0.9995180438248088,
					"AIC" -> 108638.41888758383,
					"ProbMinInfoLoss" -> 1.18579130032424511610969792871948876433226`12.149592450720572*^-2772,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8681000000000001,
			"Diffusivity" -> 1.1281262753200705,
			"PecletNumber" -> 0.7695060552983787,
			"Randomness" -> 1.2995349329801527
		}
	},
	5546 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5547 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5548 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5549 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5550 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5552 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5554 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5556 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	5558 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5560 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 37,
			"GrowthRate" -> 38/37
		}
	},
	5562 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5564 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5566 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5568 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5569 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5570 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5571 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.6923321332124762 + 1.2996271308602687*#1 & ),
					"AdjustedRSquared" -> 0.999999627003908,
					"AIC" -> 44966.084164751745,
					"ProbMinInfoLoss" -> 1.3031259903045362*^-32,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2992000000000001,
			"Diffusivity" -> 0.2097123495106062,
			"PecletNumber" -> 6.195152565081978,
			"Randomness" -> 0.1614165251774986
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.6081649565004047 + 1.2996274102502725*#1 & ),
					"AdjustedRSquared" -> 0.9999996271785216,
					"AIC" -> 44961.405979530544,
					"ProbMinInfoLoss" -> 8.191852967354982*^-33,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2991000000000001,
			"Diffusivity" -> 0.209872217467796,
			"PecletNumber" -> 6.189956992279559,
			"Randomness" -> 0.16155201098283117
		}
	},
	5572 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5573 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5574 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5575 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5576 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5577 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5578 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5579 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5580 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5581 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5582 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5584 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5586 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5588 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	5590 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5592 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5594 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5596 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5598 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5600 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5601 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5602 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5603 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (2.2092054005421238 + 1.0238152973901526*#1 & ),
					"AdjustedRSquared" -> 0.9999958600826847,
					"AIC" -> 64263.9280601644,
					"ProbMinInfoLoss" -> 1.58749596040728020013881843085234687725401`12.570300764824708*^-980,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0232,
			"Diffusivity" -> 0.022666239418500763,
			"PecletNumber" -> 45.142027360958615,
			"Randomness" -> 0.02215230592113053
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.183233483359218 + 1.0238158717161565*#1 & ),
					"AdjustedRSquared" -> 0.9999958608715631,
					"AIC" -> 64262.03354836292,
					"ProbMinInfoLoss" -> 2.636885407626819025270902745459294572103293`12.48833721518129*^-979,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0231000000000001,
			"Diffusivity" -> 0.02277089081182573,
			"PecletNumber" -> 44.93017020961991,
			"Randomness" -> 0.022256759663596644
		}
	},
	5604 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 29,
			"GrowthRate" -> 49/29
		}
	},
	5605 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-2.3319834983226615 + 1.3899101656830977*#1 & ),
					"AdjustedRSquared" -> 0.9999954010652178,
					"AIC" -> 71429.48115804399,
					"ProbMinInfoLoss" -> 4.968654559359774020124475110071587635573537710754`12.722377877858992*^-742,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3918000000000001,
			"Diffusivity" -> 0.7156205318471435,
			"PecletNumber" -> 1.9448855057407557,
			"Randomness" -> 0.514169084528771
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.7163135313248503 + 1.3899086918370838*#1 & ),
					"AdjustedRSquared" -> 0.9999954037878412,
					"AIC" -> 71423.53805194472,
					"ProbMinInfoLoss" -> 4.905612037853239481271028197517885088245309200227`12.722960872340378*^-741,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3916000000000002,
			"Diffusivity" -> 0.7157772588621134,
			"PecletNumber" -> 1.944180235919002,
			"Randomness" -> 0.5143556042412427
		}
	},
	5606 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5607 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5608 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5609 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5610 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5611 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5612 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5613 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5614 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5616 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5618 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5620 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5622 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5624 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5626 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5628 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5630 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5672 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5673 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (20.677115871597785 + 1.5014841884068408*#1 & ),
					"AdjustedRSquared" -> 0.9999964325506653,
					"AIC" -> 70434.03168767945,
					"ProbMinInfoLoss" -> 1.80456629728810773229364522680413635430149`12.925039521481075*^-363,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5034,
			"Diffusivity" -> 2.7403111585413393,
			"PecletNumber" -> 0.5486238288356481,
			"Randomness" -> 1.8227425559008508
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5674 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5675 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5676 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5677 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5678 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 58,
			"GrowthRate" -> 83/58
		}
	},
	5690 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5691 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5692 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5693 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5694 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5736 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5737 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5738 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5739 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5740 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5741 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 22,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5742 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-4.725758475845216 + 1.7449388778073889*#1 & ),
					"AdjustedRSquared" -> 0.9999998420307775,
					"AIC" -> 42267.24731936937,
					"ProbMinInfoLoss" -> 1.444972312374376981155102696856553009748504`12.469868354832245*^-1132,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7444000000000002,
			"Diffusivity" -> 0.1902512715764475,
			"PecletNumber" -> 9.16892689097775,
			"Randomness" -> 0.1090640171843886
		}
	},
	5754 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5755 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5756 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5757 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5758 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5760 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5761 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5762 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5763 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5764 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5765 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	5766 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5767 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5768 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5769 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5770 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5771 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (3.1698850285168745 + 0.9895118118131159*#1 & ),
					"AdjustedRSquared" -> 0.9999090105254943,
					"AIC" -> 94483.88243461186,
					"ProbMinInfoLoss" -> 2.441795702525725*^-25,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9873000000000001,
			"Diffusivity" -> 1.0135414021498168,
			"PecletNumber" -> 0.9741091956439508,
			"Randomness" -> 1.0265789548767514
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (2.174446144614486 + 0.9895134594251352*#1 & ),
					"AdjustedRSquared" -> 0.9999090186108677,
					"AIC" -> 94483.02701041356,
					"ProbMinInfoLoss" -> 2.909344927850102*^-25,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9872000000000001,
			"Diffusivity" -> 1.013638871388639,
			"PecletNumber" -> 0.9739168730255787,
			"Randomness" -> 1.026781676852349
		}
	},
	5772 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5773 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	5774 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-1.1269411940965806 + 1.3151222360152186*#1 & ),
					"AdjustedRSquared" -> 0.9999994595705268,
					"AIC" -> 48911.09215951183,
					"ProbMinInfoLoss" -> 2.5204839548944870311329778338481`12.787372951768216*^-585,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3161,
			"Diffusivity" -> 0.2162140398876855,
			"PecletNumber" -> 6.087023769056168,
			"Randomness" -> 0.1642838993144028
		}
	},
	5776 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5777 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5778 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5779 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5780 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5781 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5782 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5783 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5784 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5785 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-13.280953502284328 + 2.1444893880227966*#1^0.9881994739772415 & ),
					"AdjustedRSquared" -> 0.9999985333096367,
					"AIC" -> 80423.53214031337,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9881994739772415
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (2.1133896136438723*#1^0.9897290604826892 & ),
					"AdjustedRSquared" -> 0.9999984464553034,
					"AIC" -> 80997.8405120598,
					"ProbMinInfoLoss" -> 1.9521879145153674*^-125,
					"Exponent" -> 0.9897290604826892
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (63.15416675668328 + 1.9197617904696143*#1 & ),
					"AdjustedRSquared" -> 0.999978447124796,
					"AIC" -> 93335.73578101984,
					"ProbMinInfoLoss" -> 1.41450606865357592663780853268935409755016577465`12.100399381529776*^-2804,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.9187,
			"Diffusivity" -> 2.403086517893638,
			"PecletNumber" -> 0.7984315111891127,
			"Randomness" -> 1.2524555782006763
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-15.240629935364428 + 2.1444984053393483*#1^0.9881994785962418 & ),
					"AdjustedRSquared" -> 0.9999985341664744,
					"AIC" -> 80414.72117009263,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9881994785962418
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (2.1088427447038356*#1^0.989955026332893 & ),
					"AdjustedRSquared" -> 0.9999984196828893,
					"AIC" -> 81165.73631771446,
					"ProbMinInfoLoss" -> 8.301045245846498*^-164,
					"Exponent" -> 0.989955026332893
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (61.19478445841117 + 1.9197699461137043*#1 & ),
					"AdjustedRSquared" -> 0.9999784524680864,
					"AIC" -> 93333.34123095169,
					"ProbMinInfoLoss" -> 5.718694309488484943677580463243174932066391419`12.009759135351882*^-2806,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.9184,
			"Diffusivity" -> 2.4033377532592226,
			"PecletNumber" -> 0.7982232199358633,
			"Randomness" -> 1.2527823984879185
		}
	},
	5786 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5787 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5788 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5789 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5790 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5792 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5793 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5794 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5795 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (16.990324452475765 + 1.5698303520742982*#1 & ),
					"AdjustedRSquared" -> 0.9999766148729817,
					"AIC" -> 90126.99298485136,
					"ProbMinInfoLoss" -> 4.1896539792654915*^-141,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5709000000000002,
			"Diffusivity" -> 0.9347275395673194,
			"PecletNumber" -> 1.6805966803194456,
			"Randomness" -> 0.5950267614535102
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (15.412838823903007 + 1.5698316890663138*#1 & ),
					"AdjustedRSquared" -> 0.9999766138613598,
					"AIC" -> 90127.44261115187,
					"ProbMinInfoLoss" -> 3.225330425725709*^-141,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5707,
			"Diffusivity" -> 0.9349559280793053,
			"PecletNumber" -> 1.6799722348696304,
			"Randomness" -> 0.5952479328193196
		}
	},
	5796 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5797 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5798 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5799 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	5800 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5801 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (4.640069126951277 + 1.9957660095736545*#1 & ),
					"AdjustedRSquared" -> 0.9999712580147819,
					"AIC" -> 96990.8415317612,
					"ProbMinInfoLoss" -> 3.488979477371181*^-133,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.9977,
			"Diffusivity" -> 2.1620275650289575,
			"PecletNumber" -> 0.9239937696970314,
			"Randomness" -> 1.0822583796510774
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (2.6457879388076257 + 1.9957653458776525*#1 & ),
					"AdjustedRSquared" -> 0.9999712586069942,
					"AIC" -> 96990.62882837284,
					"ProbMinInfoLoss" -> 5.374096740902146*^-133,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.9974,
			"Diffusivity" -> 2.162326214617861,
			"PecletNumber" -> 0.9237274128654044,
			"Randomness" -> 1.0825704488924908
		}
	},
	5802 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5803 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (14.106588058822675 + 1.1303685655316833*#1 & ),
					"AdjustedRSquared" -> 0.9999566932308269,
					"AIC" -> 89720.80323182113,
					"ProbMinInfoLoss" -> 7.243863242483028915455706084584285951851615251283`12.996723536451137*^-395,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1361,
			"Diffusivity" -> 1.3378425059949484,
			"PecletNumber" -> 0.8492030974565925,
			"Randomness" -> 1.1775746025833538
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (12.97962100211473 + 1.1303667591236655*#1 & ),
					"AdjustedRSquared" -> 0.9999567090182307,
					"AIC" -> 89717.12496607382,
					"ProbMinInfoLoss" -> 1.09998987249372002279090724572290167550129147854549`12.998027271128349*^-393,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1360000000000001,
			"Diffusivity" -> 1.3379697441638543,
			"PecletNumber" -> 0.8490475998842019,
			"Randomness" -> 1.1777902677498717
		}
	},
	5804 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5805 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		}
	},
	5806 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (77.65744439351892 + 0.9205870718058877*#1^1.0494568747033624 & ),
					"AdjustedRSquared" -> 0.9999934948705514,
					"AIC" -> 89469.23647135436,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0494568747033624
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.0393503337828218*#1^1.0367097432395174 & ),
					"AdjustedRSquared" -> 0.9999875911615973,
					"AIC" -> 95926.41653682201,
					"ProbMinInfoLoss" -> 6.936884377953374868541202505328185335653654`12.44557686850775*^-1403,
					"Exponent" -> 1.0367097432395174
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-152.17196861684442 + 1.4626833453888302*#1 & ),
					"AdjustedRSquared" -> 0.9997130420312367,
					"AIC" -> 113788.0861605163,
					"ProbMinInfoLoss" -> 1.693896541026937832121723130556719478`11.68516908024043*^-5281,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4576,
			"Diffusivity" -> 0.2482309443186767,
			"PecletNumber" -> 5.871951234769289,
			"Randomness" -> 0.17030114182126557
		}
	},
	5808 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5809 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5810 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5811 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-18.717492289215446 + 1.4897358448733555*#1 & ),
					"AdjustedRSquared" -> 0.9999803673427394,
					"AIC" -> 87330.52212791954,
					"ProbMinInfoLoss" -> 1.0968689052071585*^-16,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4871,
			"Diffusivity" -> 0.753960653116722,
			"PecletNumber" -> 1.9723840943855984,
			"Randomness" -> 0.5070006409230865
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-20.200869786975094 + 1.4897351204453502*#1 & ),
					"AdjustedRSquared" -> 0.9999803655377033,
					"AIC" -> 87331.43178296214,
					"ProbMinInfoLoss" -> 1.5174925414996464*^-16,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4869,
			"Diffusivity" -> 0.7541555115703609,
			"PecletNumber" -> 1.9716092731376609,
			"Randomness" -> 0.5071998867242995
		}
	},
	5812 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5813 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5814 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5816 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5817 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-7.092123852383231 + 1.6847224325272228*#1 & ),
					"AdjustedRSquared" -> 0.9999686214761776,
					"AIC" -> 94479.97301219491,
					"ProbMinInfoLoss" -> 9.586673303421011370345543390197164606055`12.777448708170352*^-654,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6855,
			"Diffusivity" -> 2.5398507244203117,
			"PecletNumber" -> 0.6636216781538189,
			"Randomness" -> 1.5068826605875476
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-8.77063498349686 + 1.6847210548912095*#1 & ),
					"AdjustedRSquared" -> 0.999968622083305,
					"AIC" -> 94479.7631648618,
					"ProbMinInfoLoss" -> 2.6155250396240318109261225764571985739265`12.777738697341844*^-653,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6852,
			"Diffusivity" -> 2.5399619978001002,
			"PecletNumber" -> 0.6634744935001301,
			"Randomness" -> 1.5072169462378946
		}
	},
	5818 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5819 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-4.295921872166802 + 1.2445893854358903*#1 & ),
					"AdjustedRSquared" -> 0.9999952980964864,
					"AIC" -> 69442.24037908197,
					"ProbMinInfoLoss" -> 3.427206846215342*^-94,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2431,
			"Diffusivity" -> 0.7165397876054859,
			"PecletNumber" -> 1.7348652810392562,
			"Randomness" -> 0.5764136333404278
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-5.540513111302864 + 1.2445897036518956*#1 & ),
					"AdjustedRSquared" -> 0.9999952987520389,
					"AIC" -> 69440.85116116145,
					"ProbMinInfoLoss" -> 5.106039788959372*^-95,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2431,
			"Diffusivity" -> 0.7165397876054859,
			"PecletNumber" -> 1.7348652810392562,
			"Randomness" -> 0.5764136333404278
		}
	},
	5820 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5821 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	5822 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5824 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5825 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5826 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5827 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 5/3
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 5/3
		}
	},
	5828 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5829 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	5830 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5831 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5832 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5833 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5834 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5835 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (5.9221023102418995 + 0.5985187476631858*#1 & ),
					"AdjustedRSquared" -> 0.9999429861693357,
					"AIC" -> 79753.96608875648,
					"ProbMinInfoLoss" -> 3.941719006538048*^-47,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6021000000000001,
			"Diffusivity" -> 3.333626481271852,
			"PecletNumber" -> 0.1806141160032679,
			"Randomness" -> 5.5366658051351125
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (5.327594599470905 + 0.5985172493551708*#1 & ),
					"AdjustedRSquared" -> 0.9999430150112262,
					"AIC" -> 79748.85569980646,
					"ProbMinInfoLoss" -> 8.61910526989137*^-47,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6021000000000001,
			"Diffusivity" -> 3.333626481271852,
			"PecletNumber" -> 0.1806141160032679,
			"Randomness" -> 5.5366658051351125
		}
	},
	5836 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5837 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	5838 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 7/4
		}
	},
	5840 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5841 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5842 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5843 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (9.988028802882184 + 1.5414274514942743*#1 & ),
					"AdjustedRSquared" -> 0.9999833633091001,
					"AIC" -> 86356.855715169,
					"ProbMinInfoLoss" -> 2.3206081059081836*^-9,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5463,
			"Diffusivity" -> 0.5005265679598566,
			"PecletNumber" -> 3.089346498234269,
			"Randomness" -> 0.3236930530685227
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (8.450755955612987 + 1.5414256662422534*#1 & ),
					"AdjustedRSquared" -> 0.9999833704442925,
					"AIC" -> 86352.5427312728,
					"ProbMinInfoLoss" -> 3.22500774792982*^-9,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5461,
			"Diffusivity" -> 0.5007451135191535,
			"PecletNumber" -> 3.0875987768193403,
			"Randomness" -> 0.3238762780668479
		}
	},
	5844 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5845 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5846 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5848 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5849 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-16.39990783074173 + 1.9208458169844513*#1 & ),
					"AdjustedRSquared" -> 0.9999976765735862,
					"AIC" -> 71072.17136844019,
					"ProbMinInfoLoss" -> 5.7524928534411718688451832549755924879`12.501715804263936*^-830,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.9201000000000001,
			"Diffusivity" -> 1.6535620355394212,
			"PecletNumber" -> 1.1611901813974759,
			"Randomness" -> 0.8611853734385818
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-18.312004800463335 + 1.9208442365364404*#1 & ),
					"AdjustedRSquared" -> 0.9999976758457643,
					"AIC" -> 71075.28696711133,
					"ProbMinInfoLoss" -> 4.2629159082652270258460602102527270127`12.673625605943975*^-830,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.9198000000000002,
			"Diffusivity" -> 1.653814111157065,
			"PecletNumber" -> 1.160831793034371,
			"Randomness" -> 0.8614512507329225
		}
	},
	5850 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5851 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	5852 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5853 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5854 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5856 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5857 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5858 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5859 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-1.8749014701478885 + 1.4868146588281472*#1 & ),
					"AdjustedRSquared" -> 0.9999973712148069,
					"AIC" -> 67184.37079244651,
					"ProbMinInfoLoss" -> 4.017285953683120990202242020584451311`12.29430823477774*^-1987,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4876,
			"Diffusivity" -> 0.5657356093680982,
			"PecletNumber" -> 2.6294968451103578,
			"Randomness" -> 0.380300893632763
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.35861992197868 + 1.486813902594137*#1 & ),
					"AdjustedRSquared" -> 0.9999973716813354,
					"AIC" -> 67182.5857651893,
					"ProbMinInfoLoss" -> 7.18367758967572825615172091778647475566`12.294800969359152*^-1985,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4874,
			"Diffusivity" -> 0.5659306678817512,
			"PecletNumber" -> 2.628237140014448,
			"Randomness" -> 0.3804831705538195
		}
	},
	5860 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5861 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5862 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5863 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	5864 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5865 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5866 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5867 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-26.4205414341396 + 1.0115482934574822*#1 & ),
					"AdjustedRSquared" -> 0.9999674989798721,
					"AIC" -> 84629.08795058483,
					"ProbMinInfoLoss" -> 1.4706113450864253*^-214,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0109000000000001,
			"Diffusivity" -> 1.3726557092596636,
			"PecletNumber" -> 0.7364556116881086,
			"Randomness" -> 1.3578550887918324
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-27.417132793269126 + 1.0115454520134521*#1 & ),
					"AdjustedRSquared" -> 0.9999674946490824,
					"AIC" -> 84630.36423386162,
					"ProbMinInfoLoss" -> 7.32240487431854*^-215,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0109000000000001,
			"Diffusivity" -> 1.3726557092596636,
			"PecletNumber" -> 0.7364556116881086,
			"Randomness" -> 1.3578550887918324
		}
	},
	5868 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5869 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	5870 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 636,
			"GrowthRate" -> 515/318
		}
	},
	5872 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5873 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	5874 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5875 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5876 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5877 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5878 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5880 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5881 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (6.889714731499554 + 1.8234945875949413*#1 & ),
					"AdjustedRSquared" -> 0.9999981466215928,
					"AIC" -> 67771.62096735222,
					"ProbMinInfoLoss" -> 6.788586456676976*^-160,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.8243,
			"Diffusivity" -> 1.8207257012958746,
			"PecletNumber" -> 1.0019631176192996,
			"Randomness" -> 0.9980407286607874
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (5.064097209733446 + 1.8234948710709469*#1 & ),
					"AdjustedRSquared" -> 0.9999981465019053,
					"AIC" -> 67772.26983721298,
					"ProbMinInfoLoss" -> 6.788286722643494*^-160,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.824,
			"Diffusivity" -> 1.820920279665494,
			"PecletNumber" -> 1.0016912988277948,
			"Randomness" -> 0.9983115568341523
		}
	},
	5882 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5883 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	5884 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	5885 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	5886 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	5930 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5931 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5934 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5950 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5994 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	5995 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	5998 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6014 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6016 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6017 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6018 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6019 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 46,
			"GrowthRate" -> 65/46
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 46,
			"GrowthRate" -> 65/46
		}
	},
	6020 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6021 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6022 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6023 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6024 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6025 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6026 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6027 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6028 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6029 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6030 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6032 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6034 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6036 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 5/3
		}
	},
	6038 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6040 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6042 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6044 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6046 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6048 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6049 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6050 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6051 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		}
	},
	6052 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (15.68279099910637 + 1.4374148003201461*#1 & ),
					"AdjustedRSquared" -> 0.9999749322938787,
					"AIC" -> 89059.38497335804,
					"ProbMinInfoLoss" -> 6.22655858365813454024686420121591`12.826552282890452*^-584,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4375,
			"Diffusivity" -> 0.7980342143036068,
			"PecletNumber" -> 1.8013012152046814,
			"Randomness" -> 0.5551542360372916
		}
	},
	6053 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6054 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6055 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6056 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6057 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6058 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6059 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6060 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6061 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6062 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6064 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6066 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6068 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6070 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6072 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.9015820581943275 + 1.4920953068809506*#1 & ),
					"AdjustedRSquared" -> 0.999999823922645,
					"AIC" -> 40221.71646622041,
					"ProbMinInfoLoss" -> 2.2731871735846684988160918007079967974`12.48411629994057*^-1196,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4919,
			"Diffusivity" -> 0.24996018305571305,
			"PecletNumber" -> 5.968550597786503,
			"Randomness" -> 0.1675448643043857
		}
	},
	6074 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6076 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6078 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6080 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6081 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6082 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6083 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 9/8
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 9/8
		}
	},
	6084 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6085 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6086 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6087 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6088 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6089 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6090 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6091 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6092 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6093 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6094 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6096 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6098 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6100 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 69,
			"GrowthRate" -> 107/69
		}
	},
	6102 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6104 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6106 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6108 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6110 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6112 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6113 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6114 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6115 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.5432446444552627 + 0.9914565254185679*#1 & ),
					"AdjustedRSquared" -> 0.9999997251776185,
					"AIC" -> 36498.50218174309,
					"ProbMinInfoLoss" -> 9.2895376603590357850524160363378353995`12.852674878535323*^-464,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9912000000000001,
			"Diffusivity" -> 0.06353525930708694,
			"PecletNumber" -> 15.600786253333798,
			"Randomness" -> 0.06409933344137099
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.44865106508368635 + 0.9914566845445634*#1 & ),
					"AdjustedRSquared" -> 0.9999997252931728,
					"AIC" -> 36494.29981773247,
					"ProbMinInfoLoss" -> 1.031567862857141698204032859377102324009`12.92774479447945*^-462,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9911000000000001,
			"Diffusivity" -> 0.06363350877996381,
			"PecletNumber" -> 15.575127303243512,
			"Randomness" -> 0.06420493268082313
		}
	},
	6116 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.049536453658948 + 1.660649907718497*#1 & ),
					"AdjustedRSquared" -> 0.9999998510341337,
					"AIC" -> 40690.207145860804,
					"ProbMinInfoLoss" -> 1.2037752161754164*^-48,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6609,
			"Diffusivity" -> 0.22411232921651836,
			"PecletNumber" -> 7.411015742892838,
			"Randomness" -> 0.13493427010447248
		}
	},
	6117 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6118 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6119 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6120 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6121 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6122 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6123 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6124 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6125 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	6126 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6128 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6130 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6132 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6134 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6136 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6138 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6140 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6142 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6144 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6145 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.7733153315208621 + 1.354399703095994*#1 & ),
					"AdjustedRSquared" -> 0.9999985255151305,
					"AIC" -> 59536.67405103031,
					"ProbMinInfoLoss" -> 2.775724117576937842384148891953805827641`12.347371356410884*^-1656,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3548,
			"Diffusivity" -> 3.165137397916627,
			"PecletNumber" -> 0.42803829018347306,
			"Randomness" -> 2.3362395910220157
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-2.1260501650086376 + 1.3543993101019907*#1 & ),
					"AdjustedRSquared" -> 0.99999852564304,
					"AIC" -> 59535.80072059,
					"ProbMinInfoLoss" -> 1.42143164195123116657199450018297483931589`12.31999174619056*^-1654,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3545,
			"Diffusivity" -> 3.165050191756523,
			"PecletNumber" -> 0.42795529863249554,
			"Randomness" -> 2.3366926480299175
		}
	},
	6146 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6147 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (3.6142797479865845 + 1.1785426497854241*#1 & ),
					"AdjustedRSquared" -> 0.9999997544514951,
					"AIC" -> 38829.37313219681,
					"ProbMinInfoLoss" -> 2.030980242807373789003293706634014`12.278351900520216*^-1893,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1785,
			"Diffusivity" -> 0.7897925219607378,
			"PecletNumber" -> 1.4921640395812532,
			"Randomness" -> 0.6701676045487804
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (2.433882988294936 + 1.1785430490974311*#1 & ),
					"AdjustedRSquared" -> 0.9999997545338051,
					"AIC" -> 38826.02726277169,
					"ProbMinInfoLoss" -> 5.820871612171484912529783013923946`12.301444680388956*^-1893,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1783000000000001,
			"Diffusivity" -> 0.789863903373734,
			"PecletNumber" -> 1.4917759818712373,
			"Randomness" -> 0.6703419361569497
		}
	},
	6148 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6149 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6150 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6151 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6152 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6153 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6154 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6155 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6156 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6157 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6158 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6160 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6161 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6162 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6163 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6164 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6165 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6166 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6168 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6169 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6170 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6171 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6172 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6173 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6174 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6176 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6177 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6178 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6179 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6180 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6181 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6182 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 12,
			"GrowthRate" -> 7/12
		}
	},
	6183 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6184 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6185 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6186 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6187 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	6188 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6189 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6190 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6192 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6193 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6194 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6195 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/8
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/8
		}
	},
	6196 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6197 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6198 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6200 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6201 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6202 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6203 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6204 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6205 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6206 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6208 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6209 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 4/3
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 4/3
		}
	},
	6210 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6211 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	6212 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6213 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6214 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6215 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6216 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6217 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6218 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6219 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6220 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6221 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6222 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-28.17513284330462 + 1.101632821669975*#1^0.9791540275903232 & ),
					"AdjustedRSquared" -> 0.9999852912814435,
					"AIC" -> 88478.44432099935,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9791540275903232
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.0322569014026728*#1^0.9859617582954824 & ),
					"AdjustedRSquared" -> 0.9999835617905846,
					"AIC" -> 89589.12507412504,
					"ProbMinInfoLoss" -> 6.587776864248323*^-242,
					"Exponent" -> 0.9859617582954824
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (36.129456585656165 + 0.9059021584670213*#1 & ),
					"AdjustedRSquared" -> 0.9998914384570801,
					"AIC" -> 94484.18418945739,
					"ProbMinInfoLoss" -> 7.4157945792440232468838423238525752023937913`12.477053248538121*^-1305,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9112,
			"Diffusivity" -> 2.905494870351208,
			"PecletNumber" -> 0.31361266863632653,
			"Randomness" -> 3.1886466970491747
		}
	},
	6224 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6225 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6226 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6227 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6228 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6229 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6230 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6232 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6233 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6234 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6235 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6236 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6237 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6238 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6240 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6241 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6242 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6243 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6244 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6245 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6246 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 7/4
		}
	},
	6247 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6248 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6249 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6250 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6251 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (7.525757672868164 + 0.7625942663319664*#1^1.0142541759167616 & ),
					"AdjustedRSquared" -> 0.9999809580390324,
					"AIC" -> 90054.07009762335,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0142541759167616
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.7771396674830628*#1^1.0122729297091273 & ),
					"AdjustedRSquared" -> 0.9999808147875295,
					"AIC" -> 90128.01817177789,
					"ProbMinInfoLoss" -> 8.757491483673859*^-17,
					"Exponent" -> 1.0122729297091273
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-33.31526552655153 + 0.8715956735379558*#1 & ),
					"AdjustedRSquared" -> 0.9999023395631718,
					"AIC" -> 92653.75485135967,
					"ProbMinInfoLoss" -> 3.059344488205474891905208366762`12.840699078658579*^-565,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8716,
			"Diffusivity" -> 1.520215834345987,
			"PecletNumber" -> 0.5733396405353004,
			"Randomness" -> 1.7441668590477133
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (6.677265514038047 + 0.7625833948723132*#1^1.0142552003793641 & ),
					"AdjustedRSquared" -> 0.9999809527691403,
					"AIC" -> 90053.80260596849,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0142552003793641
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.7754768358054069*#1^1.0124970630040557 & ),
					"AdjustedRSquared" -> 0.999980840344217,
					"AIC" -> 90111.65363284835,
					"ProbMinInfoLoss" -> 2.7403695100621444*^-13,
					"Exponent" -> 1.0124970630040557
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-34.16646138613288 + 0.8715916131159143*#1 & ),
					"AdjustedRSquared" -> 0.9999023376523855,
					"AIC" -> 92653.85735233828,
					"ProbMinInfoLoss" -> 2.54264367514447920682697259807732`12.828749250195754*^-565,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8714000000000001,
			"Diffusivity" -> 1.5201644189223884,
			"PecletNumber" -> 0.5732274674720492,
			"Randomness" -> 1.7445081695230527
		}
	},
	6252 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6253 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6254 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		}
	},
	6256 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6257 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6258 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6259 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 30,
			"GrowthRate" -> 3/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 30,
			"GrowthRate" -> 3/5
		}
	},
	6260 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6261 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.007792259204435 + 1.682693689082934*#1 & ),
					"AdjustedRSquared" -> 0.9999998944909652,
					"AIC" -> 37504.73782265807,
					"ProbMinInfoLoss" -> 7.28509032903065661712139709041523942`12.387945434656915*^-1602,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6827,
			"Diffusivity" -> 1.8515444062909991,
			"PecletNumber" -> 0.9088088809983083,
			"Randomness" -> 1.1003413598924343
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-4.688268466834562 + 1.682693264366932*#1 & ),
					"AdjustedRSquared" -> 0.9999998944628665,
					"AIC" -> 37507.39559638903,
					"ProbMinInfoLoss" -> 8.2167652648079529233841816892741167`12.387688446178533*^-1603,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6824000000000001,
			"Diffusivity" -> 1.85165399916667,
			"PecletNumber" -> 0.9085930744929441,
			"Randomness" -> 1.1006027099183726
		}
	},
	6262 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6264 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6265 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6266 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6267 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6268 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6269 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 11/8
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 11/8
		}
	},
	6270 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6272 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6273 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6274 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6275 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6276 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6277 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6278 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6279 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-96.9491499281041 + 1.4588753144261524*#1^0.9621945623385545 & ),
					"AdjustedRSquared" -> 0.9999472284032577,
					"AIC" -> 103673.71243530867,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9621945623385545
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.2011040167422549*#1^0.9825220141323164 & ),
					"AdjustedRSquared" -> 0.9999313202295372,
					"AIC" -> 106307.52856952837,
					"ProbMinInfoLoss" -> 1.18602346188512106133170936280945486421984069`12.835034312116441*^-572,
					"Exponent" -> 0.9825220141323164
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (37.065919291939366 + 1.0229439817434394*#1 & ),
					"AdjustedRSquared" -> 0.9996213720026885,
					"AIC" -> 109409.42878376067,
					"ProbMinInfoLoss" -> 3.199042814468170400807837986687227820482716469`12.497032100069033*^-1246,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0033,
			"Diffusivity" -> 2.4793849859080725,
			"PecletNumber" -> 0.40465680227249673,
			"Randomness" -> 2.4712299271484826
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		}
	},
	6280 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6281 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6282 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6283 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6284 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6285 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6286 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6288 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6289 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6290 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6291 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6292 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6293 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (43.2147699173606 + 1.3929072176659862*#1^1.0114513438868353 & ),
					"AdjustedRSquared" -> 0.9999907563545826,
					"AIC" -> 94435.33733607952,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0114513438868353
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-15.323517851786457 + 1.5507407094994075*#1 & ),
					"AdjustedRSquared" -> 0.9999487744653579,
					"AIC" -> 97723.95318291438,
					"ProbMinInfoLoss" -> 7.69382510954520274447794732454042705`12.604877179623381*^-715,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5509000000000002,
			"Diffusivity" -> 3.0155819542746434,
			"PecletNumber" -> 0.5142954240728131,
			"Randomness" -> 1.94440773375114
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.786796279614792 + 1.5243660026556578*#1 & ),
					"AdjustedRSquared" -> 0.9999688704764444,
					"AIC" -> 92399.85559150125,
					"ProbMinInfoLoss" -> 1.35974619144879534825649069292390391005871253014`12.822357201943273*^-589,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.528,
			"Diffusivity" -> 3.1926266441407094,
			"PecletNumber" -> 0.4786027839504105,
			"Randomness" -> 2.0894153430240245
		}
	},
	6294 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6296 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6297 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6298 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6299 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6300 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6301 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6302 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6304 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6305 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6306 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6307 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 14,
			"GrowthRate" -> 9/7
		}
	},
	6308 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6309 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6310 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		}
	},
	6311 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6312 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6313 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6314 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6315 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6316 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6317 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6318 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6320 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6321 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6322 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6323 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	6324 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6325 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6326 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6328 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6329 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6330 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6331 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6332 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6333 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6334 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6336 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6337 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6338 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6339 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6340 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6341 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6342 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6343 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6344 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6345 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6346 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6347 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6348 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6349 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6350 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6352 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6353 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6354 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6355 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 26,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 26,
			"GrowthRate" -> 1
		}
	},
	6356 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6357 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.9232011401152705 + 1.8799959606319598*#1 & ),
					"AdjustedRSquared" -> 0.9999989802098532,
					"AIC" -> 62407.777215486414,
					"ProbMinInfoLoss" -> 3.562144745588091*^-48,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.8797000000000001,
			"Diffusivity" -> 1.886127740599625,
			"PecletNumber" -> 0.9965920968865123,
			"Randomness" -> 1.0034195566311779
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 15/8
		}
	},
	6358 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6360 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6361 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6362 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6363 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6364 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6365 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6366 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6368 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6369 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6370 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6371 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 108,
			"GrowthRate" -> 11/9
		}
	},
	6372 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6373 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6374 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 14,
			"GrowthRate" -> 11/7
		}
	},
	6375 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-67.24832522113502 + 1.2178299542087023*#1^0.860552210607975 & ),
					"AdjustedRSquared" -> 0.9994006761805525,
					"AIC" -> 106054.9779380878,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.860552210607975
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.8495481564615908*#1^0.8979182537291952 & ),
					"AdjustedRSquared" -> 0.9993434264645947,
					"AIC" -> 106966.30465441856,
					"ProbMinInfoLoss" -> 1.282088318665802*^-198,
					"Exponent" -> 0.8979182537291952
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (109.56988946894491 + 0.327033558750335*#1 & ),
					"AdjustedRSquared" -> 0.9948584660628753,
					"AIC" -> 112735.1662871835,
					"ProbMinInfoLoss" -> 2.60334039183418621621676207923924`12.389931571730495*^-1451,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.3211,
			"Diffusivity" -> 3.1279742897274323,
			"PecletNumber" -> 0.10265429644179724,
			"Randomness" -> 9.741433477818227
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-67.24832522113502 + 1.2178299542087023*#1^0.860552210607975 & ),
					"AdjustedRSquared" -> 0.9994006761805525,
					"AIC" -> 106054.9779380878,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.860552210607975
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.8495481564615908*#1^0.8979182537291952 & ),
					"AdjustedRSquared" -> 0.9993434264645947,
					"AIC" -> 106966.30465441856,
					"ProbMinInfoLoss" -> 1.282088318665802*^-198,
					"Exponent" -> 0.8979182537291952
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (109.56988946894491 + 0.327033558750335*#1 & ),
					"AdjustedRSquared" -> 0.9948584660628753,
					"AIC" -> 112735.1662871835,
					"ProbMinInfoLoss" -> 2.60334039183418621621676207923924`12.389931571730495*^-1451,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.3211,
			"Diffusivity" -> 3.1279742897274323,
			"PecletNumber" -> 0.10265429644179724,
			"Randomness" -> 9.741433477818227
		}
	},
	6376 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6377 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6378 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6379 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6380 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6381 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6382 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 5,
			"GrowthRate" -> 6/5
		}
	},
	6384 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6385 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6386 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6387 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	6388 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6389 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 9/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 9/4
		}
	},
	6390 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6392 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6393 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6394 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6395 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6396 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6397 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6398 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6400 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6401 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6402 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6403 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6404 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6405 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6406 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6407 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6408 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6409 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6410 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6411 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6412 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6413 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6414 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6416 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6418 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6420 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6422 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6424 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6426 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6428 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6430 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6432 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6433 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6434 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6435 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6436 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6437 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6438 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6439 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6440 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6441 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6442 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6443 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6444 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6445 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6446 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6448 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6450 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6452 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6454 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6456 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6458 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6460 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6462 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6464 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6465 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6466 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6467 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6468 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6469 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6470 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6471 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6472 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6473 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6474 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6475 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6476 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6477 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6478 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6480 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6482 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6484 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6486 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6488 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 5,
			"GrowthRate" -> 9/5
		}
	},
	6490 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6492 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6494 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6496 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6497 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6498 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6499 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6500 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 9/5
		}
	},
	6501 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6502 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6503 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6504 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6505 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6506 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6507 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6508 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6509 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6510 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6512 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6514 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6516 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6518 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6520 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 5,
			"GrowthRate" -> 9/5
		}
	},
	6522 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6524 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6526 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6528 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6529 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6530 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6531 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6532 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6533 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6534 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6535 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 12,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 12,
			"GrowthRate" -> 0
		}
	},
	6536 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6537 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6538 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6539 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6540 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6541 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6542 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6544 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6546 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6548 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (80.53891237068015 + 1.04286936690526*#1^1.0195869475398427 & ),
					"AdjustedRSquared" -> 0.9999152269569264,
					"AIC" -> 112362.76251700564,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0195869475398427
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (0.28135913592472217 + 1.252981170055812*#1 & ),
					"AdjustedRSquared" -> 0.9996196937803704,
					"AIC" -> 113510.4898327349,
					"ProbMinInfoLoss" -> 5.945385568005419*^-250,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2756,
			"Diffusivity" -> 1.2572885014046513,
			"PecletNumber" -> 1.0145642774708359,
			"Randomness" -> 0.9856447957076288
		}
	},
	6550 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6552 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6554 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6556 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6558 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6560 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6561 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6562 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6563 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6564 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6565 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (14.646856705682005 + 1.2872961990389589*#1 & ),
					"AdjustedRSquared" -> 0.9999816468895254,
					"AIC" -> 83735.46095374916,
					"ProbMinInfoLoss" -> 2.1309634654111943*^-18,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2863,
			"Diffusivity" -> 0.8456932510614534,
			"PecletNumber" -> 1.5210006682511994,
			"Randomness" -> 0.6574619070679106
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-5.475533714554248 + 1.4598067373951382*#1^0.9845012152281417 & ),
					"AdjustedRSquared" -> 0.9999927718614018,
					"AIC" -> 88032.73596842847,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9845012152281417
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.4465609887087412*#1^0.9854554582209538 & ),
					"AdjustedRSquared" -> 0.9999927389044116,
					"AIC" -> 88077.2279906408,
					"ProbMinInfoLoss" -> 2.1811228735024633*^-10,
					"Exponent" -> 0.9854554582209538
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (60.778480528075605 + 1.2622447994144446*#1 & ),
					"AdjustedRSquared" -> 0.9999437478851252,
					"AIC" -> 94543.23909145007,
					"ProbMinInfoLoss" -> 1.82898283194021434720489755490286736594326529655097`12.332753438290924*^-1414,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2690000000000001,
			"Diffusivity" -> 0.9220161664095996,
			"PecletNumber" -> 1.3763316156825989,
			"Randomness" -> 0.7265690830650903
		}
	},
	6566 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6567 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6568 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6569 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-33.928634569353854 + 1.1987396467642404*#1^0.9897118147590627 & ),
					"AdjustedRSquared" -> 0.9999921495175574,
					"AIC" -> 85762.42135885119,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9897118147590627
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (3.796487428754918 + 1.0884586766465838*#1 & ),
					"AdjustedRSquared" -> 0.9999566998555758,
					"AIC" -> 88963.65119586432,
					"ProbMinInfoLoss" -> 7.27399905965350084965100940655018282`12.750302909779201*^-696,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0849,
			"Diffusivity" -> 0.8934699631195366,
			"PecletNumber" -> 1.2142545858084455,
			"Randomness" -> 0.8235505236607398
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-32.87662907691325 + 1.1988666421997132*#1^0.9897003238134378 & ),
					"AdjustedRSquared" -> 0.9999921546100562,
					"AIC" -> 85758.9098661485,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9897003238134378
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (4.890995199520841 + 1.088456615298565*#1 & ),
					"AdjustedRSquared" -> 0.9999566842589817,
					"AIC" -> 88967.21479955045,
					"ProbMinInfoLoss" -> 2.11560984955324387488079316607236197`12.68312867984764*^-697,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0851,
			"Diffusivity" -> 0.8918356328531433,
			"PecletNumber" -> 1.216704020368158,
			"Randomness" -> 0.8218925747425521
		}
	},
	6570 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6571 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6572 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6573 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		}
	},
	6574 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6576 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6578 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6580 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 5,
			"GrowthRate" -> 4/5
		}
	},
	6582 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6584 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6586 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6588 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6590 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6592 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6593 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6594 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6595 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6596 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6597 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		}
	},
	6598 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6599 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6600 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6601 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6602 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6603 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6604 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6605 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6606 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6608 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6610 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6612 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6614 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6616 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6618 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6620 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6622 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6624 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6625 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6626 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6627 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6628 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-4.47314929491724 + 1.640287421116873*#1 & ),
					"AdjustedRSquared" -> 0.9999943856401063,
					"AIC" -> 76737.16740292367,
					"ProbMinInfoLoss" -> 1.4917821329996243*^-24,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6405,
			"Diffusivity" -> 0.23026477482715266,
			"PecletNumber" -> 7.124407114511695,
			"Randomness" -> 0.1403625570418486
		}
	},
	6629 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (11.358512751286037 + 0.9453540020495375*#1 & ),
					"AdjustedRSquared" -> 0.9999166892449479,
					"AIC" -> 92689.09904024652,
					"ProbMinInfoLoss" -> 2.947106789009064*^-255,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9519000000000001,
			"Diffusivity" -> 1.3932648115781772,
			"PecletNumber" -> 0.6832154175499237,
			"Randomness" -> 1.463667204095154
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (38.395336573665276 + 0.9164582668585811*#1 & ),
					"AdjustedRSquared" -> 0.9999186192521168,
					"AIC" -> 91833.83189907984,
					"ProbMinInfoLoss" -> 8.353350964064583*^-21,
					"Exponent" -> 1
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.0081004388593373*#1^0.9899687634481418 & ),
					"AdjustedRSquared" -> 0.999978112324868,
					"AIC" -> 92689.92876334584,
					"ProbMinInfoLoss" -> 1.0538739409163652*^-206,
					"Exponent" -> 0.9899687634481418
				}
			},
			"GrowthRate" -> 0.921,
			"Diffusivity" -> 1.4872558270029843,
			"PecletNumber" -> 0.6192613155572138,
			"Randomness" -> 1.614827173727453
		}
	},
	6630 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6632 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6633 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6634 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6635 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6636 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6637 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6638 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6640 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6642 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6644 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6646 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6648 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6650 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6652 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6654 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6656 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6657 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		}
	},
	6658 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6659 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 11/10
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 11/10
		}
	},
	6660 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6661 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6662 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-11.007989858985532 + 1.313729445027295*#1 & ),
					"AdjustedRSquared" -> 0.9999909801717658,
					"AIC" -> 77038.1488181465,
					"ProbMinInfoLoss" -> 0.004453415920351496,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3112000000000001,
			"Diffusivity" -> 0.785101894866422,
			"PecletNumber" -> 1.670101688167609,
			"Randomness" -> 0.59876593568214
		}
	},
	6663 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6664 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6665 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6666 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6667 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 5/6
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 5/6
		}
	},
	6668 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6669 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6670 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6672 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6673 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6674 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6675 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6676 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6677 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6678 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6680 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6681 -> {
		{{1}, 0} -> {
			"BoundaryWordCoding" -> {
				"A" -> {3, 1},
				"B" -> {3, -2, 3, 1},
				"C" -> {3, -3}
			},
			"BoundaryWordMorphism" -> {
				"A" -> "ABCB",
				"B" -> "BB",
				"C" -> "CC"
			},
			"GrowthRate" -> Missing["Nonexistent"],
			"GrowthRateLimInf" -> 15/16,
			"GrowthRateLimSup" -> 15/14
		},
		{{0}, 1} -> {
			"BoundaryWordCoding" -> {
				"A" -> {0, 3, 1},
				"B" -> {3, -2, 3, 1},
				"C" -> {3, -3}
			},
			"BoundaryWordMorphism" -> {
				"A" -> "ABCB",
				"B" -> "BB",
				"C" -> "CC"
			},
			"GrowthRate" -> Missing["Nonexistent"],
			"GrowthRateLimInf" -> 15/16,
			"GrowthRateLimSup" -> 15/14
		}
	},
	6682 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6683 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6684 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6685 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6686 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6688 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6689 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6690 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6691 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6692 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6693 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6694 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-6.0205807380599445 + 1.1168173144161704*#1 & ),
					"AdjustedRSquared" -> 0.9999763248950284,
					"AIC" -> 83440.54236554482,
					"ProbMinInfoLoss" -> 1.631332558938163*^-58,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1148,
			"Diffusivity" -> 2.078035249013999,
			"PecletNumber" -> 0.5364682820125204,
			"Randomness" -> 1.864043101017222
		}
	},
	6695 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6696 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6697 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-28.124710391425758 + 1.4144005198271536*#1^0.9805629064926831 & ),
					"AdjustedRSquared" -> 0.9999861387395348,
					"AIC" -> 93154.84868710124,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9805629064926831
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.345468406499141*#1^0.9857924527694736 & ),
					"AdjustedRSquared" -> 0.999985120895832,
					"AIC" -> 93862.44785251528,
					"ProbMinInfoLoss" -> 2.2222531509847078*^-154,
					"Exponent" -> 0.9857924527694736
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (49.769906390645204 + 1.1785893597858914*#1 & ),
					"AdjustedRSquared" -> 0.999901290757991,
					"AIC" -> 98795.54392358607,
					"ProbMinInfoLoss" -> 1.3759173541180143855846522404336539954642285975`12.35331844568765*^-1225,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1778,
			"Diffusivity" -> 5.478079614322705,
			"PecletNumber" -> 0.2150023517220496,
			"Randomness" -> 4.6511119157095475
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-29.326035876223266 + 1.41437981401283*#1^0.9805650425951523 & ),
					"AdjustedRSquared" -> 0.9999861344677944,
					"AIC" -> 93154.97172544505,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9805650425951523
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.3425701577502025*#1^0.9860187845573342 & ),
					"AdjustedRSquared" -> 0.9999850271056393,
					"AIC" -> 93922.32658200596,
					"ProbMinInfoLoss" -> 2.349687286086673*^-167,
					"Exponent" -> 0.9860187845573342
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (48.56027290727886 + 1.1785957458439589*#1 & ),
					"AdjustedRSquared" -> 0.9999013000334395,
					"AIC" -> 98794.71248044039,
					"ProbMinInfoLoss" -> 2.217457834276633435552154797280916319323189684`12.50436062486148*^-1225,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1775,
			"Diffusivity" -> 5.477886176295165,
			"PecletNumber" -> 0.21495517834880853,
			"Randomness" -> 4.6521326337963185
		}
	},
	6698 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6699 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	6700 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6701 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (14.890651785184458 + 0.773232066436319*#1 & ),
					"AdjustedRSquared" -> 0.9999610720821401,
					"AIC" -> 81060.39058100207,
					"ProbMinInfoLoss" -> 6.648829989720629*^-289,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7772,
			"Diffusivity" -> 5.6512854526100735,
			"PecletNumber" -> 0.1375262330167814,
			"Randomness" -> 7.271340005931644
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (14.116822682276837 + 0.7732314123223119*#1 & ),
					"AdjustedRSquared" -> 0.9999610804805567,
					"AIC" -> 81058.21591764878,
					"ProbMinInfoLoss" -> 1.1489108442232526*^-287,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7769,
			"Diffusivity" -> 5.6508515824577055,
			"PecletNumber" -> 0.1374837028832574,
			"Randomness" -> 7.2735893711645065
		}
	},
	6702 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6704 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6705 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6706 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6707 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 18,
			"GrowthRate" -> 5/6
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 18,
			"GrowthRate" -> 5/6
		}
	},
	6708 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6709 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6710 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6712 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6713 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/4
		}
	},
	6714 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6715 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6716 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6717 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6718 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6720 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6721 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		}
	},
	6722 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6723 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-72.1659726629349 + 0.8294632736684096*#1^0.942118064250852 & ),
					"AdjustedRSquared" -> 0.9998927254752688,
					"AIC" -> 95753.78078718792,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.942118064250852
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.6144932366675772*#1^0.9734434644810313 & ),
					"AdjustedRSquared" -> 0.9998541390536699,
					"AIC" -> 98825.40648703299,
					"ProbMinInfoLoss" -> 1.0114724136030224479701147105845080609011426524`12.768251473244145*^-667,
					"Exponent" -> 0.9734434644810313
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (26.476102130217193 + 0.48148679089486707*#1 & ),
					"AdjustedRSquared" -> 0.9991682605812473,
					"AIC" -> 102212.38810290444,
					"ProbMinInfoLoss" -> 3.398137924679572133435110351290229534163717`12.313603953448611*^-1403,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.47540000000000004,
			"Diffusivity" -> 4.081783673466367,
			"PecletNumber" -> 0.11646869065853184,
			"Randomness" -> 8.585998471742464
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-72.61726313675085 + 0.829219138938211*#1^0.9421508159569574 & ),
					"AdjustedRSquared" -> 0.9998926743239599,
					"AIC" -> 95755.67160769318,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9421508159569574
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.6131294667265434*#1^0.9736776765493698 & ),
					"AdjustedRSquared" -> 0.9998535813048195,
					"AIC" -> 98860.69565381078,
					"ProbMinInfoLoss" -> 5.65711877459976929535531164981851155851`12.763554798039406*^-675,
					"Exponent" -> 0.9736776765493698
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (25.966950855080217 + 0.48149356047293684*#1 & ),
					"AdjustedRSquared" -> 0.9991686448889953,
					"AIC" -> 102208.04385134787,
					"ProbMinInfoLoss" -> 7.6766138908364406603889408930451726143703527`12.365068668963648*^-1402,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.4752,
			"Diffusivity" -> 4.081573730487672,
			"PecletNumber" -> 0.1164256807246803,
			"Randomness" -> 8.589170308265302
		}
	},
	6724 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6725 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6726 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-1.6680281427956656 + 1.7426652191066485*#1 & ),
					"AdjustedRSquared" -> 0.9999999429288383,
					"AIC" -> 32060.15644796003,
					"ProbMinInfoLoss" -> 9.14878178425695723020641169071929041439`12.776770676862304*^-655,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7428000000000001,
			"Diffusivity" -> 0.1910311855350368,
			"PecletNumber" -> 9.123117752312515,
			"Randomness" -> 0.10961165109882762
		}
	},
	6727 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6728 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6729 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6730 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6731 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (17.09006438644225 + 0.6982627208506267*#1 & ),
					"AdjustedRSquared" -> 0.999976767037157,
					"AIC" -> 73859.16178725254,
					"ProbMinInfoLoss" -> 1.2170952394425097*^-21,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7012,
			"Diffusivity" -> 1.4536003510333029,
			"PecletNumber" -> 0.4823884360660389,
			"Randomness" -> 2.0730181845882814
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (16.387822922300842 + 0.6982629491206278*#1 & ),
					"AdjustedRSquared" -> 0.9999767643956089,
					"AIC" -> 73860.30527006285,
					"ProbMinInfoLoss" -> 2.6274676761492767*^-21,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7011000000000001,
			"Diffusivity" -> 1.453640583102119,
			"PecletNumber" -> 0.4823062923187164,
			"Randomness" -> 2.0733712496107817
		}
	},
	6732 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6733 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6734 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.07852079210395461 + 1.6444267731642623*#1 & ),
					"AdjustedRSquared" -> 0.9999999807097575,
					"AIC" -> 20052.684355363115,
					"ProbMinInfoLoss" -> 1.1055026394288719751407462149585079`12.98069702967299*^-409,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6444,
			"Diffusivity" -> 0.22915294129933098,
			"PecletNumber" -> 7.175993424636008,
			"Randomness" -> 0.13935352791250968
		}
	},
	6736 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6737 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6738 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6739 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6740 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6741 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6742 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6744 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6745 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (9.846426282642645 + 1.6371545992835448*#1 & ),
					"AdjustedRSquared" -> 0.9999976116888211,
					"AIC" -> 68151.48931226006,
					"ProbMinInfoLoss" -> 5.4351355819981366*^-68,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6392,
			"Diffusivity" -> 2.1182061394777207,
			"PecletNumber" -> 0.7738623590261958,
			"Randomness" -> 1.2922194603939243
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (8.207855265550318 + 1.6371544934975422*#1 & ),
					"AdjustedRSquared" -> 0.9999976118420947,
					"AIC" -> 68150.84623205513,
					"ProbMinInfoLoss" -> 2.0514932166880494*^-68,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6389,
			"Diffusivity" -> 2.118289624521564,
			"PecletNumber" -> 0.7736902362301668,
			"Randomness" -> 1.292506940338986
		}
	},
	6746 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6747 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6748 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6749 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6750 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6752 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6753 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-75.17908481492813 + 1.1516319658351617*#1^0.9843434228799106 & ),
					"AdjustedRSquared" -> 0.9999527700466402,
					"AIC" -> 101819.59569451149,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9843434228799106
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-22.44812337231823 + 0.994302514423022*#1 & ),
					"AdjustedRSquared" -> 0.9997844526979538,
					"AIC" -> 103206.0895476845,
					"ProbMinInfoLoss" -> 8.446663384879199*^-302,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9906,
			"Diffusivity" -> 6.754862603683853,
			"PecletNumber" -> 0.14664991105218977,
			"Randomness" -> 6.818960835537909
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-76.11994536022098 + 1.1514830112565448*#1^0.9843571450650778 & ),
					"AdjustedRSquared" -> 0.9999527425179896,
					"AIC" -> 101822.42484418442,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9843571450650778
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-23.4359629162791 + 0.9943019823850181*#1 & ),
					"AdjustedRSquared" -> 0.9997844483762999,
					"AIC" -> 103206.27938394656,
					"ProbMinInfoLoss" -> 3.160856736949419*^-301,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9903000000000001,
			"Diffusivity" -> 6.754556811952449,
			"PecletNumber" -> 0.14661213571371937,
			"Randomness" -> 6.820717774363778
		}
	},
	6754 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6755 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6756 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6757 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6758 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 7/4
		}
	},
	6760 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6761 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6762 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6763 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-95.77372152370718 + 1.191215660762645*#1^0.9766478891930569 & ),
					"AdjustedRSquared" -> 0.9999791231068244,
					"AIC" -> 92892.84950602289,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9766478891930569
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-19.49612583256851 + 0.956781507015813*#1 & ),
					"AdjustedRSquared" -> 0.9998549336236211,
					"AIC" -> 98476.16597954235,
					"ProbMinInfoLoss" -> 3.964901617522021755068777954250781573593`12.508727520628979*^-1213,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9512,
			"Diffusivity" -> 1.4271037425806994,
			"PecletNumber" -> 0.666524774351653,
			"Randomness" -> 1.5003193256735696
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-96.65750063303204 + 1.190975505413096*#1^0.9766694614429422 & ),
					"AdjustedRSquared" -> 0.9999790911032621,
					"AIC" -> 92905.18423781043,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9766694614429422
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-20.451974857483297 + 0.9567824567258251*#1 & ),
					"AdjustedRSquared" -> 0.9998549456988008,
					"AIC" -> 98475.35328633453,
					"ProbMinInfoLoss" -> 2.838961342325558553554070953599128709252364`12.47304296952504*^-1210,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9510000000000001,
			"Diffusivity" -> 1.4270841767113298,
			"PecletNumber" -> 0.6663937667584189,
			"Randomness" -> 1.500614276247455
		}
	},
	6764 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6765 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (25.870139148739817 + 0.5689439648863237*#1^1.0142591955318354 & ),
					"AdjustedRSquared" -> 0.9999749530634142,
					"AIC" -> 87030.85261107498,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0142591955318354
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-4.612080888086058 + 0.6502965865189657*#1 & ),
					"AdjustedRSquared" -> 0.9998777748797245,
					"AIC" -> 89039.73924072795,
					"ProbMinInfoLoss" -> 5.96775501271700390193379714248391382914743631`12.760135154682132*^-437,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6542,
			"Diffusivity" -> 6.616133627765657,
			"PecletNumber" -> 0.09887950226013359,
			"Randomness" -> 10.113319516609076
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (25.200794672072917 + 0.5690169603214151*#1^1.0142450160154557 & ),
					"AdjustedRSquared" -> 0.99997494766393,
					"AIC" -> 87029.96561995753,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0142450160154557
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-5.251400780070108 + 0.6502936307929351*#1 & ),
					"AdjustedRSquared" -> 0.9998778269495614,
					"AIC" -> 89035.38674979482,
					"ProbMinInfoLoss" -> 3.375473553923159795589096182043131481936837572`12.953414179342852*^-436,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6539,
			"Diffusivity" -> 6.615625935468122,
			"PecletNumber" -> 0.0988417432270874,
			"Randomness" -> 10.117182956825388
		}
	},
	6766 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-1.9581314731284516 + 1.6447435519394327*#1 & ),
					"AdjustedRSquared" -> 0.9999996490951728,
					"AIC" -> 49065.6964201751,
					"ProbMinInfoLoss" -> 5.596291354847513893373682517523864948`12.33469420636641*^-1388,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6451,
			"Diffusivity" -> 0.22895016046913752,
			"PecletNumber" -> 7.185406625743594,
			"Randomness" -> 0.13917096861536535
		}
	},
	6768 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6769 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6770 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6771 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (28.09640354035481 + 1.0501054287490543*#1 & ),
					"AdjustedRSquared" -> 0.9999506832692667,
					"AIC" -> 89547.34414811108,
					"ProbMinInfoLoss" -> 1.244426776018615677160542328965864`12.960305882050182*^-391,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0517,
			"Diffusivity" -> 1.1714611349112507,
			"PecletNumber" -> 0.8977677266943015,
			"Randomness" -> 1.113873856528716
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (27.033028682876033 + 1.0501077834850767*#1 & ),
					"AdjustedRSquared" -> 0.9999506771125032,
					"AIC" -> 89548.63739202176,
					"ProbMinInfoLoss" -> 7.1706012274892376548030070381674`13.00003691531297*^-392,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0515,
			"Diffusivity" -> 1.1714817811046958,
			"PecletNumber" -> 0.897581180484468,
			"Randomness" -> 1.1141053553064153
		}
	},
	6772 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6773 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.7929926792776679 + 1.7011860428598589*#1 & ),
					"AdjustedRSquared" -> 0.9999999182230644,
					"AIC" -> 35175.31981801319,
					"ProbMinInfoLoss" -> 8.636314596503159*^-189,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7011,
			"Diffusivity" -> 1.8076711651961355,
			"PecletNumber" -> 0.9410450488739349,
			"Randomness" -> 1.0626483835142764
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.9084413441008657 + 1.701186129655855*#1 & ),
					"AdjustedRSquared" -> 0.999999918234236,
					"AIC" -> 35173.95466100201,
					"ProbMinInfoLoss" -> 2.704364070683618*^-188,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7008,
			"Diffusivity" -> 1.8077918013845793,
			"PecletNumber" -> 0.9408163034578237,
			"Randomness" -> 1.0629067505788918
		}
	},
	6774 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6776 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6777 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (19.175587158742715 + 1.505168765691682*#1 & ),
					"AdjustedRSquared" -> 0.9999962608838747,
					"AIC" -> 70953.03626871559,
					"ProbMinInfoLoss" -> 1.9170856450819774*^-8,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5082,
			"Diffusivity" -> 2.540214973687807,
			"PecletNumber" -> 0.5937292770975368,
			"Randomness" -> 1.6842693102292847
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (17.665376177628644 + 1.50516918784569*#1 & ),
					"AdjustedRSquared" -> 0.9999962597935521,
					"AIC" -> 70955.95745463789,
					"ProbMinInfoLoss" -> 1.1457666957898393*^-8,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5079,
			"Diffusivity" -> 2.5402198351461474,
			"PecletNumber" -> 0.5936100408070569,
			"Randomness" -> 1.6846076232814824
		}
	},
	6778 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6779 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6780 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6781 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (5.537609600993457 + 1.426527905289276*#1 & ),
					"AdjustedRSquared" -> 0.9999990938680408,
					"AIC" -> 55705.5805742637,
					"ProbMinInfoLoss" -> 0.0021692030393836124,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4271,
			"Diffusivity" -> 2.53697474168301,
			"PecletNumber" -> 0.5625203816784051,
			"Randomness" -> 1.7777133639429683
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (4.109303330369295 + 1.4265281665172778*#1 & ),
					"AdjustedRSquared" -> 0.99999909374719,
					"AIC" -> 55706.917849184625,
					"ProbMinInfoLoss" -> 0.0024468381070792996,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4268,
			"Diffusivity" -> 2.5369309285399435,
			"PecletNumber" -> 0.562411843361125,
			"Randomness" -> 1.7780564399635153
		}
	},
	6782 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6784 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6785 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6786 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6787 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6788 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6789 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6790 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-31.632628205816932 + 0.8052065988733675*#1^0.9791302423608209 & ),
					"AdjustedRSquared" -> 0.9999736561987098,
					"AIC" -> 87983.38483346142,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9791302423608209
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.7285685325377621*#1^0.9895975153321231 & ),
					"AdjustedRSquared" -> 0.9999695164745498,
					"AIC" -> 89441.91894705048,
					"ProbMinInfoLoss" -> 1.9201776054132223722576595147442196433247605404621`12.975721882364443*^-317,
					"Exponent" -> 0.9895975153321231
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (15.413766876691666 + 0.6619949471299488*#1 & ),
					"AdjustedRSquared" -> 0.9998444308530092,
					"AIC" -> 91808.91739640459,
					"ProbMinInfoLoss" -> 1.977692589806149485313535992871920808`12.67292786282351*^-831,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6607000000000001,
			"Diffusivity" -> 3.1461932350466495,
			"PecletNumber" -> 0.20999981585371497,
			"Randomness" -> 4.761908937561146
		}
	},
	6791 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 22,
			"GrowthRate" -> 27/22
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6792 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6793 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6794 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6795 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6796 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6797 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6798 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6800 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6801 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6802 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6803 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6804 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6805 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6806 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6808 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6809 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6810 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6811 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6812 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6813 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 4/3
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6814 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6816 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6817 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6818 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6819 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 14,
			"GrowthRate" -> 9/7
		}
	},
	6820 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6821 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6822 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (32.33791022198007 + 0.6015424103478392*#1^1.0103841001189633 & ),
					"AdjustedRSquared" -> 0.9997888282265711,
					"AIC" -> 108804.81134458532,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0103841001189633
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (9.61751131113386 + 0.6630406736704063*#1 & ),
					"AdjustedRSquared" -> 0.9991405470211779,
					"AIC" -> 108939.58544313246,
					"ProbMinInfoLoss" -> 5.4222101888743066*^-30,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6774,
			"Diffusivity" -> 2.2603709060644013,
			"PecletNumber" -> 0.2996853295990441,
			"Randomness" -> 3.3368333422858005
		}
	},
	6823 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6824 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6825 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (24.813788902390492 + 1.7770504203535318*#1^1.0113483845492683 & ),
					"AdjustedRSquared" -> 0.9999962516778697,
					"AIC" -> 90215.93641214326,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0113483845492683
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-49.133080348026716 + 1.9765043256370405*#1 & ),
					"AdjustedRSquared" -> 0.999970991194542,
					"AIC" -> 96889.28588885955,
					"ProbMinInfoLoss" -> 7.953773604024081181622972860681472`12.431275896835894*^-1450,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.9764000000000002,
			"Diffusivity" -> 2.3158108569408653,
			"PecletNumber" -> 0.8534375741768395,
			"Randomness" -> 1.1717318644711927
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (32.04785324681973 + 1.7763071860292168*#1^1.0118109716276988 & ),
					"AdjustedRSquared" -> 0.9999970280965469,
					"AIC" -> 87979.47884700699,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0118109716276988
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-45.17971899188823 + 1.98425955784259*#1 & ),
					"AdjustedRSquared" -> 0.9999728534103007,
					"AIC" -> 96304.10802395767,
					"ProbMinInfoLoss" -> 2.13669375043596094881901500148323877860295`12.198630830110629*^-1808,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.9846000000000001,
			"Diffusivity" -> 2.2489156697226034,
			"PecletNumber" -> 0.8824697282867856,
			"Randomness" -> 1.1331833466303554
		}
	},
	6826 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6827 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6828 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6829 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-18.700019094454934 + 1.3427378007757353*#1^1.010271202491088 & ),
					"AdjustedRSquared" -> 0.9999931206436767,
					"AIC" -> 90416.08059020629,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.010271202491088
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.3062082226932386*#1^1.0131629029845308 & ),
					"AdjustedRSquared" -> 0.9999928091177539,
					"AIC" -> 90857.96862929173,
					"ProbMinInfoLoss" -> 1.1097662246337762*^-96,
					"Exponent" -> 1.0131629029845308
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-68.8157470746781 + 1.4784465447604618*#1 & ),
					"AdjustedRSquared" -> 0.9999611749476914,
					"AIC" -> 93997.2892507455,
					"ProbMinInfoLoss" -> 2.24088769497245224674308891916674742177990498378126`12.701590139766092*^-778,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4746000000000001,
			"Diffusivity" -> 3.121356584548233,
			"PecletNumber" -> 0.47242279440284624,
			"Randomness" -> 2.116747988978864
		}
	},
	6830 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6832 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6833 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6834 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6835 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	6836 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6837 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 9/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 9/4
		}
	},
	6838 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6840 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6841 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 9/4
		}
	},
	6842 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6843 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6844 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6845 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 9/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 9/5
		}
	},
	6846 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6848 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6849 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6850 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6851 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.3499060306034525 + 1.1315667845276676*#1 & ),
					"AdjustedRSquared" -> 0.9999802405795271,
					"AIC" -> 81894.97113544651,
					"ProbMinInfoLoss" -> 1.2271151996596996*^-74,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1317000000000002,
			"Diffusivity" -> 1.21919721478049,
			"PecletNumber" -> 0.9282337478139308,
			"Randomness" -> 1.0773148491477333
		}
	},
	6852 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6853 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6854 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6855 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.3499060306034525 + 1.1315667845276676*#1 & ),
					"AdjustedRSquared" -> 0.9999802405795271,
					"AIC" -> 81894.97113544651,
					"ProbMinInfoLoss" -> 1.2271151996596996*^-74,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1317000000000002,
			"Diffusivity" -> 1.21919721478049,
			"PecletNumber" -> 0.9282337478139308,
			"Randomness" -> 1.0773148491477333
		}
	},
	6856 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6857 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6858 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6859 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6860 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6861 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6862 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 51,
			"GrowthRate" -> 56/51
		}
	},
	6864 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6865 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6866 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6867 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-4.477996279629298 + 1.1315661226436606*#1 & ),
					"AdjustedRSquared" -> 0.9999802404267311,
					"AIC" -> 81895.03676633014,
					"ProbMinInfoLoss" -> 1.0360687894241164*^-74,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1316000000000002,
			"Diffusivity" -> 1.2197236527013373,
			"PecletNumber" -> 0.9277511323928428,
			"Randomness" -> 1.0778752674985306
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.3499060306034525 + 1.1315667845276676*#1 & ),
					"AdjustedRSquared" -> 0.9999802405795271,
					"AIC" -> 81894.97113544651,
					"ProbMinInfoLoss" -> 1.2271151996596996*^-74,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1317000000000002,
			"Diffusivity" -> 1.21919721478049,
			"PecletNumber" -> 0.9282337478139308,
			"Randomness" -> 1.0773148491477333
		}
	},
	6868 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6869 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6870 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6872 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6873 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6874 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6875 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6876 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6877 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6878 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6880 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6881 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6882 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6883 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 116,
			"GrowthRate" -> 39/29
		}
	},
	6884 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6885 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6886 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 7/4
		}
	},
	6888 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6889 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6890 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6891 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6892 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6893 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6894 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (51.82122454245052 + 0.9170617089206167*#1 & ),
					"AdjustedRSquared" -> 0.9997420882216238,
					"AIC" -> 103383.55049740968,
					"ProbMinInfoLoss" -> 4.2414406872013463*^-51,
					"Exponent" -> 1
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.0185231937421504*#1^0.989129184846414 & ),
					"AdjustedRSquared" -> 0.9999261502095458,
					"AIC" -> 104908.24100820733,
					"ProbMinInfoLoss" -> 3.508937827565721285571946191050064250917286`12.866661754002376*^-382,
					"Exponent" -> 0.989129184846414
				}
			},
			"GrowthRate" -> 0.9232,
			"Diffusivity" -> 2.8244660633296776,
			"PecletNumber" -> 0.3268582377342029,
			"Randomness" -> 3.05943031123232
		}
	},
	6896 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6897 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6898 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6899 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	6900 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6901 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	6902 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6904 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6905 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6906 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6907 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6908 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	6909 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	6910 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6912 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6913 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6914 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6915 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6916 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6917 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6918 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6919 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6920 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6921 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6922 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6923 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6924 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6925 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6926 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6928 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6930 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6932 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6934 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6936 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6938 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6940 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6942 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6944 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6945 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6946 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6947 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6948 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6949 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6950 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6951 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6952 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6953 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6954 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6955 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6956 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6957 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6958 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6960 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6962 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6964 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6966 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6968 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	6970 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6972 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6974 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6976 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6977 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6978 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6979 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	6980 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6981 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6982 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6983 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6984 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	6985 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6986 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6987 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6988 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	6989 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6990 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6992 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6994 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	6996 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	6998 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7000 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 9/5
		}
	},
	7002 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7004 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7006 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7008 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7009 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7010 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7011 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	7012 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	7013 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7014 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7016 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7017 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7018 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7019 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7020 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7021 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	7022 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7024 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7026 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7028 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7030 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7032 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 9/5
		}
	},
	7034 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7036 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7038 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7040 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7041 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7042 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7043 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7044 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7045 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 11/6
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 11/6
		}
	},
	7046 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7047 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7048 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7049 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7050 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7051 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7052 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7053 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7054 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7056 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7058 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7060 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 17/10
		}
	},
	7062 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7064 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7066 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7068 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7070 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7072 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7073 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7074 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7075 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7076 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (17.90219074615881 + 1.0180587974591786*#1^0.9853246888741052 & ),
					"AdjustedRSquared" -> 0.9999780217057755,
					"AIC" -> 92164.76187466976,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9853246888741052
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (1.0621046807530947*#1^0.9808904248891368 & ),
					"AdjustedRSquared" -> 0.9999773054034204,
					"AIC" -> 92484.47732327764,
					"ProbMinInfoLoss" -> 3.755540460094813*^-70,
					"Exponent" -> 0.9808904248891368
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (61.954686288627585 + 0.8871114515971145*#1 & ),
					"AdjustedRSquared" -> 0.9998862499646256,
					"AIC" -> 94531.88382525663,
					"ProbMinInfoLoss" -> 9.68276594404016786731774605819293805832666808`12.881399133146584*^-515,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8905000000000001,
			"Diffusivity" -> 1.8510787666084072,
			"PecletNumber" -> 0.48107083073055634,
			"Randomness" -> 2.078695975977998
		}
	},
	7077 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-4.593461386120181 + 1.8571355787193518*#1 & ),
					"AdjustedRSquared" -> 0.9999999968021966,
					"AIC" -> 4514.200095362284,
					"ProbMinInfoLoss" -> 3.221644543940263*^-23,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.8567,
			"Diffusivity" -> 0.12291629242940297,
			"PecletNumber" -> 15.105401922746706,
			"Randomness" -> 0.06620148243087358
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-2.6731116711604415 + 1.8571271696172702*#1 & ),
					"AdjustedRSquared" -> 0.9999999969075146,
					"AIC" -> 4179.219019585298,
					"ProbMinInfoLoss" -> 1.1239109911404727*^-24,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.8569,
			"Diffusivity" -> 0.12257346958940743,
			"PecletNumber" -> 15.149281538820613,
			"Randomness" -> 0.0660097310514338
		}
	},
	7078 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7080 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7081 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7082 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7083 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7084 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7085 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 2/3
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 2/3
		}
	},
	7086 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7088 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7090 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7092 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7094 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7096 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7098 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7100 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7102 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7104 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7105 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7106 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7107 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7108 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7109 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.31640504053153573 + 1.3581248265092425*#1 & ),
					"AdjustedRSquared" -> 0.9999738328518034,
					"AIC" -> 88353.8136942126,
					"ProbMinInfoLoss" -> 1.7997347536252634*^-217,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3624,
			"Diffusivity" -> 1.184690043319195,
			"PecletNumber" -> 1.1500054446164736,
			"Randomness" -> 0.8695611004985282
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.6653842784260635 + 1.3581274903952754*#1 & ),
					"AdjustedRSquared" -> 0.9999738208624991,
					"AIC" -> 88358.43380903531,
					"ProbMinInfoLoss" -> 5.197208991548759*^-218,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3626,
			"Diffusivity" -> 1.1841449197930396,
			"PecletNumber" -> 1.1507037502117141,
			"Randomness" -> 0.8690334065705559
		}
	},
	7110 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7111 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7112 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7113 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7114 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7115 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7116 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7117 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7118 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7120 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-0.30898331831325787 + 0.7917499616674968*#1 & ),
					"AdjustedRSquared" -> 0.9999934323638999,
					"AIC" -> 63737.81826268497,
					"ProbMinInfoLoss" -> 4.348298743430681*^-212,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7916000000000001,
			"Diffusivity" -> 0.16499809612887675,
			"PecletNumber" -> 4.797631115583885,
			"Randomness" -> 0.20843620026386653
		}
	},
	7122 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7124 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7126 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7128 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7130 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7132 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7134 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7136 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7137 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7138 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7139 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7140 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	7141 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-92.48978698391679 + 1.6585597498934397*#1^0.9854385605783703 & ),
					"AdjustedRSquared" -> 0.999978943863326,
					"AIC" -> 101265.74954919062,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9854385605783703
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-21.209401080110116 + 1.4467735228637346*#1 & ),
					"AdjustedRSquared" -> 0.9998920701766852,
					"AIC" -> 103789.01575155111,
					"ProbMinInfoLoss" -> 1.2014507446711690157801639020624829082587403155982`12.8536566952353*^-548,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4371,
			"Diffusivity" -> 2.291282738996044,
			"PecletNumber" -> 0.6272032584811792,
			"Randomness" -> 1.5943794718502846
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (13.685470147012968 + 1.3920813978308149*#1 & ),
					"AdjustedRSquared" -> 0.9999453182379539,
					"AIC" -> 96218.25562732946,
					"ProbMinInfoLoss" -> 1.9882918615605017*^-62,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4006,
			"Diffusivity" -> 2.3743784660522462,
			"PecletNumber" -> 0.5898806866829044,
			"Randomness" -> 1.6952580794318477
		}
	},
	7142 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7144 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7145 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7146 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7147 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7148 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7149 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7150 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7152 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7154 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7156 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7158 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7160 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7162 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7164 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7166 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7168 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7169 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	7170 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7171 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	7172 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7173 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7174 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7175 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7176 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7177 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7178 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7179 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7180 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7181 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7182 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7184 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7185 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7186 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7187 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	7188 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7189 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7190 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7192 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7193 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7194 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7195 -> {
		{{1}, 0} -> {
			"BoundaryWordCoding" -> Missing["Unknown"],
			"BoundaryWordMorphism" -> Missing["Unknown"],
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordCoding" -> Missing["Unknown"],
			"BoundaryWordMorphism" -> Missing["Unknown"],
			"GrowthRate" -> 5/4
		}
	},
	7196 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7197 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7198 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7200 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7201 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7202 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7203 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7204 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7205 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7206 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 5/4
		}
	},
	7208 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7209 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7210 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7211 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	7212 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7213 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7214 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	7216 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7217 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7218 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7219 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (2.0509968797006883 + 1.1477229083332268*#1 & ),
					"AdjustedRSquared" -> 0.9999998300021781,
					"AIC" -> 34622.30892504924,
					"ProbMinInfoLoss" -> 6.562600110758721917811472725805`12.549933894802015*^-682,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1482,
			"Diffusivity" -> 0.8300005635690595,
			"PecletNumber" -> 1.3833725546675066,
			"Randomness" -> 0.7228710708666255
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (0.9033977197844071 + 1.1477228081752258*#1 & ),
					"AdjustedRSquared" -> 0.9999998300595059,
					"AIC" -> 34618.93434735382,
					"ProbMinInfoLoss" -> 2.4636828924218649868462080888258236685845381102007`12.75820244353632*^-683,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1480000000000001,
			"Diffusivity" -> 0.8300598213452072,
			"PecletNumber" -> 1.3830328495355124,
			"Randomness" -> 0.723048624865163
		}
	},
	7220 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7221 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7222 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7224 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7225 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7226 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7227 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (4.519897749793018 + 0.9818124792021216*#1 & ),
					"AdjustedRSquared" -> 0.9999988891425087,
					"AIC" -> 50270.640262543355,
					"ProbMinInfoLoss" -> 1.15302562507746042699528660384530810976098`12.909369931831387*^-460,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9826,
			"Diffusivity" -> 0.6884348967003121,
			"PecletNumber" -> 1.4272954562728148,
			"Randomness" -> 0.7006257853656749
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (3.537348574866192 + 0.9818124890361234*#1 & ),
					"AdjustedRSquared" -> 0.9999988891285018,
					"AIC" -> 50270.76655217784,
					"ProbMinInfoLoss" -> 3.907310219464003796569146374306030058274`12.873259815724785*^-461,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.9824,
			"Diffusivity" -> 0.688427894599822,
			"PecletNumber" -> 1.4270194565126706,
			"Randomness" -> 0.700761293363011
		}
	},
	7228 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7229 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7230 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7232 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7233 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	7234 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7235 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	7236 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7237 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7238 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7239 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7240 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7241 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7242 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7243 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7244 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7245 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7246 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		}
	},
	7248 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7249 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7250 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7251 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 56,
			"GrowthRate" -> 17/14
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 56,
			"GrowthRate" -> 17/14
		}
	},
	7252 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7253 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7254 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7256 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7257 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7258 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7259 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7260 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7261 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7262 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7264 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7265 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	7266 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7267 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (17.08654347806914 + 0.7909408312336532*#1^0.9860751028036899 & ),
					"AdjustedRSquared" -> 0.9999938633024271,
					"AIC" -> 74504.73718243062,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9860751028036899
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.8328672257718728*#1^0.980667757872047 & ),
					"AdjustedRSquared" -> 0.9999927919124675,
					"AIC" -> 76112.90664403142,
					"ProbMinInfoLoss" -> 6.17217783648299108565290152857775011`13.012489835987754*^-350,
					"Exponent" -> 0.980667757872047
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (49.766136753678154 + 0.6940781248367807*#1 & ),
					"AdjustedRSquared" -> 0.9999532543884014,
					"AIC" -> 80730.6619541311,
					"ProbMinInfoLoss" -> 1.14186155970955064399907947446236208`12.461415897088436*^-1352,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6992,
			"Diffusivity" -> 2.595629436918487,
			"PecletNumber" -> 0.2693758939758694,
			"Randomness" -> 3.712284663785021
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (16.329956074649495 + 0.7910787047517349*#1^0.9860569686625493 & ),
					"AdjustedRSquared" -> 0.9999938609075268,
					"AIC" -> 74505.65916124314,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9860569686625493
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.8311146933246758*#1^0.9808883760372389 & ),
					"AdjustedRSquared" -> 0.9999928818579455,
					"AIC" -> 75984.35759519429,
					"ProbMinInfoLoss" -> 8.02998747760014981768962852459545786202703663`12.934077147449536*^-322,
					"Exponent" -> 0.9808883760372389
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (49.052842784279214 + 0.6940809633468095*#1 & ),
					"AdjustedRSquared" -> 0.9999531956082769,
					"AIC" -> 80743.3109037944,
					"ProbMinInfoLoss" -> 3.24439772272109779263261038844689`12.460598642069057*^-1355,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.6990000000000001,
			"Diffusivity" -> 2.59550904080206,
			"PecletNumber" -> 0.2693113331572123,
			"Randomness" -> 3.7131745934221168
		}
	},
	7268 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7269 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7270 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 7/4
		}
	},
	7272 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7273 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7274 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7275 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	7276 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7277 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7278 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 26,
			"GrowthRate" -> 18/13
		}
	},
	7280 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7281 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7282 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7283 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		}
	},
	7284 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7285 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 5/3
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 5/3
		}
	},
	7286 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7288 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7289 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7290 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7291 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 38,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 38,
			"GrowthRate" -> 1
		}
	},
	7292 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7293 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7294 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7296 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7297 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7298 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7299 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7300 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7301 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7302 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7303 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 44,
			"GrowthRate" -> 14/11
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7304 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7305 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7306 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7307 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7308 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7309 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7310 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7312 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7313 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7314 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7315 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 7/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 7/4
		}
	},
	7316 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7317 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7318 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7320 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7321 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7322 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7323 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 7/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 7/4
		}
	},
	7324 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7325 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7326 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7328 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7329 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7330 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7331 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (12.850684608477753 + 1.740181324945811*#1 & ),
					"AdjustedRSquared" -> 0.9999969637190662,
					"AIC" -> 71772.55638124469,
					"ProbMinInfoLoss" -> 5.4579351089117166437685461102339908390274`12.728169179091218*^-519,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7407000000000001,
			"Diffusivity" -> 0.19204705027414123,
			"PecletNumber" -> 9.063924686764022,
			"Randomness" -> 0.11032748335390431
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-11.062027302706268 + 1.7353028151790237*#1 & ),
					"AdjustedRSquared" -> 0.9999984151457637,
					"AIC" -> 65214.98463787248,
					"ProbMinInfoLoss" -> 8.505388176904566*^-10,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.734,
			"Diffusivity" -> 0.19522916484487016,
			"PecletNumber" -> 8.88186968057689,
			"Randomness" -> 0.11258890706163216
		}
	},
	7332 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7333 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7334 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (11.674937053704637 + 1.2934018324060188*#1 & ),
					"AdjustedRSquared" -> 0.9999954651684857,
					"AIC" -> 69849.84696083664,
					"ProbMinInfoLoss" -> 5.7667070475895010142134598854941583755378`12.630297424764468*^-885,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2954,
			"Diffusivity" -> 0.2081717473607733,
			"PecletNumber" -> 6.222746440971163,
			"Randomness" -> 0.1607007467660748
		}
	},
	7336 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7337 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7338 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7339 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (3.2800154215644586 + 1.4113299039252964*#1 & ),
					"AdjustedRSquared" -> 0.9999910289894308,
					"AIC" -> 78417.12786747333,
					"ProbMinInfoLoss" -> 1.703832848065617*^-191,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4111,
			"Diffusivity" -> 0.38915771953270545,
			"PecletNumber" -> 3.62603625515749,
			"Randomness" -> 0.27578323260768584
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (34.471214041422364 + 1.4139040067910378*#1 & ),
					"AdjustedRSquared" -> 0.999995068796014,
					"AIC" -> 72469.38037772251,
					"ProbMinInfoLoss" -> 3.482446769269634*^-113,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4177,
			"Diffusivity" -> 0.38488623817372736,
			"PecletNumber" -> 3.6834260604560463,
			"Randomness" -> 0.2714863780586354
		}
	},
	7340 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7341 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7342 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	7344 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7345 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7346 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7347 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 7/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 7/4
		}
	},
	7348 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7349 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 13/6
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 13/6
		}
	},
	7350 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7352 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7353 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7354 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7355 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-19.914634683434276 + 1.2796089260440842*#1 & ),
					"AdjustedRSquared" -> 0.9999937202361124,
					"AIC" -> 72890.88248441754,
					"ProbMinInfoLoss" -> 4.50049855878420461978376157729127998`12.653181051922596*^-870,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2766,
			"Diffusivity" -> 0.5071862257239926,
			"PecletNumber" -> 2.5170241920069754,
			"Randomness" -> 0.39729455250195256
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-21.18751335132751 + 1.279608221848082*#1 & ),
					"AdjustedRSquared" -> 0.9999937174878447,
					"AIC" -> 72895.24693537323,
					"ProbMinInfoLoss" -> 3.391336400430909495715283700345428`12.652121825021625*^-872,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2766,
			"Diffusivity" -> 0.5069861857159911,
			"PecletNumber" -> 2.5180173266400185,
			"Randomness" -> 0.39713785501800963
		}
	},
	7356 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7357 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7358 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7360 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7361 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7362 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7363 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7364 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7365 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7366 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7367 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 5,
			"GrowthRate" -> 6/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 5,
			"GrowthRate" -> 6/5
		}
	},
	7368 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7369 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7370 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7371 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7372 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7373 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7374 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7376 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7377 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7378 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7379 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (5.7931650764943345 + 1.660301736811016*#1 & ),
					"AdjustedRSquared" -> 0.999999605889516,
					"AIC" -> 50415.15688815359,
					"ProbMinInfoLoss" -> 6.56146987146311501217493735871136`12.534638389991105*^-1143,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.661,
			"Diffusivity" -> 0.22408011955426388,
			"PecletNumber" -> 7.412527284009092,
			"Randomness" -> 0.13490675469853333
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (3.7093902190530215 + 1.6603767242837633*#1 & ),
					"AdjustedRSquared" -> 0.9999995739129638,
					"AIC" -> 51196.18398827837,
					"ProbMinInfoLoss" -> 2.286789184181446902665340812274600823572`12.444499735102948*^-1406,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6607,
			"Diffusivity" -> 0.22417668852302314,
			"PecletNumber" -> 7.407995947042659,
			"Randomness" -> 0.13498927471730182
		}
	},
	7380 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7381 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7382 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7384 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7385 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7386 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7387 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7388 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7389 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7390 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7392 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7393 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7394 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7395 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-1.2553893789282304 + 1.59768426944884*#1 & ),
					"AdjustedRSquared" -> 0.9999999636267151,
					"AIC" -> 25818.30410567249,
					"ProbMinInfoLoss" -> 1.10121728721135856251107202694263035`12.67595758327383*^-639,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5976000000000001,
			"Diffusivity" -> 0.24048662117662056,
			"PecletNumber" -> 6.643196998583447,
			"Randomness" -> 0.15052993313509047
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-2.365367596773431 + 1.5978753059887545*#1 & ),
					"AdjustedRSquared" -> 0.9999999742572484,
					"AIC" -> 22363.88046416025,
					"ProbMinInfoLoss" -> 2.804804674934078*^-23,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.5976000000000001,
			"Diffusivity" -> 0.24048662117662056,
			"PecletNumber" -> 6.643196998583447,
			"Randomness" -> 0.15052993313509047
		}
	},
	7396 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7397 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7398 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-9.965619201917436 + 1.7136599778425998*#1 & ),
					"AdjustedRSquared" -> 0.9999944746423928,
					"AIC" -> 77452.56915391103,
					"ProbMinInfoLoss" -> 1.0524728456375773230038563687212953998355`12.65536912569723*^-865,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7136,
			"Diffusivity" -> 0.2043649854083228,
			"PecletNumber" -> 8.384998029756488,
			"Randomness" -> 0.11926061239981489
		}
	},
	7400 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7401 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7402 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7403 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-341.7911951921884 + 341.51625273490646*#1^0.03195995139344754 & ),
					"AdjustedRSquared" -> 0.9996263784613582,
					"AIC" -> 42241.931357019916,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.03195995139344754
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (29.92232344931661*#1^0.14877687772212944 & ),
					"AdjustedRSquared" -> 0.9992794172652619,
					"AIC" -> 48809.100428676866,
					"ProbMinInfoLoss" -> 9.0647373891342453292877392046949038148`12.438241568519354*^-1427,
					"Exponent" -> 0.14877687772212944
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (81.83614677468027 + 0.004133477297334756*#1 & ),
					"AdjustedRSquared" -> 0.735773918484229,
					"AIC" -> 67727.24900501024,
					"ProbMinInfoLoss" -> 8.581989189379529663540647206762346`11.849329714867288*^-5535,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.0118,
			"Diffusivity" -> 1.0113653693835076,
			"PecletNumber" -> 0.011667395737697506,
			"Randomness" -> 85.70892960877184
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7404 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7405 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7406 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 3/2
		}
	},
	7408 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7409 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7410 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7411 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7412 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7413 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 9/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 9/4
		}
	},
	7414 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7416 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7417 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7418 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7419 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-891.5272931700442 + 903.4165849280158*#1^0.013320131911337593 & ),
					"AdjustedRSquared" -> 0.9985667637738251,
					"AIC" -> 58204.70077838822,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.013320131911337593
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (43.65480860656979*#1^0.11879329053780152 & ),
					"AdjustedRSquared" -> 0.9978628204399245,
					"AIC" -> 62199.22117464831,
					"ProbMinInfoLoss" -> 3.9894867509815413315259719892855718472`12.541152510741815*^-868,
					"Exponent" -> 0.11879329053780152
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (99.00474857486243 + 0.0034963606489635756*#1 & ),
					"AdjustedRSquared" -> 0.5200363917245903,
					"AIC" -> 73818.04995986723,
					"ProbMinInfoLoss" -> 4.02071442017910792348409704514824874256`12.06212369334861*^-3391,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.0126,
			"Diffusivity" -> 1.010945923558149,
			"PecletNumber" -> 0.01246357466446152,
			"Randomness" -> 80.23380345699596
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7420 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7421 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7422 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7424 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7425 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7426 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7427 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7428 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7429 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	7430 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7431 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7432 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7433 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	7434 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7435 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7436 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7437 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	7438 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7440 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7442 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7444 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7446 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7448 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7450 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7452 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7454 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7456 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7457 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7458 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7459 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7460 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7461 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7462 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7464 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7465 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-7.239969516953571 + 1.2735351003933502*#1 & ),
					"AdjustedRSquared" -> 0.9999977117432914,
					"AIC" -> 62700.26285049424,
					"ProbMinInfoLoss" -> 4.871273154617934*^-80,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2730000000000001,
			"Diffusivity" -> 0.19910336702804107,
			"PecletNumber" -> 6.393663849093596,
			"Randomness" -> 0.15640484448392855
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-8.509830723069028 + 1.273534492695343*#1 & ),
					"AdjustedRSquared" -> 0.9999977112653646,
					"AIC" -> 62702.34170013162,
					"ProbMinInfoLoss" -> 2.800553375498919*^-80,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2728000000000002,
			"Diffusivity" -> 0.1992125597836839,
			"PecletNumber" -> 6.389155389509965,
			"Randomness" -> 0.15651521038944366
		}
	},
	7466 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7467 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7468 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7469 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	7470 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7472 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7474 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7476 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7478 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7480 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	7482 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7484 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7486 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7488 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7489 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	7490 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7491 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7492 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7493 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	7494 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7495 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7496 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7497 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	7498 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7499 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (17.345174497454142 + 0.5880609390066086*#1 & ),
					"AdjustedRSquared" -> 0.9999373865347921,
					"AIC" -> 80338.34143538972,
					"ProbMinInfoLoss" -> 4.3545734672497832996788352570085965610471672657406`12.981147106461853*^-336,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.5887,
			"Diffusivity" -> 0.24216382430401473,
			"PecletNumber" -> 2.43099893921786,
			"Randomness" -> 0.41135353202652414
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (16.748383918396726 + 0.588062576958625*#1 & ),
					"AdjustedRSquared" -> 0.9999373817849713,
					"AIC" -> 80339.15575505885,
					"ProbMinInfoLoss" -> 6.5415986452172680196186199886674855020691936205511`13.067090392500859*^-336,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.5887,
			"Diffusivity" -> 0.24216382430401473,
			"PecletNumber" -> 2.43099893921786,
			"Randomness" -> 0.41135353202652414
		}
	},
	7500 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7501 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	7502 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7504 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7506 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7508 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7510 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7512 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7514 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7516 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7518 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7520 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7521 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 0
		}
	},
	7522 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7523 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7524 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7525 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7526 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7528 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7529 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 48,
			"GrowthRate" -> 3/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 48,
			"GrowthRate" -> 3/4
		}
	},
	7530 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7531 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 0
		}
	},
	7532 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7533 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	7534 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7536 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7538 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7540 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7542 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7544 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7546 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7548 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7550 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7552 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7553 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7554 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7555 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-10.944393339313686 + 1.300352503417523*#1 & ),
					"AdjustedRSquared" -> 0.9999997314440915,
					"AIC" -> 41692.15453528284,
					"ProbMinInfoLoss" -> 1.68109973520786195485393488819447080628620649`11.924288882076416*^-4657,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2995,
			"Diffusivity" -> 0.6037115213821842,
			"PecletNumber" -> 2.1525181381743774,
			"Randomness" -> 0.4645721595861363
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-12.23908412839752 + 1.3003515816675149*#1 & ),
					"AdjustedRSquared" -> 0.9999997303150626,
					"AIC" -> 41734.09298103467,
					"ProbMinInfoLoss" -> 3.855490903827839978642336937696573366`11.856712319642982*^-4645,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2994,
			"Diffusivity" -> 0.6038714493573782,
			"PecletNumber" -> 2.151782471886661,
			"Randomness" -> 0.46473099073216734
		}
	},
	7556 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7557 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7558 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7559 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7560 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7561 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	7562 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7563 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7564 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7565 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7566 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7568 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7570 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7572 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7574 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7576 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7578 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7580 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7582 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7584 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7585 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7586 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7587 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (10.15598211822042 + 1.0175419893774178*#1 & ),
					"AdjustedRSquared" -> 0.9999963695458696,
					"AIC" -> 62827.81762298699,
					"ProbMinInfoLoss" -> 2.2894219565110300556854024616943398`12.190124406387731*^-1584,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0186,
			"Diffusivity" -> 0.482950595519644,
			"PecletNumber" -> 2.1091184262937066,
			"Randomness" -> 0.47413174506150013
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (9.135262526252776 + 1.0175424532494244*#1 & ),
					"AdjustedRSquared" -> 0.9999963688041204,
					"AIC" -> 62829.86967014573,
					"ProbMinInfoLoss" -> 3.757445910813962578346551735851956`12.27366508635832*^-1585,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0186,
			"Diffusivity" -> 0.482950595519644,
			"PecletNumber" -> 2.1091184262937066,
			"Randomness" -> 0.47413174506150013
		}
	},
	7588 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 9/5
		}
	},
	7589 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 12,
			"GrowthRate" -> 19/12
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 12,
			"GrowthRate" -> 19/12
		}
	},
	7590 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7592 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7593 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7594 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7595 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7596 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7597 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7598 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7600 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7602 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7604 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 5,
			"GrowthRate" -> 4/5
		}
	},
	7606 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7608 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.82668160815083 + 1.4397302106573033*#1 & ),
					"AdjustedRSquared" -> 0.9999953685428958,
					"AIC" -> 72204.28221161217,
					"ProbMinInfoLoss" -> 1.79849038694521454926710262574232`12.615224539307697*^-949,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4384000000000001,
			"Diffusivity" -> 0.24623546571500518,
			"PecletNumber" -> 5.841563057633686,
			"Randomness" -> 0.1711870590343473
		}
	},
	7610 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7612 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7614 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7616 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7617 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7618 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7619 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (249.6981142455567 + 0.46061094815667436*#1^1.0531399221102915 & ),
					"AdjustedRSquared" -> 0.9996254727990782,
					"AIC" -> 117637.00753654775,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0531399221102915
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (122.23354269427803 + 0.757482723188826*#1 & ),
					"AdjustedRSquared" -> 0.9981436389076564,
					"AIC" -> 119313.62827300109,
					"ProbMinInfoLoss" -> 8.441759143044728761976462458394506520161`12.89639372444348*^-365,
					"Exponent" -> 1
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.9604178033924708*#1^0.9759508775657688 & ),
					"AdjustedRSquared" -> 0.9994339360870893,
					"AIC" -> 121766.4333787173,
					"ProbMinInfoLoss" -> 2.02568381685007293724154267900572543727179805803`12.63973009456465*^-897,
					"Exponent" -> 0.9759508775657688
				}
			},
			"GrowthRate" -> 0.778,
			"Diffusivity" -> 1.5656241959463,
			"PecletNumber" -> 0.49692640290970885,
			"Randomness" -> 2.0123704318075837
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7620 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7621 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7622 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7624 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7625 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7626 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7627 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7628 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7629 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7630 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7632 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7634 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7636 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7638 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7640 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7642 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7644 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7646 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7648 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7649 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7650 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7651 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (24.38237414725838 + 0.21884809732194288*#1^1.0674875018001801 & ),
					"AdjustedRSquared" -> 0.9999310555107928,
					"AIC" -> 87569.57826211589,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1.0674875018001801
				},
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.2513465231103804*#1^1.0529303638595968 & ),
					"AdjustedRSquared" -> 0.9999233385310072,
					"AIC" -> 88629.55396861843,
					"ProbMinInfoLoss" -> 6.748385090107935*^-231,
					"Exponent" -> 1.0529303638595968
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (-62.36003204319948 + 0.41151473493514706*#1 & ),
					"AdjustedRSquared" -> 0.9992531651803174,
					"AIC" -> 97994.10749169876,
					"ProbMinInfoLoss" -> 2.199072646291012347486760005526737459299055540559`12.12264257069996*^-2264,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.40940000000000004,
			"Diffusivity" -> 1.9599487454246525,
			"PecletNumber" -> 0.20888301337252438,
			"Randomness" -> 4.787368699132028
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7652 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.037008640844143 + 1.7845110906191075*#1 & ),
					"AdjustedRSquared" -> 0.9999999193001848,
					"AIC" -> 35999.10622325865,
					"ProbMinInfoLoss" -> 5.249401293364679*^-83,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.784,
			"Diffusivity" -> 0.1693163915311315,
			"PecletNumber" -> 10.536487246552165,
			"Randomness" -> 0.09490829121700196
		}
	},
	7653 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-4.559663366338356 + 1.3757199606772013*#1 & ),
					"AdjustedRSquared" -> 0.9999996802806205,
					"AIC" -> 44562.83694040292,
					"ProbMinInfoLoss" -> 4.236630768633838398548704225234096053725`12.111882354129666*^-3024,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3755000000000002,
			"Diffusivity" -> 0.23453255507587167,
			"PecletNumber" -> 5.86485743761681,
			"Randomness" -> 0.17050712837213497
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (2.252068166820682 + 1.3762289234742882*#1 & ),
					"AdjustedRSquared" -> 0.9999993507559658,
					"AIC" -> 51653.887982395216,
					"ProbMinInfoLoss" -> 4.84472106726079949402407937262248796801367394665`12.162657334194376*^-1745,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3758000000000001,
			"Diffusivity" -> 0.23480719746309497,
			"PecletNumber" -> 5.859275247370715,
			"Randomness" -> 0.17066957222204895
		}
	},
	7654 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7656 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7657 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7658 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7659 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7660 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7661 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7662 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7664 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7666 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7668 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7670 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7672 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7674 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7676 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7678 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 3
		}
	},
	7680 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7681 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-37.266311851182266 + 1.2598950728629503*#1 & ),
					"AdjustedRSquared" -> 0.9999599920783956,
					"AIC" -> 91098.14940923486,
					"ProbMinInfoLoss" -> 2.2978427462558084*^-236,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2562,
			"Diffusivity" -> 4.034561907881126,
			"PecletNumber" -> 0.31135970365112875,
			"Randomness" -> 3.211719398090372
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-38.5108372637129 + 1.2598927581769248*#1 & ),
					"AdjustedRSquared" -> 0.9999599808663995,
					"AIC" -> 91100.91482863913,
					"ProbMinInfoLoss" -> 6.255834480540541*^-237,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2559,
			"Diffusivity" -> 4.03441552396888,
			"PecletNumber" -> 0.31129664074971164,
			"Randomness" -> 3.212370032621132
		}
	},
	7682 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7683 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	7684 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7685 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	7686 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 5,
			"GrowthRate" -> 6/5
		}
	},
	7687 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7688 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7689 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7690 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7691 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 1
		}
	},
	7692 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7693 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7694 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 5,
			"GrowthRate" -> 6/5
		}
	},
	7696 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7697 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7698 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7699 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7700 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7701 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7702 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7704 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7705 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 796,
			"GrowthRate" -> 329/199
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 796,
			"GrowthRate" -> 329/199
		}
	},
	7706 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7707 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 160,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 160,
			"GrowthRate" -> 1
		}
	},
	7708 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7709 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7710 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7712 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7713 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7714 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7715 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (5.1418868287181265 + 1.3334785947747803*#1 & ),
					"AdjustedRSquared" -> 0.9999976166692064,
					"AIC" -> 64027.239883378024,
					"ProbMinInfoLoss" -> 3.10779303257894491567639199161197962025`12.692658691488434*^-501,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3331000000000002,
			"Diffusivity" -> 0.5562445422377805,
			"PecletNumber" -> 2.396607784477162,
			"Randomness" -> 0.4172564265529821
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (3.8049653765582487 + 1.3334793789867911*#1 & ),
					"AdjustedRSquared" -> 0.9999976170945379,
					"AIC" -> 64025.466871760524,
					"ProbMinInfoLoss" -> 1.012574898969794375502872155071154887668`12.771784619117863*^-500,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3329,
			"Diffusivity" -> 0.5563777822071065,
			"PecletNumber" -> 2.3956743828132234,
			"Randomness" -> 0.41741899782962455
		}
	},
	7716 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7717 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (4.902349414921483 + 1.627085421574853*#1 & ),
					"AdjustedRSquared" -> 0.9999982434979708,
					"AIC" -> 64955.473405135825,
					"ProbMinInfoLoss" -> 2.44409075560044554214321847075102189248857118`12.18149366143471*^-2576,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6273,
			"Diffusivity" -> 1.9799513458047144,
			"PecletNumber" -> 0.8218888830011195,
			"Randomness" -> 1.2167094855310725
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (3.2731515751482227 + 1.6270858211028545*#1 & ),
					"AdjustedRSquared" -> 0.9999982434643079,
					"AIC" -> 64955.66996338292,
					"ProbMinInfoLoss" -> 3.1299393896663325847380588481318080875594184694`12.181849155565423*^-2574,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.627,
			"Diffusivity" -> 1.980027688706058,
			"PecletNumber" -> 0.821705680824716,
			"Randomness" -> 1.2169807551973313
		}
	},
	7718 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.1704493849206488 + 1.4984707228047036*#1 & ),
					"AdjustedRSquared" -> 0.9999998915143509,
					"AIC" -> 35463.934440590194,
					"ProbMinInfoLoss" -> 9.9121112972254753372305614973437261`12.362435415012694*^-1699,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.498,
			"Diffusivity" -> 0.25002120135998396,
			"PecletNumber" -> 5.99149188889449,
			"Randomness" -> 0.16690333869157808
		}
	},
	7720 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7721 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.602343234312721 + 1.7752811005368085*#1 & ),
					"AdjustedRSquared" -> 0.9999997807867771,
					"AIC" -> 45888.47948624041,
					"ProbMinInfoLoss" -> 7.834114469429600439812049196401688`12.392589839809238*^-1585,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7756,
			"Diffusivity" -> 1.6231091002678983,
			"PecletNumber" -> 1.0939498766330202,
			"Randomness" -> 0.9141186642644168
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-5.374424722463011 + 1.7752804169028018*#1 & ),
					"AdjustedRSquared" -> 0.9999997808817311,
					"AIC" -> 45884.13925807663,
					"ProbMinInfoLoss" -> 4.863061139553995658314974143246739`12.385712783660393*^-1585,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.7753,
			"Diffusivity" -> 1.6232744498694718,
			"PecletNumber" -> 1.0936536333352336,
			"Randomness" -> 0.9143662760488209
		}
	},
	7722 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7723 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (16.323400840096298 + 1.0694350963223493*#1 & ),
					"AdjustedRSquared" -> 0.9999923875305937,
					"AIC" -> 71226.96926885987,
					"ProbMinInfoLoss" -> 9.592877651408209*^-144,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0707,
			"Diffusivity" -> 0.5208051711352372,
			"PecletNumber" -> 2.0558551630086868,
			"Randomness" -> 0.4864155889934036
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (15.24710129014624 + 1.0694362361183596*#1 & ),
					"AdjustedRSquared" -> 0.9999923852258923,
					"AIC" -> 71230.017684167,
					"ProbMinInfoLoss" -> 3.9832673414500965*^-144,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.0705,
			"Diffusivity" -> 0.5208334196092144,
			"PecletNumber" -> 2.055359659530306,
			"Randomness" -> 0.48653285344158276
		}
	},
	7724 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7725 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7726 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-3.582358595864499 + 1.4388904826709048*#1 & ),
					"AdjustedRSquared" -> 0.9999995178871387,
					"AIC" -> 49568.086563502984,
					"ProbMinInfoLoss" -> 6.202915183878911*^-72,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4379000000000002,
			"Diffusivity" -> 0.24617364717067827,
			"PecletNumber" -> 5.840998890523276,
			"Randomness" -> 0.17120359355356995
		}
	},
	7728 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7729 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7730 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7731 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (2.8539875787764326 + 1.1221775047337714*#1 & ),
					"AdjustedRSquared" -> 0.9999994348518665,
					"AIC" -> 46185.157405321064,
					"ProbMinInfoLoss" -> 9.399340419423466206861255184284325621725739236`12.498791630789592*^-937,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1221,
			"Diffusivity" -> 0.8631627315562123,
			"PecletNumber" -> 1.2999866177921573,
			"Randomness" -> 0.7692386877784619
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (1.730342454259517 + 1.1221778337257757*#1 & ),
					"AdjustedRSquared" -> 0.9999994349450407,
					"AIC" -> 46183.5144679498,
					"ProbMinInfoLoss" -> 5.3523682078285119993151763474859866332985233722`12.621436402306843*^-936,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.1219000000000001,
			"Diffusivity" -> 0.8632115461996289,
			"PecletNumber" -> 1.2996814105873258,
			"Randomness" -> 0.7694193298864683
		}
	},
	7732 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7733 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7734 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7736 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7737 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7738 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7739 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7740 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7741 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7742 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7744 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7745 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-49.2699222384279 + 1.4739861511201036*#1^0.986793437701045 & ),
					"AdjustedRSquared" -> 0.9999804123503611,
					"AIC" -> 98501.919508825,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.986793437701045
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (8.838984878500344 + 1.3022244205822406*#1 & ),
					"AdjustedRSquared" -> 0.9999017332538624,
					"AIC" -> 100745.72309671229,
					"ProbMinInfoLoss" -> 5.81087660098300236234549098172669`12.904634927722748*^-488,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.296,
			"Diffusivity" -> 3.74292382228821,
			"PecletNumber" -> 0.34625337344100676,
			"Randomness" -> 2.888058504852014
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(3)",
					"Fit" -> (-50.54206542748666 + 1.4738436804982158*#1^0.9868041238855465 & ),
					"AdjustedRSquared" -> 0.9999804073640135,
					"AIC" -> 98501.49957419028,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9868041238855465
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (7.519403960386409 + 1.3022291562922923*#1 & ),
					"AdjustedRSquared" -> 0.9999017693016033,
					"AIC" -> 100742.12643969367,
					"ProbMinInfoLoss" -> 2.844842018195249632627324810039082`12.769128112412107*^-487,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.2957,
			"Diffusivity" -> 3.742801325541636,
			"PecletNumber" -> 0.3461845519712415,
			"Randomness" -> 2.88863265072288
		}
	},
	7746 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7747 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/4
		}
	},
	7748 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7749 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 1
		}
	},
	7750 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 5/3
		}
	},
	7752 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7753 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7754 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7755 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 2/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 2/5
		}
	},
	7756 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7757 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7758 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 5/3
		}
	},
	7760 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7761 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7762 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7763 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		}
	},
	7764 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7765 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7766 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7768 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7769 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7770 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7771 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 8,
			"GrowthRate" -> 1
		}
	},
	7772 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7773 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7774 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7776 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7777 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-19.194090249012813 + 1.6954407139784062*#1 & ),
					"AdjustedRSquared" -> 0.9999936242253193,
					"AIC" -> 78670.37985525219,
					"ProbMinInfoLoss" -> 7.184053392312159*^-76,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6899000000000002,
			"Diffusivity" -> 1.9428789648318703,
			"PecletNumber" -> 0.8697917011759084,
			"Randomness" -> 1.1497005531876858
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-20.888698109791154 + 1.6954416754544146*#1 & ),
					"AdjustedRSquared" -> 0.999993628006636,
					"AIC" -> 78664.458643395,
					"ProbMinInfoLoss" -> 4.750807543071406*^-75,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.6896,
			"Diffusivity" -> 1.9429928790038435,
			"PecletNumber" -> 0.8695863058778909,
			"Randomness" -> 1.1499721111528431
		}
	},
	7778 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7779 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (11.154097629766914 + 0.8929721632577203*#1 & ),
					"AdjustedRSquared" -> 0.9999959827734776,
					"AIC" -> 61228.36597645196,
					"ProbMinInfoLoss" -> 0.0005687067234511755,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8951,
			"Diffusivity" -> 1.449584806450239,
			"PecletNumber" -> 0.6174871563340484,
			"Randomness" -> 1.6194668824156395
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (10.259089288937687 + 0.8929721649257193*#1 & ),
					"AdjustedRSquared" -> 0.9999959827650082,
					"AIC" -> 61228.38709664729,
					"ProbMinInfoLoss" -> 0.0003912171318547072,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.8949,
			"Diffusivity" -> 1.4495427938472982,
			"PecletNumber" -> 0.6173670786391927,
			"Randomness" -> 1.619781868194545
		}
	},
	7780 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7781 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-16.857991119099903 + 1.367249833240495*#1 & ),
					"AdjustedRSquared" -> 0.9999984319832742,
					"AIC" -> 60340.563368810755,
					"ProbMinInfoLoss" -> 2.49056716219882476423520842991349016812394544000799`12.712359123902067*^-759,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.3663,
			"Diffusivity" -> 2.8852879486788447,
			"PecletNumber" -> 0.47354025813112355,
			"Randomness" -> 2.1117528717549914
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-18.21662538252422 + 1.3672483202444794*#1 & ),
					"AdjustedRSquared" -> 0.9999984302814728,
					"AIC" -> 60351.38857699591,
					"ProbMinInfoLoss" -> 1.1117645046235762504813699150738708318176623952324`12.711586783568508*^-760,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.366,
			"Diffusivity" -> 2.885207644589224,
			"PecletNumber" -> 0.47344945954296536,
			"Randomness" -> 2.112157865731496
		}
	},
	7782 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 7/4
		}
	},
	7784 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7785 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7786 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7787 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 5/4
		}
	},
	7788 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7789 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7790 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 5/3
		}
	},
	7792 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7793 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7794 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7795 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 6/5
		}
	},
	7796 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7797 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 17/10
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 17/10
		}
	},
	7798 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7800 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7801 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7802 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7803 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.8978093028916573*#1^0.9794511567736787 & ),
					"AdjustedRSquared" -> 0.999971224663252,
					"AIC" -> 91242.05376832938,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.9794511567736787
				},
				{
					"FitName" -> "Power(3)",
					"Fit" -> (1.1068419578480244 + 0.8950136072823826*#1^0.9797775686475889 & ),
					"AdjustedRSquared" -> 0.9999712257088271,
					"AIC" -> 91242.69015351651,
					"ProbMinInfoLoss" -> 0.7274626702936371,
					"Exponent" -> 0.9797775686475889
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (52.05264746474744 + 0.740315958911159*#1 & ),
					"AdjustedRSquared" -> 0.9998366130016205,
					"AIC" -> 94535.69146772957,
					"ProbMinInfoLoss" -> 6.24684716982459909663098711273552362`12.737943940846682*^-716,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7411,
			"Diffusivity" -> 0.6041849233933195,
			"PecletNumber" -> 1.2266112100873292,
			"Randomness" -> 0.8152542482705701
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Power(2)",
					"Fit" -> (0.8958781084809114*#1^0.979677265271854 & ),
					"AdjustedRSquared" -> 0.9999712208214768,
					"AIC" -> 91240.44506939806,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 0.979677265271854
				},
				{
					"FitName" -> "Power(3)",
					"Fit" -> (0.3268018583464666 + 0.8950534164096293*#1^0.9797736543346771 & ),
					"AdjustedRSquared" -> 0.999971218284951,
					"AIC" -> 91242.32615587118,
					"ProbMinInfoLoss" -> 0.39041568966479273,
					"Exponent" -> 0.9797736543346771
				},
				{
					"FitName" -> "Linear",
					"Fit" -> (51.28306534654753 + 0.7403216747632139*#1 & ),
					"AdjustedRSquared" -> 0.9998366013193335,
					"AIC" -> 94536.56098209257,
					"ProbMinInfoLoss" -> 1.80935465315141149776528002686515523`12.712447168161503*^-716,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 0.7409,
			"Diffusivity" -> 0.604081292306066,
			"PecletNumber" -> 1.2264905558846755,
			"Randomness" -> 0.8153344477069322
		}
	},
	7804 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7805 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 3/2
		}
	},
	7806 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7808 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7809 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7810 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7811 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7812 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7813 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7814 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 5,
			"GrowthRate" -> 6/5
		}
	},
	7815 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7816 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7817 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7818 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7819 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	7820 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7821 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7822 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 3,
			"GrowthRate" -> 4/3
		}
	},
	7824 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7825 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7826 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7827 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7828 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 0
		}
	},
	7829 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7830 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7832 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7833 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 7/3
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 6,
			"GrowthRate" -> 7/3
		}
	},
	7834 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7835 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 4,
			"GrowthRate" -> 3/2
		}
	},
	7836 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 1
		}
	},
	7837 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 2
		}
	},
	7838 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 2
		}
	},
	7840 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7841 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7842 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7843 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-1.0974203420255801 + 1.8278583782305824*#1 & ),
					"AdjustedRSquared" -> 0.9999998409076938,
					"AIC" -> 43266.60026982633,
					"ProbMinInfoLoss" -> 1.2304650652186036*^-246,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.8273000000000001,
			"Diffusivity" -> 0.14283482759158092,
			"PecletNumber" -> 12.793098369712363,
			"Randomness" -> 0.07816714693349801
		},
		{{0}, 1} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-2.831860606038245 + 1.8277382782933782*#1 & ),
					"AdjustedRSquared" -> 0.9999999642948392,
					"AIC" -> 28323.391492966835,
					"ProbMinInfoLoss" -> 1.,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.8271000000000002,
			"Diffusivity" -> 0.1429657668707459,
			"PecletNumber" -> 12.779982509042641,
			"Randomness" -> 0.07824736843672807
		}
	},
	7844 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7845 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 2,
			"GrowthRate" -> 5/2
		}
	},
	7846 -> {
		{{1}, 0} -> {
			"BestFits" -> {
				{
					"FitName" -> "Linear",
					"Fit" -> (-22.587651005106167 + 1.4309416560354167*#1 & ),
					"AdjustedRSquared" -> 0.9999898839999507,
					"AIC" -> 79894.34482889331,
					"ProbMinInfoLoss" -> 1.42200670632370144523193126848307501691229563`12.268681479119632*^-1882,
					"Exponent" -> 1
				}
			},
			"GrowthRate" -> 1.4288,
			"Diffusivity" -> 0.24496116344981167,
			"PecletNumber" -> 5.832761323787297,
			"Randomness" -> 0.17144538315356359
		}
	},
	7848 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 1,
			"GrowthRate" -> 0
		}
	},
	7849 -> {
		{{1}, 0} -> {
			"BoundaryWordPeriodLength" -> 254,
			"GrowthRate" -> 297/127
		},
		{{0}, 1} -> {
			"BoundaryWordPeriodLength" -> 10,
			"GrowthRate" -> 12/5
		}
	},
	7850 -> {
		}
