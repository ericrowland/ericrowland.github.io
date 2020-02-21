(* :Title: Symbolic Words *)

(* :Context: SymbolicWords` *)

(* :Author: Eric Rowland *)

(* :Date: {2016, 12, 10} *)

(* :Package Version: 1.01 *)

(* :Mathematica Version: 11 *)

(* :Discussion:
	SymbolicWords is a collection of tools for manipulating run-length encodings of words and morphisms with symbolic exponents.
	Documentation can be found at  http://people.hofstra.edu/Eric_Rowland/packages.html .
*)


BeginPackage["SymbolicWords`"]

SymbolicWords`Private`$SymbolList = {
	EventuallyPeriodicSymbolicWord,
	EventuallyPeriodicSymbolicWordQ,
	LocatingLength,
	PowerFreeMorphismObstructions,
	PowerFreePrefixLength,
	PowerFreeWordTransientObstructions,
	SowFailedMinExpressions,
	SymbolicWord,
	SymbolicWordAppend,
	SymbolicWordBlockDrop,
	SymbolicWordBlockTake,
	SymbolicWordCharacters,
	SymbolicWordFactorList,
	SymbolicWordFirstBlockCharacter,
	SymbolicWordFirstCharacter,
	SymbolicWordJoin,
	SymbolicWordLength,
	SymbolicWordPartitionAt,
	SymbolicWordPower,
	SymbolicWordQ,
	SymbolicWordSimplified,
	SymbolicWordSimplify,
	SymbolicWordUnequal,
	ToSymbolicWord,
	TransientOnly,
	$PowerFreeMorphismList
}


Unprotect["SymbolicWords`*"]

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


EventuallyPeriodicSymbolicWord::usage =
box[EventuallyPeriodicSymbolicWord["prefix", "period"]] <> " represents an eventually periodic infinite word beginning with " <> box["prefix"] <> " and followed by repeating copies of " <> box["period"] <> "."

EventuallyPeriodicSymbolicWordQ::usage =
box[SymbolicWordQ["expr"]] <> " yields True if " <> box["expr"] <> " is a valid EventuallyPeriodicSymbolicWord object, and False otherwise."

LocatingLength::usage =
"LocatingLength is an option for PowerFreeMorphismObstructions that specifies a length to test whether the morphism locates words of that length."

PowerFreeMorphismObstructions::usage =
box[PowerFreeMorphismObstructions["n" :> "\[CurlyPhi]"["n"], "a" / "b", "assum"]] <> " gives a list of symbolic factors of " <> box["\[CurlyPhi]"[Subscript["n", 1]]] <> " " <> box["\[CurlyPhi]"[Subscript["n", 2]]] <> " " <> box["\[CurlyPhi]"[Subscript["n", 3]]] <> " \[CenterEllipsis] that SymbolicWordUnequal does not rule out as being " <> box["a"] <> "/" <> box["b"] <> "\[Hyphen]powers, along with their corresponding intervals, using the assumptions " <> box["assum"] <> ".\n" <>
box[PowerFreeMorphismObstructions["n" :> "word", "a" / "b"]] <> " uses default assumptions specified by any enclosing Assuming constructs."

PowerFreePrefixLength::usage =
"PowerFreePrefixLength is an option for PowerFreeWordTransientObstructions that specifies a prefix of the word in which to skip the check for " <> box["a"] <> "/" <> box["b"] <> "\[Hyphen]powers."

PowerFreeWordTransientObstructions::usage =
box[PowerFreeWordTransientObstructions["word", "a" / "b", "n", "assum"]] <> " gives a list of symbolic factors, overlapping the transient factor of an eventually periodic word, that SymbolicWordUnequal does not rule out as being " <> box["a"] <> "/" <> box["b"] <> "\[Hyphen]powers, along with their corresponding intervals, using the assumptions " <> box["assum"] <> "."

SowFailedMinExpressions::usage =
"SowFailedMinExpressions is an option for SymbolicWordFactorList and SymbolicWordPartitionAt that specifies whether to sow Min[ ] expressions that cannot be resolved, rather than printing messages about them."

SymbolicWord::usage =
box[SymbolicWord[SubscriptSequence["b", {1, 2, "..."}]]] <> " represents a symbolic word with blocks " <> box[Subscript["b", "i"]] <> "."

SymbolicWordAppend::usage =
box[SymbolicWordAppend["word", "newblock"]] <> " gives " <> box["word"] <> " with " <> box["newblock"] <> " appended."

SymbolicWordBlockDrop::usage =
box[SymbolicWordBlockDrop["word", "n"]] <> " gives " <> box["word"] <> " with its first " <> box["n"] <> " blocks dropped.\n" <>
box[SymbolicWordBlockDrop["word", -"n"]] <> " gives " <> box["word"] <> " with its last " <> box["n"] <> " blocks dropped."

SymbolicWordBlockTake::usage =
box[SymbolicWordBlockTake["word", "n"]] <> " gives a symbolic word containing the first " <> box["n"] <> " blocks of " <> box["word"] <> ".\n" <>
box[SymbolicWordBlockTake["word", -"n"]] <> " gives the last " <> box["n"] <> " blocks of " <> box["word"] <> "."

SymbolicWordCharacters::usage =
box[SymbolicWordCharacters["word"]] <> " gives a list of the characters in a symbolic word with integer block lengths."

SymbolicWordFactorList::usage =
box[SymbolicWordFactorList["word", "n", "assum"]] <> " gives a list of all symbolic factors of length " <> box["n"] <> " of an eventually periodic word.\n" <>
box[SymbolicWordFactorList["word", SubscriptList["n", {1, 2, "..."}], "assum"]] <> " gives a list of all symbolic factors of " <> box["word"] <> " where each factor is split into subfactors of lengths " <> box[SubscriptSequence["n", {1, 2, "..."}]] <> ".\n" <>
box[SymbolicWordFactorList["word", SubscriptList["n", {1, 2, "..."}]]] <> " uses default assumptions specified by any enclosing Assuming constructs."

SymbolicWordFirstBlockCharacter::usage =
box[SymbolicWordFirstBlockCharacter["word"]] <> " gives the character of the first block in " <> box["word"] <> "."

SymbolicWordFirstCharacter::usage =
box[SymbolicWordFirstCharacter["word", "assum"]] <> " gives the first character in " <> box["word"] <> ", taking into account blocks of length zero.\n" <>
box[SymbolicWordFirstCharacter["word"]] <> " uses default assumptions specified by any enclosing Assuming constructs."

SymbolicWordJoin::usage =
box[SymbolicWordJoin[SubscriptSequence["w", {1, 2, "..."}]]] <> " yields a symbolic word consisting of a concatenation of the " <> box[Subscript["w", "i"]] <> "."

SymbolicWordLength::usage =
box[SymbolicWordLength["word"]] <> " gives the number of characters in a symbolic word."

SymbolicWordPartitionAt::usage =
box[SymbolicWordPartitionAt["word", "n", "assum"]] <> " partitions an eventually periodic word into its prefix of length " <> box["n"] <> " and the remainder, using the assumptions " <> box["assum"] <> ".\n" <>
box[SymbolicWordPartitionAt["word", "n"]] <> " uses default assumptions specified by any enclosing Assuming constructs."

SymbolicWordPower::usage =
box[SymbolicWordPower["word", "n"]] <> " generates a symbolic word of " <> box["n"] <> " copies of " <> box["word"] <> "."

SymbolicWordQ::usage =
box[SymbolicWordQ["expr"]] <> " yields True if " <> box["expr"] <> " is a valid SymbolicWord object, and False otherwise."

SymbolicWordSimplified::usage =
box[SymbolicWordSimplified["word", "assum"]] <> " yields True if adjacent blocks in " <> box["word"] <> " have unequal characters and blocks in " <> box["word"] <> " have positive lengths under the assumptions " <> box["assum"] <> ".\n" <>
box[SymbolicWordSimplified["word"]] <> " uses default assumptions specified by any enclosing Assuming constructs."

SymbolicWordSimplify::usage =
box[SymbolicWordSimplify["word", "assum"]] <> " combines adjacent blocks in " <> box["word"] <> " having common characters and deletes each block whose symbolic length is equal to 0 under the assumptions " <> box["assum"] <> ".\n" <>
box[SymbolicWordSimplify["word"]] <> " uses default assumptions specified by any enclosing Assuming constructs."

SymbolicWordUnequal::usage =
box[SymbolicWordUnequal[Subscript["word", 1], Subscript["word", 2], "assum"]] <> " yields True if " <> box[Subscript["word", 1]] <> " and " <> box[Subscript["word", 2]] <> " can be shown to be unequal under the assumptions " <> box["assum"] <> ".\n" <>
box[SymbolicWordUnequal[SubscriptSequence["word", {1, 2}]]] <> " uses default assumptions specified by any enclosing Assuming constructs."

ToSymbolicWord::usage =
box[ToSymbolicWord["list"]] <> " gives a symbolic word representing " <> box["list"] <> " in its run\[Hyphen]length encoding."

TransientOnly::usage =
"TransientOnly is an option for SymbolicWordFactorList that specifies whether to only list symbolic factors beginning in the nonperiodic portion of the word."

$PowerFreeMorphismList::usage =
"$PowerFreeMorphismList is a list of 30 symbolic power\[Hyphen]free morphisms and associated data."


Monitor::abort = "Monitor breaks Abort and Catch in version " <> ToString[$VersionNumber] <> ".  Use version 11 or later for monitoring."


AssembleAssumptions[assumpts_] :=
	Replace[
		assumpts && $Assumptions,
		and_And :> DeleteDuplicates[and]
	]

ExtendedSymbolicWordQ[_?SymbolicWordQ] :=
	True
(* This doesn't check that the exponent is non-negative. *)
ExtendedSymbolicWordQ[SymbolicWordPower[_?ExtendedSymbolicWordQ, _]] :=
	True
ExtendedSymbolicWordQ[SymbolicWordJoin[__?ExtendedSymbolicWordQ]] :=
	True
ExtendedSymbolicWordQ[_] :=
	False

FactorLengthBound[_, rational_Rational, locatinglength_] :=
	StrictFloor[locatinglength/(Numerator[rational] - Denominator[rational])]
FactorLengthBound[a_/b_, {{intervalmin_, _}, ___}, locatinglength_] :=
Module[{acoefficient, bcoefficient},
	acoefficient = Coefficient[locatinglength, a];
	bcoefficient = Coefficient[locatinglength, b];
	StrictFloor[(acoefficient intervalmin + bcoefficient)/(intervalmin - 1)]
]

(* FirstBlockCharacterDrop drops  n  elements from the first block. *)
FirstBlockCharacterDrop[
	word_,
	0,
	_ : True
] :=
	word
FirstBlockCharacterDrop[
	word_,
	length_,
	assumptions_ : True
] :=
	SymbolicWordSimplify[MapAt[# - length &, word, {1, 2}], assumptions]
FirstBlockCharacterDrop[
	EventuallyPeriodicSymbolicWord[SymbolicWord[], period_],
	length_,
	assumptions_ : True
] :=
	FirstBlockCharacterDrop[EventuallyPeriodicSymbolicWord[period, period], length, assumptions]
FirstBlockCharacterDrop[
	EventuallyPeriodicSymbolicWord[prefix_, period_],
	length_,
	assumptions_ : True
] :=
	EventuallyPeriodicSymbolicWord[FirstBlockCharacterDrop[prefix, length, assumptions], period]

(* LocatingLengthQ assumes that  length  is a linear combination of  a  and  b . *)
LocatingLengthQ[n_, period_, a_Symbol/b_Symbol, length_, intervals_, nassumptions_, assumptions_, OptionsPattern[]] :=
Module[{obstructions, completedintervals, i, j},
	(* Test positivity.
	   Map over the intervals, since expressions such as
		Refine[2 a >= 1, Element[a | b, Integers] && (b < a < 3/2 b || 3/2 b < a < 2 b)]
	   doesn't evaluate to True. *)
	If[!TrueQ[And @@ (Refine[length >= 1, assumptions && First[#] b < a < Last[#] b] &) /@ intervals],
		Return[False]
	];
	If[TrueQ[OptionValue[Monitor]],
		PrintTemporary[
			"Determining whether the morphism locates words of length ", length,
			Tab,
			" (which if it does would require checking factors up to length ", FactorLengthBound[a/b, intervals, length] * a, ")"
		]
	];
	{obstructions, completedintervals} = SymbolicFactorTestObstructions[
		n,
		EventuallyPeriodicSymbolicWord[SymbolicWord[], period],
		a/b,
		length,
		intervals,
		Function[{nn, factorlist, nnassumptions, obstructionsfunctionassumption},
			(* Test that pairs of instances of different symbolic factors are unequal. *)
			Select[
				Subsets[factorlist, {2}],
				Function[{wordintervalpair1, wordintervalpair2},
					Module[{ncount = 0, index},
						!TrueQ[SymbolicWordUnequal[
							First[wordintervalpair1] /. nn :> Subscript[nn, ncount++],
							First[wordintervalpair2] /. nn :> Subscript[nn, ncount++] /. i -> j,
							And @@ Join[
								{Last[wordintervalpair1], Last[wordintervalpair2] /. i -> j, obstructionsfunctionassumption},
								Table[
									nnassumptions /. nn -> Subscript[nn, index],
									{index, 0, ncount - 1}
								]
							]
						]]
					]
				] @@ # &,
				1
			]
		],
		(* We have to pass these as separate arguments because if we put them inside obstructionsfunction then they don't evaluate. *)
		nassumptions,
		assumptions,
		GeneratedParameters -> i,
		Quiet -> True
	];
	If[obstructions === {} && TrueQ[OptionValue[Information]],
		Print["Locating length: ", length];
		Print["Interior endpoints for locating length verification: ", First /@ Rest[completedintervals]]
	];
	obstructions === {}
]
(* GeneratedParameters and LocatingLength are not actually used. *)
Options[LocatingLengthQ] = {GeneratedParameters -> C, Information -> False, LocatingLength -> Automatic, Monitor -> False}

(* This assumes that there aren't two adjacent blocks with the same character, like  Superscript[0,a-b]  followed by  Superscript[0,2b-a] . *)
MinFirstBlockLength[factor_List, assumptions_, options : OptionsPattern[]] :=
Module[{i},
	MinOrFail[
		Table[
			If[i < Length[factor] && Length[factor[[i]]] == 1 && SymbolicWordFirstBlockCharacter[factor[[i]]] === SymbolicWordFirstBlockCharacter[factor[[i + 1]]],
				(* This subfactor consists of a single block and the next subfactor begins with the same character, so this subfactor isn't the minimizing one. *)
				Infinity,
				SymbolicWordLength[SymbolicWordBlockTake[factor[[i]], 1]]
			],
			{i, 1, Length[factor]}
		],
		assumptions,
		options
	]
]
Options[MinFirstBlockLength] = {SowFailedMinExpressions -> False}

MinOrFail[list_List, assumptions_, OptionsPattern[]] :=
Module[{refined = Refine[Min[list], assumptions], failedmins},
	If[!MatchQ[refined, _Min],
		refined
		,
		failedmins = Cases[
			Refine[Min[#], assumptions] & /@ Subsets[DeleteDuplicates[list], {2}],
			_Min
		];
		(* Fail. *)
		If[TrueQ[OptionValue[SowFailedMinExpressions]],
			Sow[failedmins],
			(* When this message prints it looks a little messy since MinOrFail has context SymbolicWords`Private`. *)
			Message[
				MinOrFail::fail,
				Replace[
					failedmins,
					{
						{only_} :> only,
						longerlist_ :> Row[longerlist, ","]
					}
				]
			]
		];
		$Failed
	]
]
Options[MinOrFail] = {SowFailedMinExpressions -> False}
MinOrFail::fail = "Unable to determine `1`."
MinOrFail::pos = "One of the symbolic lengths `1` is non-positive."

RefineOrFail[booleanexpression_, assumptions_] :=
With[{refined = Refine[booleanexpression, assumptions]},
	If[MatchQ[refined, True | False],
		refined
		,
		(* When this message prints it looks a little messy since RefineOrFail has context SymbolicWords`Private`. *)
		Message[RefineOrFail::fail, booleanexpression];
		$Failed
	]
]
RefineOrFail::fail = "Unable to determine whether `1` is True or False."

StrictCeiling[x_] := Floor[x] + 1

StrictFloor[x_] := Ceiling[x] - 1

(* The real substance to SymbolicFactorTestObstructions is that it partitions an interval
   when it can't compute the symbolic factors of the required length on that interval. *)
SymbolicFactorTestObstructions[
	n_,
	periodicword_,
	a_/b_,
	subfactorlengths_,
	intervals : {__List},
	obstructionsfunction_,
	nassumptions_,
	assumptions_,
	OptionsPattern[]
] :=
Module[
	{
		totallength, pendingintervals = intervals, completedintervals = {}, newintervals, interval, obstructions = {}, newobstructions,
		factorlist, failedmins, newendpoints, interiorendpoints, applicableinteriorendpoints,
		i = OptionValue[GeneratedParameters], transientonly = OptionValue[TransientOnly], failed
	},
	totallength = Replace[subfactorlengths, list_List :> Expand[Total[list]]];
	failed = Catch[
		If[TrueQ[OptionValue[Monitor]] && 10 < $VersionNumber < 11,
			Message[Monitor::abort]
		];
		If[TrueQ[OptionValue[Monitor]] && !(10 < $VersionNumber < 11), Monitor, List][
			While[pendingintervals != {},
				interval = pendingintervals[[1,1]] b < a < pendingintervals[[1,2]] b;
				{factorlist, failedmins} = Reap[SymbolicWordFactorList[
					periodicword,
					subfactorlengths,
					Element[a | b, Integers] && interval,
					GeneratedParameters -> i,
					SowFailedMinExpressions -> True,
					TransientOnly -> transientonly
				]];
				(* MatchQ[factorlist, _SymbolicWordFactorList]  is equivalent to  failedmins != {} . *)
				If[failedmins == {},
					(* Apply the test on the interior of the interval. *)
					newobstructions = obstructionsfunction[
						n,
						factorlist,
						nassumptions,
						(* Probably  assumptions  has an interval assumption that is implied by  interval , so I could remove it. *)
						interval && assumptions
					];
					If[newobstructions != {},
						interval = (#/b &) /@ interval;
						newobstructions = Append[#, interval] & /@ newobstructions;
						obstructions = Join[obstructions, newobstructions];
						If[TrueQ[OptionValue[Monitor]],
							PrintTemporary[Style[Row[{"Obstructions found of length ", totallength, ": ", newobstructions}], Red]]
						]
					];
					completedintervals = Append[completedintervals, First[pendingintervals]];
					pendingintervals = Rest[pendingintervals]
					,
					(* Partition the current pending interval into new intervals. *)
					newintervals = Partition[
						Union[
							First[pendingintervals],
							Join @@ Function[min,
								(* For the interval 3/2 < a/b < 5/3 we run into  Min[a - b - 1, -4 a + 7 b] . *)
								Replace[
									(* This really assumes that the exponents in the morphism are linear combinations of  a  and  b ;
									   otherwise the equation passed to Solve below doesn't make much sense. *)
									Subtract @@ min /. a|b -> 0,
									{
										d : -1 | 0 | 1 :> (
											newendpoints = (a /. Solve[Subtract @@ min == d, a])/b;
											If[!MatchQ[newendpoints, {_Rational?(pendingintervals[[1,1]] < # < pendingintervals[[1,2]] &) ..}],
												If[!TrueQ[OptionValue[Quiet]],
													Message[SymbolicFactorTestObstructions::out, Equal @@ min, pendingintervals[[1,1]], pendingintervals[[1,2]]]
												];
												Throw[True]
											];
											newendpoints
										),
										_ :> (
											If[!TrueQ[OptionValue[Quiet]],
												Message[SymbolicFactorTestObstructions::rat, Equal @@ min]
											];
											Throw[True]
										)
									}
								]
							] /@ Join @@ First[failedmins]
						],
						2,
						1
					];
					pendingintervals = Join[newintervals, Rest[pendingintervals]]
				]
			],
			Column[{
				Row[{Tab, "Pending intervals: ", pendingintervals}],
				Row[{Tab, "Completed intervals: ", completedintervals}]
			}]
		];
		(* Compute symbolic factors for each subinterval endpoint. *)
		interiorendpoints = First /@ Rest[completedintervals];
		applicableinteriorendpoints = Select[interiorendpoints, (assumptions /. {a -> Numerator[#], b -> Denominator[#]}) =!= False &];
(* might want to keep this (commented) for easy access
If[Length[applicableinteriorendpoints] == Length[interiorendpoints],
	Print["Interior endpoints for factors of length ", totallength, ": ", interiorendpoints],
	Print["Interior endpoints for factors of length ", totallength, ": ", interiorendpoints, ";", Tab, "applicable: ", applicableinteriorendpoints]
];
*)
		(* Apply the test on each endpoint in the interior of the main interval. *)
		Function[interiorendpoint,
			factorlist = SymbolicWordFactorList[
				(* For intervals with no obstructions, we don't seem to need to delete empty blocks,
				   but for intervals that ultimately don't pan out for a morphism, we can get blocks with explicit length zero. *)
				SymbolicWordSimplify[periodicword /. {a -> Numerator[interiorendpoint], b -> Denominator[interiorendpoint]}],
				subfactorlengths /. {a -> Numerator[interiorendpoint], b -> Denominator[interiorendpoint]},
				GeneratedParameters -> i,
				TransientOnly -> transientonly
			];
			If[MatchQ[factorlist, _SymbolicWordFactorList],
				(* This might not ever occur, since all the block lengths should be refinable to explicit integers at this point.
				   If it does, it could issue a message if  !TrueQ[OptionValue[Quiet]] , but probably a message was already generated by SymbolicWordFactorList. *)
				Throw[True]
			];
			newobstructions = obstructionsfunction[
				n,
				factorlist,
				nassumptions,
				assumptions
			];
			If[newobstructions != {},
				newobstructions = Append[#, a/b == interiorendpoint] & /@ newobstructions;
				obstructions = Join[obstructions, newobstructions];
				If[TrueQ[OptionValue[Monitor]],
					PrintTemporary[Style[Row[{"Obstructions found of length ", totallength, ": ", newobstructions}], Red]]
				]
			]
		] /@ applicableinteriorendpoints;
		If[TrueQ[OptionValue[Last]] && TrueQ[OptionValue[Information]],
			Print["Interior endpoints for ", a/b, "\[Hyphen]power\[Hyphen]freeness verification: ", interiorendpoints];
			If[Length[applicableinteriorendpoints] != Length[interiorendpoints],
				Print[Tab, "applicable: ", applicableinteriorendpoints]
			]
		];
		False
	];
	If[failed,
		{$Failed, $Failed},
		{obstructions, completedintervals}
	]
]
Options[SymbolicFactorTestObstructions] = {GeneratedParameters -> C, Information -> False, Last -> False, Monitor -> False, Quiet -> False, TransientOnly -> False}
SymbolicFactorTestObstructions::out = "Endpoint obtained by solving `1` is not in the interval (`2`, `3`)."
SymbolicFactorTestObstructions::rat = "Endpoint obtained by solving `1` is not an explicit rational."


SyntaxInformation[EventuallyPeriodicSymbolicWord] = {"ArgumentsPattern" -> {_, _}}

(* This checks that the period word is not SymbolicWord[], but it doesn't check that the symbolic length is actually nonzero under the assumptions.
   That could lead to SymbolicWordLength erroneously yielding Infinity. *)
EventuallyPeriodicSymbolicWordQ[EventuallyPeriodicSymbolicWord[_?SymbolicWordQ, period_ /; SymbolicWordQ[period] && Length[period] >= 1]] := True
EventuallyPeriodicSymbolicWordQ[_] := False
SyntaxInformation[EventuallyPeriodicSymbolicWordQ] = {"ArgumentsPattern" -> {_}}

PowerFreeMorphismObstructions[
	HoldPattern[Pattern][n_Symbol, Blank[]] :> period_?SymbolicWordQ,
	rational_Rational /; 1 < rational < 2,
	assumpts : Except[_Rule] : True,
	OptionsPattern[]
] :=
Module[
	{
		a, b, assumptions, nassumptions, nmin, periodcharacters, periodlength, minimumlocatinglength, locatinglength, mmax,
		nmax, nvalues, positionlists, newletter, obstructions = {}, m, position, ncount, repeatedperiodcharacters, nsymbols, newobstruction, failed
	},
	assumptions = AssembleAssumptions[assumpts];
	nassumptions = Switch[assumptions,
		_And,
			Select[assumptions, !FreeQ[#, n] &],
		_,
			If[FreeQ[assumptions, n],
				True,
				assumptions
			]
	];
	nmin = Max[Cases[
		List @@ Replace[
			nassumptions,
			{
				_And :> List @@ nassumptions,
				_ :> {nassumptions}
			}
		],
		Alternatives[
			n >= bound_Integer,
			bound_Integer <= n,
			n == bound_Integer || (n >= higherbound_Integer | higherbound_Integer <= n) /; higherbound >= bound,
			(n >= higherbound_Integer | higherbound_Integer <= n) || n == bound_Integer /; higherbound >= bound
		] :> bound
	]];
	failed = Catch[

		(* Check input. *)
		If[!IntegerQ[nmin],
			Message[PowerFreeMorphismObstructions::nbound, n]; Throw[True]
		];
		If[!MatchQ[Select[List @@ period, !FreeQ[#, n] &], {} | {Superscript[_, 1]}],
			Message[PowerFreeMorphismObstructions::unique, period, n]; Throw[True]
		];
		(* Convert the symbolic word to a list, which can be operated on much more quickly. *)
		periodcharacters = SymbolicWordCharacters[period];
		If[MatchQ[periodcharacters, _SymbolicWordCharacters],
			Message[PowerFreeMorphismObstructions::expint, rational]; Throw[True]
		];
		periodlength = Length[periodcharacters];
		a = Numerator[rational];
		b = Denominator[rational];
		If[GCD[Denominator[rational], periodlength] != 1,
			Message[PowerFreeMorphismObstructions::assum, HoldForm[GCD][b, periodlength] == 1]; Throw[True]
		];

		(* Determine the maximum length factors we need to check.  This depends on the locating length.
		   So first we find an integer such that all factors of that length in the repeating period have a unique position.
		   For an explicit rational a/b, we can find the minimum locating length explictly, and then we don't need to verify it later. *)
		(* This is the largest value of n such that n + d is equal to one of the integer characters. *)
		nmax = Subtract[
			Max[Cases[periodcharacters, _Integer]],
			Replace[
				Max[Replace[
					DeleteCases[periodcharacters, _Integer],
					{n + shift_. :> shift, _ -> Infinity},
					{1}
				]],
				Infinity -> 0
			]
		];
		If[!IntegerQ[nmax],
			Message[PowerFreeMorphismObstructions::nbound, n]; Throw[True]
		];
		nvalues = Select[Range[nmin, nmax], Reduce[nassumptions && n == #, n] =!= False &];
		minimumlocatinglength = 1;
		positionlists = {Range[periodlength]};
		If[TrueQ[OptionValue[Monitor]] && 10 < $VersionNumber < 11,
			Message[Monitor::abort]
		];
		If[TrueQ[OptionValue[Monitor]] && !(10 < $VersionNumber < 11), Monitor, List][
			While[
				positionlists = Join @@ Function[positions,
					(* The words of length  length-1  in the period starting at  positions  are identical (for some values of n).
					   Determine which words are still identical when we extend by one letter. *)
					(* We don't need DeleteDuplicates here because n+d is the last letter of only one word for a given length. *)
					Map[
						First,
						DeleteCases[
							GatherBy[
								Join @@ ((
									newletter = periodcharacters[[Mod[# + minimumlocatinglength - 1, periodlength, 1]]];
									If[FreeQ[newletter, n],
										{{#, newletter}},
										Table[
											{#, newletter /. n -> m},
											{m, nvalues}
										]
									]
								) & /@ positions),
								Last
							],
							{_}
						],
						{2}
					]
				] /@ positionlists;
				positionlists != {} && minimumlocatinglength <= periodlength
				,
				minimumlocatinglength++
			],
			Row[{
				"Minimum locating length is at least ", minimumlocatinglength, "; ", Tab,
				Total[Length /@ positionlists], " positions (in ", Length[positionlists], " classes) still have non-unique words"
			}]
		];
		If[!IntegerQ[minimumlocatinglength] || minimumlocatinglength > periodlength,
			Message[PowerFreeMorphismObstructions::locate, a, b]; Throw[True]
		];
		locatinglength = OptionValue[LocatingLength];
		If[locatinglength =!= Automatic,
			If[
				!TrueQ[And[
					locatinglength >= minimumlocatinglength,
					(* Instead of testing
						FactorLengthBound[a/b, rational, locatinglength] <= mmaxbound
					   we can just test the following directly. *)
					Ceiling[(FactorLengthBound[a/b, rational, locatinglength] a - 1)/periodlength] + 1 <= a - 1
				]],
				locatinglength = $Failed
			]
			,
			(* Eliminate lengths that don't let us conclude that all factors we'll be examining are images (under the morphism) of words that are too short to contain an a/b-power.
			   Again we can just test the following directly instead of using  mmaxbound .
			   It may not actually eliminate anything. *)
			locatinglength = minimumlocatinglength;
			(* In practice, all the locating lengths end up being the minimal locating length.
			   Maybe it's possible to show that  minimumlocatinglength  passes the test; then we don't need this While loop.
			*)
			While[
				And[
					Ceiling[(FactorLengthBound[a/b, rational, locatinglength] a - 1)/periodlength] + 1 > a - 1,
					locatinglength <= periodlength
				],
				locatinglength++
			];
			If[locatinglength > periodlength,
				locatinglength = $Failed
			]
		];
		If[locatinglength === $Failed,
			Message[PowerFreeMorphismObstructions::locate, a, b]; Throw[True]
		];
		If[TrueQ[OptionValue[Information]],
			Print["Locating length: ", locatinglength]
		];
		mmax = FactorLengthBound[a/b, rational, locatinglength];
		If[TrueQ[OptionValue[Information]],
			Print["Max factor length to check: ", mmax * a]
		];

		(* Compute factors of each length in  Range[a, mmax * a, a]  and identify the a/b-powers.
		   Since the morphisms can be quite long, generate factors one at a time rather than all at once. *)
		ncount = 0;
		repeatedperiodcharacters = Join @@ ConstantArray[periodcharacters, Ceiling[(mmax a - 1)/periodlength] + 1] /. n :> Subscript[n, ncount++];
		nsymbols = Thread[Subscript[n, Range[0, ncount - 1]]];
		If[TrueQ[OptionValue[Monitor]] && 10 < $VersionNumber < 11,
			Message[Monitor::abort]
		];
		If[TrueQ[OptionValue[Monitor]] && !(10 < $VersionNumber < 11), Monitor, List][
			Quiet[
				obstructions = Reap[Do[
					Do[
						If[
							(* Test potential equality of first and third subfactors. *)
							MatchQ[
								Solve[
									Equal[
										Take[repeatedperiodcharacters, {position, position + m (a - b) - 1}],
										Take[repeatedperiodcharacters, {position + m b, position + m a - 1}]
									],
									nsymbols
								],
								{___, {(_ -> integer_Integer /; (nassumptions /. n -> integer) =!= False) ...}, ___}
							],
							newobstruction = {
								Take[repeatedperiodcharacters, {position, position + m (a - b) - 1}],
								Take[repeatedperiodcharacters, {position + m (a - b), position + m b - 1}],
								Take[repeatedperiodcharacters, {position + m b, position + m a - 1}]
							} /. Subscript[n, _] -> n;
							Sow[newobstruction];
							If[TrueQ[OptionValue[Monitor]],
								PrintTemporary[Style[Row[{"Obstruction found of length ", m * a, ": ", newobstruction}], Red]]
							]
						]
						,
						{position, 1, periodlength}
					]
					,
					{m, 1, mmax}
				]][[2]],
				Solve::svars
			],
			Row[{"Computing and checking factors of length ", m * a, " (out of ", mmax * a, ")"}]
		];

		False

	];
	If[obstructions =!= {}, obstructions = First[obstructions]];
	obstructions /; !failed
]
PowerFreeMorphismObstructions[
	HoldPattern[Pattern][n_Symbol, Blank[]] :> period_?SymbolicWordQ,
	a_Symbol/b_Symbol,
	assumpts : Except[_Rule] : True,
	options : OptionsPattern[]
] :=
Module[
	{
		assumptions, nassumptions, intervals, periodlength, locatinglength,
		acoefficient, lengthlist, mmax, mmaxbound, obstructions, repeatedfactorlengths, m, c, d, blockcount, minnumerator, failed
	},
	assumptions = AssembleAssumptions[assumpts];
	(* Refine (in MinOrFail) works much better when we move the symbolic denominator to the other sides.
	   (This assumes  b > 0  without the user indicating so.) *)
	assumptions = assumptions /. (Imin_ < a/b < Imax_) :> (Imin b < a < Imax b);
	nassumptions = Switch[assumptions,
		_And,
			Select[assumptions, !FreeQ[#, n] &],
		_,
			If[FreeQ[assumptions, n],
				True,
				assumptions
			]
	];
	failed = Catch[

		(* Check input. *)
		If[TrueQ[nassumptions],
			(* We don't Throw[ ] here because this problem is potentially non-fatal. *)
			Message[PowerFreeMorphismObstructions::nbound, n]
		];
		If[!TrueQ[Refine[Element[a | b, Integers], assumpts]],
			Message[PowerFreeMorphismObstructions::assum, Element[a | b, Integers]]; Throw[True]
		];
		If[!TrueQ[Refine[GCD[a, b] == 1, assumpts]],
			Message[PowerFreeMorphismObstructions::assum, GCD[a, b] == 1]; Throw[True]
		];
		(* Extract intervals for a/b from the assumptions. *)
		intervals = Refine[
			Reduce[
				Select[
					assumptions,
					And[
						!MatchQ[#, _Element],
						FreeQ[#, HoldPattern[GCD][___, a | b, ___]],
						!FreeQ[#, a | b]
					] &
				]
			],
			(* This assumes  b > 0  without the user indicating so. *)
			a > 0 && b > 0
		];
		intervals = Switch[intervals,
			_Or, List @@ intervals,
			_, {intervals}
		];
		(* Reduce produces intervals of the form  a/Imax < b < a/Imin , which we need to rewrite as  Imin b < a < Imax b . *)
		intervals = Replace[
			intervals,
			(* The inequalities have head Inequality, but for insurance we also replace the equivalent Less expressions. *)
			{
				Inequality[maxreciprocal_. a, Less, b, Less, minreciprocal_. a] :>
					{1/minreciprocal, 1/maxreciprocal},
				maxreciprocal_. a < b < minreciprocal_. a :>
					{1/minreciprocal, 1/maxreciprocal},
				(* It's conceivable that the inequalities are already written correctly. *)
				Inequality[Imin_. b, Less, a, Less, Imax_. b] :>
					{Imin, Imax},
				(Imin_. b < a < Imax_. b) :>
					{Imin, Imax},
				_ ->
					$Failed
			},
			{1}
		];
		intervals = Sort[intervals];
		If[MemberQ[intervals, $Failed] || !And @@ (1 < First[#] < 2 && 1 < Last[#] <= 2 &) /@ intervals,
			Message[PowerFreeMorphismObstructions::interval, a/b]; Throw[True]
		];
		If[!MatchQ[Select[List @@ period, !FreeQ[#, n] &], {} | {Superscript[_, 1]}],
			Message[PowerFreeMorphismObstructions::unique, period, n]; Throw[True]
		];
		periodlength = SymbolicWordLength[period];
		acoefficient = Abs[Coefficient[periodlength, a]];
		(* Check that  GCD[b, periodlength] == 1 , either indirectly or directly. *)
		If[
			!Or[
				And[
					MatchQ[MonomialList[periodlength], {(a | b | _Integer (a | b)) ..}],
					acoefficient == 1 || TrueQ[Refine[GCD[b, acoefficient] == 1, assumpts]]
				],
				TrueQ[Refine[GCD[b, periodlength] == 1, assumpts]]
			],
			Message[PowerFreeMorphismObstructions::assum, GCD[b, periodlength] == 1]; Throw[True]
		];

		(* Determine the maximum length factors we need to check.  This depends on the locating length.
		   So first we find an integer such that all factors of that length in the repeating period have a unique position. *)
		locatinglength = OptionValue[LocatingLength];
		If[locatinglength =!= Automatic,
			lengthlist = {locatinglength}
			,
			(* For symbolic a/b, generate linear combinations of a,b systematically.  The upper bound 10 is somewhat arbitrary but works well. *)
			lengthlist = Join @@ Table[c a - d b, {c, 1, 10}, {d, 0, c}];
			(* Eliminate lengths of factors that obviously appear in more than one position. *)
			repeatedfactorlengths = Union @@ Table[
				DeleteDuplicates[Cases[
					Tally[SymbolicWord @@@ Partition[List @@ period, blockcount, 2]],
					{factor_, count_ /; count >= 2} :> SymbolicWordLength[factor]
				]],
				{blockcount, 2, Length[period], 2}
			];
			lengthlist = DeleteCases[
				lengthlist,
				Alternatives @@ repeatedfactorlengths
			];
			lengthlist = ({#, FactorLengthBound[a/b, intervals, #]} &) /@ lengthlist;
			(* Find the smallest integer that is the numerator of a rational number satisfying the assumptions. *)
			minnumerator = 3;
			While[
				Select[
					Join @@ (Range[StrictCeiling[minnumerator/Last[#]], StrictFloor[minnumerator/First[#]]] &) /@ intervals,
					GCD[#, acoefficient] == 1 &
				] == {},
				minnumerator++
			];
			(* Eliminate lengths that don't let us conclude that all factors we'll be examining are images (under the morphism) of words that are too short to contain an a/b-power. *)
			mmaxbound = (Coefficient[periodlength, a] + Coefficient[periodlength, b]/intervals[[1,1]]) (minnumerator - 2);
			lengthlist = Select[lengthlist, Last[#] <= mmaxbound &];
			lengthlist = First /@ SortBy[
				lengthlist,
				(* In case of a tie, retain the current order. *)
				{Last}
			]
		];
		lengthlist = Select[
			lengthlist,
			LocatingLengthQ[n, period, a/b, #, intervals, nassumptions, assumptions, options] &,
			1
		];
		If[Length[lengthlist] >= 1,
			locatinglength = First[lengthlist],
			Message[PowerFreeMorphismObstructions::locate, a, b]; Throw[True]
		];
		mmax = FactorLengthBound[a/b, intervals, locatinglength];
		If[TrueQ[OptionValue[Information]],
			Print["Max factor length to check: ", mmax * a]
		];

		(* Compute symbolic factors of each length in  Range[a, mmax * a, a]  and identify the a/b-powers. *)
		If[TrueQ[OptionValue[Monitor]] && 10 < $VersionNumber < 11,
			Message[Monitor::abort]
		];
		If[TrueQ[OptionValue[Monitor]] && !(10 < $VersionNumber < 11), Monitor, List][
			obstructions = Join @@ Table[
				(* Compute symbolic factors for each subinterval on which all inequalities that we run into can be resolved. *)
				{obstructions, intervals} = SymbolicFactorTestObstructions[
					n,
					EventuallyPeriodicSymbolicWord[SymbolicWord[], period],
					a/b,
					m {a - b, 2 b - a, a - b},
					(* Inherit the intervals determined for the previous factor length. *)
					intervals,
					Function[{nn, factorlist, nnassumptions, obstructionsfunctionassumption},
						Select[
							factorlist,
							Function[{subfactorlist, lessequal},
								Module[{ncount = 0, index},
									(* Test potential equality of first and third subfactors. *)
									!TrueQ[(*(If[!TrueQ[#],Print[subfactorlist, Tab, Style[#,Pink]]];#)&@*)SymbolicWordUnequal[
										subfactorlist[[1]] /. nn :> Subscript[nn, ncount++],
										subfactorlist[[3]] /. nn :> Subscript[nn, ncount++],
										And @@ Join[
											{lessequal, obstructionsfunctionassumption},
											Table[
												nnassumptions /. nn -> Subscript[nn, index],
												{index, 0, ncount - 1}
											]
										]
									]]
								]
							] @@ # &
						]
					],
					(* We have to pass these as separate arguments because if we put them inside obstructionsfunction then they don't evaluate. *)
					nassumptions,
					assumptions,
					Last -> m == mmax,
					Sequence @@ DeleteCases[{options}, LocatingLength -> _]
				];
				If[obstructions === $Failed, Throw[True]];
				obstructions
				,
				{m, 1, mmax}
			],
			Row[{"Computing and checking factors of length ", m * a, " (out of ", mmax * a, ")"}]
		];

		False

	];
	obstructions /; !failed
]
Options[PowerFreeMorphismObstructions] = {GeneratedParameters -> C, Information -> False, LocatingLength -> Automatic, Monitor -> False}
SyntaxInformation[PowerFreeMorphismObstructions] = {"ArgumentsPattern" -> {_, _, OptionsPattern[]}}
PowerFreeMorphismObstructions::assum = "Assumptions don't imply `1`."
PowerFreeMorphismObstructions::expint = "For an explicit rational `1`, the morphism run lengths are expected to be positive integers."
PowerFreeMorphismObstructions::interval = "Assumptions don't confine `1` to open subintervals of (1,2]."
PowerFreeMorphismObstructions::locate = "Unable to find a locating length of the form c `1` - d `2` with c \[GreaterEqual] d \[GreaterEqual] 0 for the morphism."
PowerFreeMorphismObstructions::nbound = "Assumptions don't provide a bound on `1`."
PowerFreeMorphismObstructions::unique = "Morphism image `1` contains more than one character which depends on `2`."

PowerFreeWordTransientObstructions[
	EventuallyPeriodicSymbolicWord[prefix_, period_]?EventuallyPeriodicSymbolicWordQ,
	rational_Rational /; 1 < rational < 2,
	n_Symbol,
	assumpts : Except[_Rule] : True,
	OptionsPattern[]
] :=
Module[
	{
		a, b, assumptions, nassumptions, nmin, prefixcharacters, periodcharacters, prefixlength, periodlength, commonsuffixlength, minimumlocatinglength, mmax,
		nmax, nvalues, positionlists, newletter, obstructions = {}, m, position, ncount, prefixperiodcharacters, nsymbols, powerfreeprefixlength, newobstruction, failed
	},
	assumptions = AssembleAssumptions[assumpts];
	nassumptions = Switch[assumptions,
		_And,
			Select[assumptions, !FreeQ[#, n] &],
		_,
			If[FreeQ[assumptions, n],
				True,
				assumptions
			]
	];
	nmin = Max[Cases[
		List @@ Replace[
			nassumptions,
			{
				_And :> List @@ nassumptions,
				_ :> {nassumptions}
			}
		],
		Alternatives[
			n >= bound_Integer,
			bound_Integer <= n,
			n == bound_Integer || (n >= higherbound_Integer | higherbound_Integer <= n) /; higherbound >= bound,
			(n >= higherbound_Integer | higherbound_Integer <= n) || n == bound_Integer /; higherbound >= bound
		] :> bound
	]];
	failed = Catch[

		(* Check input. *)
		If[!IntegerQ[nmin],
			Message[PowerFreeWordTransientObstructions::nbound, n]; Throw[True]
		];
		If[!MatchQ[Select[List @@ period, !FreeQ[#, n] &], {} | {Superscript[_, 1]}],
			Message[PowerFreeWordTransientObstructions::unique, period, n]; Throw[True]
		];
		(* Convert the symbolic words to lists, which can be operated on much more quickly. *)
		prefixcharacters = SymbolicWordCharacters[prefix];
		periodcharacters = SymbolicWordCharacters[period];
		If[MatchQ[prefixcharacters, _SymbolicWordCharacters] || MatchQ[periodcharacters, _SymbolicWordCharacters],
			Message[PowerFreeWordTransientObstructions::expint, rational]; Throw[True]
		];
		prefixlength = Length[prefixcharacters];
		If[prefixlength == 0,
			Message[PowerFreeWordTransientObstructions::empty]; Throw[True]
		];
		periodlength = Length[periodcharacters];
		commonsuffixlength = 0;
		While[
			And[
				commonsuffixlength + 1 <= prefixlength,
				!TrueQ[Refine[prefixcharacters[[-(commonsuffixlength + 1)]] != periodcharacters[[-Mod[commonsuffixlength + 1, periodlength, 1]]], assumptions]]
			],
			commonsuffixlength++
		];
		a = Numerator[rational];
		b = Denominator[rational];

		(* Determine the maximum length factors we need to check.  This depends on the lengths of uniquely occuring factors.
		   So first we find a factor beginning at each position (of the prefix with the common suffix removed) that only occurs once.
		   This is almost equivalent to computing the locating length for factors overlapping the prefix + first period. *)
		(* The period may have an instance of symbolic n.  The actual infinite word we're concerned with has specific values for each of these n's, but
		   PowerFreeWordTransientObstructions just takes the symbolic word, not a morphism, so we can't necessarily tell what the values are. *)
		(* This is the largest value of n such that n + d is equal to one of the integer characters. *)
		nmax = Subtract[
			Max[Cases[Join[prefixcharacters, periodcharacters], _Integer]],
			Replace[
				Max[Replace[
					DeleteCases[Join[prefixcharacters, periodcharacters], _Integer],
					{n + shift_. :> shift, _ -> Infinity},
					{1}
				]],
				Infinity -> 0
			]
		];
		If[!IntegerQ[nmax],
			Message[PowerFreeWordTransientObstructions::nbound, n]; Throw[True]
		];
		nvalues = Select[Range[nmin, nmax], Reduce[nassumptions && n == #, n] =!= False &];
		minimumlocatinglength = 1;
		(* Positions in  Range[prefixlength]  represent only those positions, but positions in  Range[prefixlength + 1, prefixlength + periodlength]
		   are just representatives of general positions (modulo  Length[periodlength] ) in the rest of the infinite word. *)
		positionlists = {Range[prefixlength + periodlength]};
		If[TrueQ[OptionValue[Monitor]] && 10 < $VersionNumber < 11,
			Message[Monitor::abort]
		];
		If[TrueQ[OptionValue[Monitor]] && !(10 < $VersionNumber < 11), Monitor, List][
			While[
				positionlists = Join @@ Function[positions,
					(* The words of length  length-1  in the period starting at  positions  are identical (for some values of n).
					   Determine which words are still identical when we extend by one letter. *)
					DeleteCases[
						(* If the last letter in multiple words is n+d, then multiple copies get created.  So we delete duplicates. *)
						DeleteDuplicates[Map[
							First,
							GatherBy[
								Join @@ ((
									newletter = If[# + minimumlocatinglength - 1 <= prefixlength,
										prefixcharacters[[# + minimumlocatinglength - 1]],
										periodcharacters[[Mod[# + minimumlocatinglength - 1 - prefixlength, periodlength, 1]]]
									];
									If[FreeQ[newletter, n],
										{{#, newletter}},
										Table[
											{#, newletter /. n -> m},
											{m, nvalues}
										]
									]
								) & /@ positions),
								Last
							],
							{2}
						]],
						(* Delete lists of positions that can't correspond to a/b-powers. *)
						Alternatives[
							(* A one-element list corresponds to a uniquely-occurring factor. *)
							{_},
							(* We're only concerned with factors beginning in the prefix (and earlier than the common suffix). *)
							{_?(# >= prefixlength - commonsuffixlength + 1 &), __}
						]
					]
				] /@ positionlists;
				positionlists != {} && minimumlocatinglength <= prefixlength
				,
				minimumlocatinglength++
			],
			Row[{
				"Minimum locating length for factors overlapping the prefix is at least ", minimumlocatinglength, "; ", Tab,
				Total[Length /@ positionlists], " positions (in ", Length[positionlists], " classes) still have non-unique words"
			}]
		];
		If[!IntegerQ[minimumlocatinglength] || minimumlocatinglength > prefixlength,
			Message[PowerFreeWordTransientObstructions::locate]; Throw[True]
		];
		If[TrueQ[OptionValue[Information]],
			Print["Minimum locating length for factors overlapping the prefix: ", minimumlocatinglength]
		];
		If[
			And[
				commonsuffixlength != 0,
				!And[
					(* Check that the period isn't composed of a single letter. *)
					Or @@ Table[!TrueQ[Refine[Equal @@ (periodcharacters /. n -> m)]], {m, nvalues}],
					(* Check that we don't need to increase  minimumlocatinglength  to take care of positions in the common suffix.
					   It suffices to use repetitions in the period to identify a factor (with length at most  minimumlocatinglength ) that does not re-occur. *)
					minimumlocatinglength >= commonsuffixlength + Times[
						periodlength,
						1 + Max[Table[
							Length /@ Rest[Split[Join[prefixcharacters, periodcharacters, periodcharacters] /. n -> m]],
							{m, nvalues}
						]]
					]
				]
			],
			Message[PowerFreeWordTransientObstructions::cmnsfx, commonsuffixlength]
		];
		mmax = Ceiling[minimumlocatinglength/(a - b)] - 1;
		If[TrueQ[OptionValue[Information]],
			Print["Max factor length to check: ", mmax * a]
		];

		(* Compute factors of each length in  Range[a, mmax * a, a]  and identify the a/b-powers.
		   Since the morphisms can be quite long, generate factors one at a time rather than all at once. *)
		ncount = 0;
		prefixperiodcharacters = Join[
			prefixcharacters,
			Join @@ ConstantArray[periodcharacters, Ceiling[(mmax a - 1)/periodlength]]
		] /. n :> Subscript[n, ncount++];
		nsymbols = Thread[Subscript[n, Range[0, ncount - 1]]];
		(* If  position + m a - 1 <= (length of the prefix we computed) , then we already know there's no a/b-power there. *)
		powerfreeprefixlength = Replace[OptionValue[PowerFreePrefixLength], Except[_Integer?Positive] -> -Infinity];
		If[TrueQ[OptionValue[Monitor]] && !(10 < $VersionNumber < 11), Monitor, List][
			Quiet[
				obstructions = Reap[Do[
					Do[
						If[
							(* Test potential equality of first and third subfactors. *)
							MatchQ[
								Solve[
									Equal[
										Take[prefixperiodcharacters, {position, position + m (a - b) - 1}],
										Take[prefixperiodcharacters, {position + m b, position + m a - 1}]
									],
									nsymbols
								],
								{___, {(_ -> integer_Integer /; (nassumptions /. n -> integer) =!= False) ...}, ___}
							],
							newobstruction = {
								Take[prefixperiodcharacters, {position, position + m (a - b) - 1}],
								Take[prefixperiodcharacters, {position + m (a - b), position + m b - 1}],
								Take[prefixperiodcharacters, {position + m b, position + m a - 1}]
							} /. Subscript[n, _] -> n;
							Sow[newobstruction];
							If[TrueQ[OptionValue[Monitor]],
								PrintTemporary[Style[Row[{"Obstruction found of length ", m * a, ": ", newobstruction}], Red]]
							]
						]
						,
						{position, Max[powerfreeprefixlength - m a + 2, 1], prefixlength}
					]
					,
					{m, 1, mmax}
				]][[2]],
				Solve::svars
			],
			Row[{"Computing and checking factors of length ", m * a, " (out of ", mmax * a, ")"}]
		];

		False

	];
	If[obstructions =!= {}, obstructions = First[obstructions]];
	obstructions /; !failed
]
PowerFreeWordTransientObstructions[
	EventuallyPeriodicSymbolicWord[prefix_, period_]?EventuallyPeriodicSymbolicWordQ,
	a_Symbol/b_Symbol,
	n_Symbol,
	assumpts : Except[_Rule] : True,
	options : OptionsPattern[]
] :=
Module[{assumptions, nassumptions, intervals, lastprefixcharacter, blockcount, candidatefactor, mmax, obstructions, m, failed},
	assumptions = AssembleAssumptions[assumpts];
	(* Refine (in MinOrFail) works much better when we move the symbolic denominator to the other sides.
	   (This assumes  b > 0  without the user indicating so.) *)
	assumptions = assumptions /. (Imin_ < a/b < Imax_) :> (Imin b < a < Imax b);
	nassumptions = Switch[assumptions,
		_And,
			Select[assumptions, !FreeQ[#, n] &],
		_,
			If[FreeQ[assumptions, n],
				True,
				assumptions
			]
	];
	failed = Catch[

		(* Check input. *)
		If[TrueQ[nassumptions],
			(* We don't Throw[ ] here because this problem is potentially non-fatal. *)
			Message[PowerFreeWordTransientObstructions::nbound, n]
		];
		If[!TrueQ[Refine[Element[a | b, Integers], assumpts]],
			Message[PowerFreeWordTransientObstructions::assum, Element[a | b, Integers]]; Throw[True]
		];
		If[!TrueQ[Refine[GCD[a, b] == 1, assumpts]],
			Message[PowerFreeWordTransientObstructions::assum, GCD[a, b] == 1]; Throw[True]
		];
		(* Extract intervals for a/b from the assumptions. *)
		intervals = Refine[
			Reduce[
				Select[
					assumptions,
					And[
						!MatchQ[#, _Element],
						FreeQ[#, HoldPattern[GCD][___, a | b, ___]],
						!FreeQ[#, a | b]
					] &
				]
			],
			(* This assumes  b > 0  without the user indicating so. *)
			a > 0 && b > 0
		];
		intervals = Switch[intervals,
			_Or, List @@ intervals,
			_, {intervals}
		];
		(* Reduce produces intervals of the form  a/Imax < b < a/Imin , which we need to rewrite as  Imin b < a < Imax b . *)
		intervals = Replace[
			intervals,
			(* The inequalities have head Inequality, but for insurance we also replace the equivalent Less expressions. *)
			{
				Inequality[maxreciprocal_. a, Less, b, Less, minreciprocal_. a] :>
					{1/minreciprocal, 1/maxreciprocal},
				maxreciprocal_. a < b < minreciprocal_. a :>
					{1/minreciprocal, 1/maxreciprocal},
				(* It's conceivable that the inequalities are already written correctly. *)
				Inequality[Imin_. b, Less, a, Less, Imax_. b] :>
					{Imin, Imax},
				(Imin_. b < a < Imax_. b) :>
					{Imin, Imax},
				_ ->
					$Failed
			},
			{1}
		];
		intervals = Sort[intervals];
		If[MemberQ[intervals, $Failed] || !And @@ (1 < First[#] < 2 && 1 < Last[#] <= 2 &) /@ intervals,
			Message[PowerFreeWordTransientObstructions::interval, a/b]; Throw[True]
		];
		If[!MatchQ[Select[List @@ period, !FreeQ[#, n] &], {} | {Superscript[_, 1]}],
			Message[PowerFreeWordTransientObstructions::unique, period, n]; Throw[True]
		];
		lastprefixcharacter = SymbolicWordFirstCharacter[Reverse[prefix]];
		(* Test that the last character of the prefix is nonzero. *)
		If[MatchQ[lastprefixcharacter, _SymbolicWordFirstCharacter] || !TrueQ[Refine[lastprefixcharacter != 0, assumptions]],
			Message[PowerFreeWordTransientObstructions::prefix, prefix]; Throw[True]
		];
		(* Test that the last character of the prefix is unequal to the last character of the period. *)
		If[!TrueQ[Refine[lastprefixcharacter != SymbolicWordFirstCharacter[Reverse[period]], assumptions]],
			Message[PowerFreeWordTransientObstructions::last, lastprefixcharacter, SymbolicWordFirstCharacter[Reverse[period]]]; Throw[True]
		];
		(* Test that sliding a window of constant block length through the period will retain block alignment.
		   (The real issue is that when we're comparing two blocks of zeros, they should be maximal blocks so that one can't be a subfactor of the other.)
		   It's sufficient that the period alternates between 0 blocks and single-letter nonzero blocks. *)
		If[
			!And[
				EvenQ[Length[period]],
				MatchQ[
					Partition[List @@ period, 2],
					{
						{
							Superscript[0, _],
							Superscript[_?(TrueQ[Refine[# != 0, assumptions]] &), 1]
						} ..
					}
				]
			],
			Message[PowerFreeWordTransientObstructions::period, period]; Throw[True]
		];

		(* Determine the maximum length factors we need to check.  This depends on the length of a uniquely occuring factor.
		   So first we find a factor that only occurs once.  This factor is of the form (final letter of the prefix) (some prefix of the period). *)
		blockcount = 2;
		While[
			And[
				blockcount <= Length[period]
				,
				candidatefactor = SymbolicWordJoin[SymbolicWord[Superscript[lastprefixcharacter, 1]], SymbolicWordBlockTake[period, blockcount]];
				Select[
					SymbolicWord @@@ Partition[List @@ period, Length[candidatefactor], 1, 1],
					!TrueQ[SymbolicWordUnequal[candidatefactor, #, assumptions]] &,
					1
				] != {}
			],
			blockcount += 2
		];
		If[blockcount > Length[period],
			Message[PowerFreeWordTransientObstructions::factor, SymbolicWordLength[prefix]]; Throw[True]
		];
		mmax = 0;
		While[!TrueQ[Refine[SymbolicWordLength[prefix] + SymbolicWordLength[candidatefactor] - 1 <= (mmax + 1) (a - b), assumptions]],
			mmax++
		];
		If[TrueQ[OptionValue[Information]],
			Print["Max factor length to check: ", mmax * a]
		];

		(* Compute symbolic factors of each length in  Range[a, mmax * a, a]  and identify the a/b-powers. *)
		If[TrueQ[OptionValue[Monitor]] && 10 < $VersionNumber < 11,
			Message[Monitor::abort]
		];
		If[TrueQ[OptionValue[Monitor]] && !(10 < $VersionNumber < 11), Monitor, List][
			obstructions = Join @@ Table[
				(* Compute symbolic factors for each subinterval on which all inequalities that we run into can be resolved. *)
				{obstructions, intervals} = SymbolicFactorTestObstructions[
					n,
					EventuallyPeriodicSymbolicWord[prefix, period],
					a/b,
					m {a - b, 2 b - a, a - b},
					(* Inherit the intervals determined for the previous factor length. *)
					intervals,
					Function[{nn, factorlist, nnassumptions, obstructionsfunctionassumption},
						Select[
							factorlist,
							Function[{subfactorlist, lessequal},
								Module[{ncount = 0, index},
									(* Test potential equality of first and third subfactors. *)
									!TrueQ[SymbolicWordUnequal[
										subfactorlist[[1]] /. nn :> Subscript[nn, ncount++],
										subfactorlist[[3]] /. nn :> Subscript[nn, ncount++],
										And @@ Join[
											{lessequal, obstructionsfunctionassumption},
											Table[
												nnassumptions /. nn -> Subscript[nn, index],
												{index, 0, ncount - 1}
											]
										]
									]]
								]
							] @@ # &
						]
					],
					(* We have to pass these as separate arguments because if we put them inside obstructionsfunction then they don't evaluate. *)
					nassumptions,
					assumptions,
					Last -> m == mmax,
					TransientOnly -> True,
					options
				];
				If[obstructions === $Failed, Throw[True]];
				obstructions
				,
				{m, 1, mmax}
			],
			Row[{"Computing and checking factors of length ", m * a, " (out of ", mmax * a, ")"}]
		];

		False

	];
	obstructions /; !failed
]
Options[PowerFreeWordTransientObstructions] = {PowerFreePrefixLength -> 0, GeneratedParameters -> C, Information -> False, Monitor -> False}
SyntaxInformation[PowerFreeWordTransientObstructions] = {"ArgumentsPattern" -> {_, _, OptionsPattern[]}}
PowerFreeWordTransientObstructions::assum = "Assumptions don't imply `1`."
PowerFreeWordTransientObstructions::cmnsfx = "Factors beginning in last `1` positions of the prefix will not be checked."
PowerFreeWordTransientObstructions::empty = "Empty prefix detected."
PowerFreeWordTransientObstructions::expint = "For an explicit rational `1`, the morphism run lengths are expected to be positive integers."
PowerFreeWordTransientObstructions::factor = "Unable to find a uniquely-occurring factor beginning at position `1`."
PowerFreeWordTransientObstructions::interval = "Assumptions don't confine `1` to open subintervals of (1,2]."
PowerFreeWordTransientObstructions::last = "Unable to determine that the last letters `1` and `2` of the prefix and period are unequal. Try rotating the period."
PowerFreeWordTransientObstructions::locate = "Unable to find a length that uniquely locates all factors overlapping the prefix."
PowerFreeWordTransientObstructions::nbound = "Assumptions don't provide a bound on `1`."
PowerFreeWordTransientObstructions::period = "Period `1` does not alternate between 0 blocks and nonzero blocks."
PowerFreeWordTransientObstructions::prefix = "Unable to determine that the prefix `1` ends in a nonzero character."
PowerFreeWordTransientObstructions::unique = "Morphism image `1` contains more than one character which depends on `2`."

SyntaxInformation[SymbolicWord] = {"ArgumentsPattern" -> {___}}

SymbolicWordAppend[word_?SymbolicWordQ, newblock : Superscript[_, _]] :=
	SymbolicWordJoin[word, SymbolicWord[newblock]]
SyntaxInformation[SymbolicWordAppend] = {"ArgumentsPattern" -> {_, _}}

SymbolicWordBlockDrop[word_?SymbolicWordQ, blockcount_Integer] /; Length[word] >= Abs[blockcount] :=
	Drop[word, blockcount]
SymbolicWordBlockDrop[EventuallyPeriodicSymbolicWord[prefix_, period_] ? EventuallyPeriodicSymbolicWordQ, blockcount_Integer?NonNegative] :=
	If[Length[prefix] >= blockcount,
		EventuallyPeriodicSymbolicWord[SymbolicWordBlockDrop[prefix, blockcount], period],
		EventuallyPeriodicSymbolicWord[
			If[Divisible[blockcount - Length[prefix], Length[period]],
				SymbolicWord[],
				SymbolicWordBlockDrop[period, Mod[blockcount - Length[prefix], Length[period]]]
			],
			period
		]
	]
SyntaxInformation[SymbolicWordBlockDrop] = {"ArgumentsPattern" -> {_, _}}

SymbolicWordBlockTake[word_?SymbolicWordQ, blockcount_Integer] /; Length[word] >= Abs[blockcount] :=
	Take[word, blockcount]
SymbolicWordBlockTake[EventuallyPeriodicSymbolicWord[prefix_, period_] ? EventuallyPeriodicSymbolicWordQ, blockcount_Integer?NonNegative] :=
	If[Length[prefix] >= blockcount,
		SymbolicWordBlockTake[prefix, blockcount],
		(* This can merge blocks, which may be desirable sometimes but not others. *)
		SymbolicWordJoin @@ Join[
			{prefix},
			ConstantArray[period, Floor[(blockcount - Length[prefix]) / Length[period]]],
			{SymbolicWordBlockTake[period, Mod[blockcount - Length[prefix], Length[period]]]}
		]
	]
SymbolicWordBlockTake[periodicword_?EventuallyPeriodicSymbolicWordQ, Infinity] :=
	periodicword
SyntaxInformation[SymbolicWordBlockTake] = {"ArgumentsPattern" -> {_, _}}

SymbolicWordCharacters[word : SymbolicWord[Superscript[_, _Integer?NonNegative] ...]] :=
	Join @@ ConstantArray @@@ List @@ word
SyntaxInformation[SymbolicWordCharacters] = {"ArgumentsPattern" -> {_}}

(* TODO Ideally there would also be a version of SymbolicWordFactorList for finite words. *)
SymbolicWordFactorList[
	initialqueue_?EventuallyPeriodicSymbolicWordQ,
	unexpandedlengths : {Except[_List] ..},
	assumptions : Except[_Rule] : True,
	OptionsPattern[]
] :=
Module[{factorlist = {}, lengths, queue, factor, intervalmax, i, failed, sowq = OptionValue[SowFailedMinExpressions], subfactorlength, firstcharacter},
	failed = Catch[
		lengths = Expand[unexpandedlengths];
		(* Mark the first character in the period with a wrapper so we can tell when we've seen all factors. *)
		queue = EventuallyPeriodicSymbolicWord[
			If[TrueQ[OptionValue[TransientOnly]],
				First[initialqueue],
				SymbolicWordJoin[First[initialqueue], Last[initialqueue]]
			],
			MapAt[firstcharacter, Last[initialqueue], {1, 1}]
		];
		(* Construct the first factor of the given length. *)
		factor = Table[
			Replace[
				SymbolicWordPartitionAt[queue, subfactorlength, assumptions, SowFailedMinExpressions -> sowq],
				{
					_SymbolicWordPartitionAt :> Throw[True],
					{prefix_, newqueue_} :> (queue = newqueue; prefix)
				}
			]
			,
			{subfactorlength, lengths}
		];
		While[factorlist == {} || !MatchQ[SymbolicWordFirstBlockCharacter[factorlist[[-1, 1, 1]]], _firstcharacter],
			(* Determine an interval by computing the minimal first block length. *)
			intervalmax = MinFirstBlockLength[Append[factor, queue], assumptions, SowFailedMinExpressions -> sowq];
			If[intervalmax === $Failed,
				Throw[True]
			];
			If[TrueQ[intervalmax <= 0],
				Message[MinOrFail::pos, SymbolicWordLength[SymbolicWordBlockTake[#, 1]] & /@ Append[factor, queue]]; Throw[True]
			];
			factor = MapThread[
				SymbolicWordAppend,
				{
					FirstBlockCharacterDrop[#, i] & /@ factor,
					Superscript[SymbolicWordFirstBlockCharacter[#], i] & /@ Append[Rest[factor], queue]
				}
			];
			(* For the first factor, the lower endpoint of the interval needs to be 0 instead of 1,
			   since it doesn't have a previous interval to include that boundary point. *)
			factorlist = Append[factorlist, {factor, Boole[factorlist != {}] <= i <= intervalmax}];
			factor = SymbolicWordSimplify[#, assumptions] & /@ (factor /. i -> intervalmax);
			queue = FirstBlockCharacterDrop[queue, intervalmax, assumptions]
		];
		(* If an interval only contains one point and the next interval contains more than one point, merge the two. *)
		(factorlist = MapAt[# - 1 &, Delete[factorlist, #], {#, 2, 1}]; &) /@
			Reverse[Select[
				First /@ Position[Most[factorlist], {_, 1 <= i <= 1}],
				factorlist[[# + 1, 2, 1]] =!= factorlist[[# + 1, 2, -1]] &
			]];
		factorlist = (Most[factorlist] /. {firstcharacter -> Identity, i -> OptionValue[GeneratedParameters]});
		(* If the period begins and ends with the same character, then, because of the  firstcharacter  wrapper, some adjacent blocks may have the same characters. *)
		factorlist = MapAt[SymbolicWordSimplify /@ # &, #, 1] & /@ factorlist;
		False
	];
	factorlist /; !failed
]
SymbolicWordFactorList[
	initialqueue_?EventuallyPeriodicSymbolicWordQ,
	length : Except[_List],
	assumptions : Except[_Rule] : True,
	options : OptionsPattern[]
] :=
With[{factorlist = SymbolicWordFactorList[initialqueue, {length}, assumptions, options]},
	(MapAt[First, #, 1] &) /@ factorlist /;
		!MatchQ[factorlist, _SymbolicWordFactorList]
]
Options[SymbolicWordFactorList] = {GeneratedParameters -> C, SowFailedMinExpressions -> False, TransientOnly -> False}
SyntaxInformation[SymbolicWordFactorList] = {"ArgumentsPattern" -> {_, _, _., OptionsPattern[]}}

SymbolicWordFirstBlockCharacter[SymbolicWord[Superscript[character_, _], ___] ? SymbolicWordQ] :=
	character
SymbolicWordFirstBlockCharacter[EventuallyPeriodicSymbolicWord[SymbolicWord[], period_] ? EventuallyPeriodicSymbolicWordQ] :=
	SymbolicWordFirstBlockCharacter[period]
SymbolicWordFirstBlockCharacter[EventuallyPeriodicSymbolicWord[prefix_, _] ? EventuallyPeriodicSymbolicWordQ] :=
	SymbolicWordFirstBlockCharacter[prefix]
SyntaxInformation[SymbolicWordFirstBlockCharacter] = {"ArgumentsPattern" -> {_}}

SymbolicWordFirstCharacter[
	SymbolicWord[Superscript[character_, length_], ___] ? SymbolicWordQ,
	assumptions_ : True
] /; TrueQ[Refine[length >= 1, assumptions]] :=
	character
SymbolicWordFirstCharacter[
	word : SymbolicWord[Superscript[_, length_], ___] ? SymbolicWordQ,
	assumptions_ : True
] /; TrueQ[Refine[length == 0, assumptions]] :=
	SymbolicWordFirstCharacter[SymbolicWordBlockDrop[word, 1], assumptions]
SymbolicWordFirstCharacter[
	EventuallyPeriodicSymbolicWord[prefix_, period_] ? EventuallyPeriodicSymbolicWordQ,
	assumptions_ : True
] :=
	SymbolicWordFirstCharacter[SymbolicWordJoin[prefix, period], assumptions]
SyntaxInformation[SymbolicWordFirstCharacter] = {"ArgumentsPattern" -> {_, _.}}

SymbolicWordJoin[] :=
	SymbolicWord[]
SymbolicWordJoin[word : _?SymbolicWordQ | _?EventuallyPeriodicSymbolicWordQ] :=
	word
SymbolicWordJoin[
	word1 : SymbolicWord[___, Superscript[character_, _]] ? SymbolicWordQ,
	word2 : SymbolicWord[Superscript[character_, length2_], ___] ? SymbolicWordQ,
	words___?SymbolicWordQ
] :=
	SymbolicWordJoin[
		Join[MapAt[# + length2 &, word1, {-1, 2}], Rest[word2]],
		words
	]
SymbolicWordJoin[
	word1_?SymbolicWordQ,
	word2_?SymbolicWordQ,
	words___?SymbolicWordQ
] :=
	SymbolicWordJoin[
		Join[word1, word2],
		words
	]
SymbolicWordJoin[word_?SymbolicWordQ, periodicword : EventuallyPeriodicSymbolicWord[prefix_, period_] ? EventuallyPeriodicSymbolicWordQ] :=
	EventuallyPeriodicSymbolicWord[SymbolicWordJoin[word, prefix], period]
SymbolicWordJoin[
	words__?SymbolicWordQ,
	periodicword_?EventuallyPeriodicSymbolicWordQ
] :=
	SymbolicWordJoin[SymbolicWordJoin[words], periodicword]
SyntaxInformation[SymbolicWordJoin] = {"ArgumentsPattern" -> {___}}

SymbolicWordLength[word_?SymbolicWordQ] :=
	Total[Last /@ word]
SymbolicWordLength[periodicword_?EventuallyPeriodicSymbolicWordQ] :=
	Infinity
(* These are extensions to allow "compound" symbolic words that don't satisfy SymbolicWordQ.  They assume all exponents are non-negative.
   Some of the other basic SymbolicWord* functions could also be extended to this more general object. *)
SymbolicWordLength[SymbolicWordPower[word_, power_]?ExtendedSymbolicWordQ] :=
	power SymbolicWordLength[word]
SymbolicWordLength[word_SymbolicWordJoin?ExtendedSymbolicWordQ] :=
	Total[SymbolicWordLength /@ List @@ word]
SyntaxInformation[SymbolicWordLength] = {"ArgumentsPattern" -> {_}}

SymbolicWordPartitionAt[
	periodicword_?EventuallyPeriodicSymbolicWordQ,
	length_,
	assumptions : Except[_Rule] : True,
	options : OptionsPattern[]
] :=
Module[{prefix = SymbolicWord[], queue = periodicword, remainingcharactercount = length, nonnegativeQ, shiftlength},
	While[nonnegativeQ = RefineOrFail[remainingcharactercount >= 0, assumptions],
		If[TrueQ[Refine[remainingcharactercount == 0, assumptions]],
			Break[]
		];
		shiftlength = MinOrFail[{remainingcharactercount, SymbolicWordLength[SymbolicWordBlockTake[queue, 1]]}, assumptions, options];
		If[shiftlength === $Failed,
			nonnegativeQ = $Failed; Break[]
		];
		If[TrueQ[shiftlength <= 0],
			Message[MinOrFail::pos, {remainingcharactercount, SymbolicWordLength[SymbolicWordBlockTake[queue, 1]]}]; nonnegativeQ = $Failed; Break[]
		];
		prefix = SymbolicWordAppend[prefix, Superscript[SymbolicWordFirstBlockCharacter[queue], shiftlength]];
		(* Pass the assumptions to SymbolicWordSimplify to detect zeros such as  a - 7  for
			SymbolicWordPartitionAt[
				EventuallyPeriodicSymbolicWord[SymbolicWord[], SymbolicWord[Superscript[0, a - 1], Superscript[1, 1], Superscript[0, a - b - 1], Superscript[n+1, 1]]],
				3 a - 3 b,
				a == 7 && b == 4
			]
		*)
		queue = FirstBlockCharacterDrop[queue, shiftlength, assumptions];
		remainingcharactercount -= shiftlength
	];
	{prefix, queue} /; nonnegativeQ =!= $Failed
]
Options[SymbolicWordPartitionAt] = {SowFailedMinExpressions -> False}
SyntaxInformation[SymbolicWordPartitionAt] = {"ArgumentsPattern" -> {_, _, _., OptionsPattern[]}}

SymbolicWordPower[word_?SymbolicWordQ, power_Integer?NonNegative] :=
	SymbolicWordJoin @@ ConstantArray[word, power]
SymbolicWordPower[SymbolicWord[Superscript[character_, length_]], power_] :=
	SymbolicWord[Superscript[character, length power]]
SyntaxInformation[SymbolicWordPower] = {"ArgumentsPattern" -> {_, _}}

SymbolicWordQ[SymbolicWord[Superscript[_, _] ...]] := True
SymbolicWordQ[_] := False
SyntaxInformation[SymbolicWordQ] = {"ArgumentsPattern" -> {_}}

(* SymbolicWordSimplified currently never evaluates to False, although it could be extended. *)
SymbolicWordSimplified[
	word_?SymbolicWordQ,
	assumptions_ : True
] /; And[
		TrueQ[And @@ (Refine[Last[#] >= 1, assumptions] &) /@ word],
		TrueQ[And @@ (Refine[Unequal @@ #, assumptions] &) /@ Partition[First /@ word, 2, 1]]
	] := True
(* This doesn't check that the last character of the prefix is unequal to the first character of the period. *)
SymbolicWordSimplified[
	EventuallyPeriodicSymbolicWord[prefix_, period_] ? EventuallyPeriodicSymbolicWordQ,
	assumptions_ : True
] /; And[
		TrueQ[SymbolicWordSimplified[prefix, assumptions]],
		TrueQ[SymbolicWordSimplified[period, assumptions]]
	] := True
SyntaxInformation[SymbolicWordSimplified] = {"ArgumentsPattern" -> {_, _.}}


(*** SymbolicWordSimplify code ***)

deleteEmptyBlocks[word_SymbolicWord, assumptions_] :=
	DeleteCases[word, Superscript[_, exponent_ /; TrueQ[Refine[exponent == 0, assumptions]]]]
deleteEmptyBlocks[EventuallyPeriodicSymbolicWord[prefix_, period_], assumptions_] :=
	EventuallyPeriodicSymbolicWord[deleteEmptyBlocks[prefix, assumptions], period]

mergeBlocks[word_SymbolicWord] :=
	FixedPoint[
		Replace[#,
			SymbolicWord[a___, Superscript[character_, length1_], Superscript[character_, length2_], z___] :>
				SymbolicWord[a, Superscript[character, length1 + length2], z]
		] &,
		word
	]
mergeBlocks[word_EventuallyPeriodicSymbolicWord] :=
	SymbolicWordSimplify /@ word

SymbolicWordSimplify[
	word : _?SymbolicWordQ | _?EventuallyPeriodicSymbolicWordQ,
	assumptions_ : True
] :=
	mergeBlocks[deleteEmptyBlocks[word, assumptions]]
SyntaxInformation[SymbolicWordSimplify] = {"ArgumentsPattern" -> {_, _.}}

(*** end SymbolicWordSimplify code ***)


(* TODO Should these all be testing their arguments with SymbolicWordQ? *)
(* Some of these could cause  $RecursionLimit  to be hit for words with many blocks. *)
SymbolicWordUnequal[
	w_?SymbolicWordQ,
	w_,
	_ : True
] := False
(* Chop identical prefixes. *)
SymbolicWordUnequal[
	word1 : SymbolicWord[block_, ___],
	word2 : SymbolicWord[block_, ___],
	assumptions_ : True
] := SymbolicWordUnequal[Rest[word1], Rest[word2], assumptions]
(* Chop identical suffixes. *)
SymbolicWordUnequal[
	word1 : SymbolicWord[___, block_],
	word2 : SymbolicWord[___, block_],
	assumptions_ : True
] := SymbolicWordUnequal[Most[word1], Most[word2], assumptions]
(* Chop prefixes of the same length. *)
SymbolicWordUnequal[
	word1 : SymbolicWord[Superscript[_, length_], ___],
	word2 : SymbolicWord[Superscript[_, length_], ___],
	assumptions_ : True
] /; TrueQ[SymbolicWordUnequal[Rest[word1], Rest[word2], assumptions]] := True
(* Chop suffixes of the same length. *)
SymbolicWordUnequal[
	word1 : SymbolicWord[___, Superscript[_, length_]],
	word2 : SymbolicWord[___, Superscript[_, length_]],
	assumptions_ : True
] /; TrueQ[SymbolicWordUnequal[Most[word1], Most[word2], assumptions]] := True
(* A constant word isn't equal to a word containing a different letter. *)
SymbolicWordUnequal[
	SymbolicWord[Superscript[a_, _]],
	SymbolicWord[___, Superscript[b_, blength_], ___],
	assumptions_ : True
] /; TrueQ[Refine[a != b && blength >= 1, assumptions]] := True
SymbolicWordUnequal[
	SymbolicWord[___, Superscript[b_, blength_], ___],
	SymbolicWord[Superscript[a_, _]],
	assumptions_ : True
] /; TrueQ[Refine[a != b && blength >= 1, assumptions]] := True
(* These are generalized by the down value below ("Find all blocks of a single character ..."), but I'm keeping them because they are faster in the cases they apply. *)
(* Compare prefixes. *)
SymbolicWordUnequal[
	SymbolicWord[Superscript[a_, length1_], Superscript[b_, blength_], ___],
	SymbolicWord[Superscript[a_, length2_], Superscript[c_, clength_], ___],
	assumptions_ : True
] /; TrueQ[Refine[a != b && a != c && length1 != length2 && blength >= 1 && clength >= 1, assumptions]] := True
(* Compare suffixes. *)
SymbolicWordUnequal[
	SymbolicWord[___, Superscript[b_, blength_], Superscript[a_, length1_]],
	SymbolicWord[___, Superscript[c_, clength_], Superscript[a_, length2_]],
	assumptions_ : True
] /; TrueQ[Refine[a != b && a != c && length1 != length2 && blength >= 1 && clength >= 1, assumptions]] := True
(* Compare first characters. *)
SymbolicWordUnequal[
	word1_?SymbolicWordQ,
	word2_?SymbolicWordQ,
	assumptions_ : True
] :=
With[{a = SymbolicWordFirstCharacter[word1, assumptions], b = SymbolicWordFirstCharacter[word2, assumptions]},
	True /; !MemberQ[{a, b}, _SymbolicWordFirstCharacter] && TrueQ[Refine[a != b, assumptions]]
]
(* Compare last characters. *)
SymbolicWordUnequal[
	word1_?SymbolicWordQ,
	word2_?SymbolicWordQ,
	assumptions_ : True
] :=
With[{a = SymbolicWordFirstCharacter[Reverse[word1], assumptions], b = SymbolicWordFirstCharacter[Reverse[word2], assumptions]},
	True /; !MemberQ[{a, b}, _SymbolicWordFirstCharacter] && TrueQ[Refine[a != b, assumptions]]
]
(* Replace a variable with an integer if there is an inequality like  1<=i<=1  that restricts it to a single integer. *)
SymbolicWordUnequal[
	word1_?SymbolicWordQ,
	word2_?SymbolicWordQ,
	integer_Integer <= variable_ <= integer_
] := SymbolicWordUnequal[word1 /. variable -> integer, word2 /. variable -> integer]
SymbolicWordUnequal[
	word1_?SymbolicWordQ,
	word2_?SymbolicWordQ,
	assumptions : And[___, integer_Integer <= variable_ <= integer_, ___]
] := SymbolicWordUnequal[word1 /. variable -> integer, word2 /. variable -> integer, DeleteCases[assumptions, integer <= variable <= integer]]
(* Find all blocks of a single character, and either...
   1. Compare the words obtained by deleting the blocks.  For example:
	SymbolicWordUnequal[
		SymbolicWord[Superscript[0,-1 + 5 a - 6 b - i], Superscript[1,1], Superscript[0,-7 a + 9 b + i]],
		SymbolicWord[Superscript[0,-1 - 2 a + 3 b - j], Superscript[2 + n,1], Superscript[0,j]],
		n >= 0
	]
   2. Refine the system of block length equalities.  For example:
	SymbolicWordUnequal[
		SymbolicWord[Superscript[0,-1 + 352 a - 621 b - i], Superscript[1,1], Superscript[0,-1 - 51 a + 91 b], Superscript[1 + n,1], Superscript[0,i]],
		SymbolicWord[Superscript[0,-1 - 51 a + 91 b - j], Superscript[1 + n,1], Superscript[0,-1 + 352 a - 621 b], Superscript[1,1], Superscript[0,j]],
		0 <= i <= -1 + 352 a - 621 b && 0 <= j <= -1 - 51 a + 91 b && (a | b) \[Element] Integers && GCD[a, b] == 1 && GCD[301, b] == 1 && (30 b)/17 < a < (53 b)/30 && n >= 0
	]
*)
SymbolicWordUnequal[
	word1 : SymbolicWord[Superscript[a_, _], ___],
	word2_?SymbolicWordQ,
	assumptions_ : True
] :=
Module[{markedblocks1, markedblocks2, shortenedword1, shortenedword2, deletedblocklengths1, deletedblocklengths2},
	(* Mark each block according to whether it is the designated letter or not. *)
	markedblocks1 = {#, TrueQ[Refine[First[#] == a, assumptions]]} & /@ List @@ word1;
	markedblocks2 = {#, TrueQ[Refine[First[#] == a, assumptions]]} & /@ List @@ word2;
	shortenedword1 = SymbolicWordSimplify[SymbolicWord @@ Cases[markedblocks1, {block_, False} :> block]];
	shortenedword2 = SymbolicWordSimplify[SymbolicWord @@ Cases[markedblocks2, {block_, False} :> block]];
	deletedblocklengths1 = Cases[markedblocks1, {Superscript[_, length_], True} :> length];
	deletedblocklengths2 = Cases[markedblocks2, {Superscript[_, length_], True} :> length];
	True /; And[
		(* All of the remaining characters are unequal to the deleted character. *)
		TrueQ[And @@ (Refine[First[#] != a, assumptions] &) /@ shortenedword1],
		TrueQ[And @@ (Refine[First[#] != a, assumptions] &) /@ shortenedword2],
		Or[
			(* The words obtained by deleting the designated letter are unequal. *)
			TrueQ[SymbolicWordUnequal[shortenedword1, shortenedword2, assumptions]],
			And[
				(* There are the same number of deleted blocks. *)
				Length[deletedblocklengths1] == Length[deletedblocklengths2] >= 1,
				(* There aren't adjacent blocks of the designated letter. *)
				!MatchQ[markedblocks1, {___, {_, True}, {_, True}, ___}],
				!MatchQ[markedblocks2, {___, {_, True}, {_, True}, ___}],
				(* The remaining block lengths are positive.  (It would suffice to show that the deleted blocks are separated by words of positive length.) *)
				TrueQ[And @@ (Refine[Last[#] >= 1, assumptions] &) /@ List @@ shortenedword1],
				TrueQ[And @@ (Refine[Last[#] >= 1, assumptions] &) /@ List @@ shortenedword2],
				(* The system of equalities of the deleted block lengths has no solution. *)
				TrueQ[!Refine[
					And @@ Thread[deletedblocklengths1 == deletedblocklengths2],
					assumptions
				]]
			]
		]
	]
]
(* This is the same as the previous down value; just the first two arguments are swapped.
   It's needed for the following (or at least it used to be needed, before we started replacing  i->1  when  1<=i<=1 ).
	SymbolicWordUnequal[
		SymbolicWord[Superscript[1,2 - i], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[2,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,1 + i]],
		SymbolicWord[Superscript[0,7 - j], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[2,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,5], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,7], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,2], Superscript[1,1], Superscript[0,j]],
		1 <= i <= 1 && 0 <= j <= 7
	]
*)
SymbolicWordUnequal[
	word1_?SymbolicWordQ,
	word2 : SymbolicWord[Superscript[a_, _], ___],
	assumptions_ : True
] :=
Module[{markedblocks1, markedblocks2, shortenedword1, shortenedword2, deletedblocklengths1, deletedblocklengths2},
	(* Mark each block according to whether it is the designated letter or not. *)
	markedblocks1 = {#, TrueQ[Refine[First[#] == a, assumptions]]} & /@ List @@ word1;
	markedblocks2 = {#, TrueQ[Refine[First[#] == a, assumptions]]} & /@ List @@ word2;
	shortenedword1 = SymbolicWordSimplify[SymbolicWord @@ Cases[markedblocks1, {block_, False} :> block]];
	shortenedword2 = SymbolicWordSimplify[SymbolicWord @@ Cases[markedblocks2, {block_, False} :> block]];
	deletedblocklengths1 = Cases[markedblocks1, {Superscript[_, length_], True} :> length];
	deletedblocklengths2 = Cases[markedblocks2, {Superscript[_, length_], True} :> length];
	True /; And[
		(* All of the remaining characters are unequal to the deleted character. *)
		TrueQ[And @@ (Refine[First[#] != a, assumptions] &) /@ shortenedword1],
		TrueQ[And @@ (Refine[First[#] != a, assumptions] &) /@ shortenedword2],
		Or[
			(* The words obtained by deleting the designated letter are unequal. *)
			TrueQ[SymbolicWordUnequal[shortenedword1, shortenedword2, assumptions]],
			And[
				(* There are the same number of deleted blocks. *)
				Length[deletedblocklengths1] == Length[deletedblocklengths2] >= 1,
				(* There aren't adjacent blocks of the designated letter. *)
				!MatchQ[markedblocks1, {___, {_, True}, {_, True}, ___}],
				!MatchQ[markedblocks2, {___, {_, True}, {_, True}, ___}],
				(* The remaining block lengths are positive.  (It would suffice to show that the deleted blocks are separated by words of positive length.) *)
				TrueQ[And @@ (Refine[Last[#] >= 1, assumptions] &) /@ List @@ shortenedword1],
				TrueQ[And @@ (Refine[Last[#] >= 1, assumptions] &) /@ List @@ shortenedword2],
				(* The system of equalities of the deleted block lengths has no solution. *)
				TrueQ[!Refine[
					And @@ Thread[deletedblocklengths1 == deletedblocklengths2],
					assumptions
				]]
			]
		]
	]
]
(* This is probably also generalized by a previous down value, but it also speeds things up. *)
SymbolicWordUnequal[
	word1 : SymbolicWord[Superscript[a_, _], ___],
	word2_?SymbolicWordQ,
	assumptions_ : True
] :=
Module[{shortenedword1, shortenedword2},
	shortenedword1 = SymbolicWordSimplify[Select[word1, !TrueQ[Refine[First[#] == a, assumptions]] &]];
	shortenedword2 = SymbolicWordSimplify[Select[word2, !TrueQ[Refine[First[#] == a, assumptions]] &]];
	True /; And[
		TrueQ[And @@ (Refine[First[#] != a, assumptions] &) /@ shortenedword1],
		TrueQ[And @@ (Refine[First[#] != a, assumptions] &) /@ shortenedword2],
		TrueQ[SymbolicWordUnequal[shortenedword1, shortenedword2, assumptions]]
	]
]
(* Compare the explicit character lists for integer block lengths. *)
SymbolicWordUnequal[
	word1 : SymbolicWord[Superscript[_, _Integer?NonNegative] ...],
	word2 : SymbolicWord[Superscript[_, _Integer?NonNegative] ...],
	assumptions_ : True
] :=
Module[{result},
	result = !Replace[
		SymbolicWordCharacters[word1] == SymbolicWordCharacters[word2],
		equation : HoldPattern[Equal][__List] :>
			Refine[And @@ Thread[equation], assumptions]
	];
	result /; MatchQ[result, True | False]
]
(* Generate the explicit character lists for a one-parameter family.  For example:
	SymbolicWordUnequal[
		SymbolicWord[Superscript[0,1 - C], Superscript[1,2], Superscript[0,7], Superscript[1,1], Superscript[1 + n,1], Superscript[0,7], Superscript[1,2], Superscript[0,6], Superscript[1,1 + C]],
		SymbolicWord[Superscript[0,1 - C], Superscript[1,1], Superscript[1 + n,1], Superscript[0,7], Superscript[1,2], Superscript[0,6], Superscript[1,2], Superscript[0,7], Superscript[1,1], Superscript[1 + n,C]],
		1 <= C <= 1 && n >= 0
	]
*)
SymbolicWordUnequal[
	word1_?SymbolicWordQ,
	word2_?SymbolicWordQ,
	assumptions_ : True
] :=
Module[{symbol, interval, explicitwords, result},
	symbol = Variables[Join[Last /@ List @@ word1, Last /@ List @@ word2]];
	If[Length[symbol] == 1,
		symbol = First[symbol];
		(* Find an interval for the parameter. *)
		Replace[
			AssembleAssumptions[assumptions],
			(* These rules don't pick up assumptions like  C == 1 . *)
			{
				min_Integer <= symbol <= max_Integer :> (interval = {min, max}),
				(* This rule only finds the first relevant interval. *)
				And[___, min_Integer <= symbol <= max_Integer, ___] :> (interval = {min, max})
			}
		]
	];
	If[ListQ[interval],
		explicitwords = Table @@ {
			{word1, word2, assumptions},
			{symbol, interval[[1]], interval[[2]]}
		};
		result = And @@ (!Replace[
			SymbolicWordCharacters[#1] == SymbolicWordCharacters[#2],
			equation : HoldPattern[Equal][__List] :>
				Refine[And @@ Thread[equation], #3]
		] &) @@@ explicitwords
	];
	result /; MatchQ[result, True | False]
]
(* Compare the lengths. *)
SymbolicWordUnequal[
	word1_?SymbolicWordQ,
	word2_?SymbolicWordQ,
	assumptions_ : True
] /; TrueQ[Refine[SymbolicWordLength[word1] != SymbolicWordLength[word2], assumptions]] := True
(* Delete empty blocks (and merge adjacent blocks with the same letters). *)
SymbolicWordUnequal[
	word1_?SymbolicWordQ,
	word2_?SymbolicWordQ,
	assumptions_ : True
] :=
With[{newword1 = SymbolicWordSimplify[word1, assumptions], newword2 = SymbolicWordSimplify[word2, assumptions]},
	SymbolicWordUnequal[newword1, newword2, assumptions] /; newword1 =!= word1 || newword2 =!= word2
]
SyntaxInformation[SymbolicWordUnequal] = {"ArgumentsPattern" -> {_, _, _.}}

ToSymbolicWord[list_List] :=
	SymbolicWord @@ (Superscript[First[#], Length[#]] &) /@ Split[list]
SyntaxInformation[ToSymbolicWord] = {"ArgumentsPattern" -> {_}}


(*
LocatingLengthExceptionalRationals make the morphism a perfect power.
PowerFreeExceptionalRationals are obstructions to power-freeness.

WordAdditionalRationals are exceptional rationals that aren't governed by the morphism but that lie in the interval and nonetheless have the predicted value of k.
*)
$PowerFreeMorphismList = {
	(* 2 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, a - 1], Superscript[1, 1], Superscript[0, a - b - 1], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {2, -1},
		"LocatingLengthCoefficients" -> {2, -2},
		"NonzeroCharacterCount" -> 2,
		"SourceRationals" -> {5/3, 22/13, 12/7, 19/11, 26/15, 23/13, 16/9, 9/5, 20/11, 24/13, 13/7, 28/15, 17/9, 21/11, 25/13, 29/15},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {5/3, 2},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 5/3 <= q < 2 && CoprimeQ[Denominator[q], 2]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {},
		"WordExceptionalRationals" -> {},
		"WordIntervalEndpoints" -> {5/3, 2},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 5/3 <= q < 2 && CoprimeQ[Denominator[q], 2]],
		"WordStatus" -> "Theorem"
	},
	(* 3 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, 5*a - 6*b - 1], Superscript[1, 1], Superscript[0, 3*b - 2*a - 1], Superscript[1, 1], Superscript[0, 3*b - 2*a - 1], Superscript[n + 2, 1]]
		]],
		"LengthCoefficients" -> {1, 0},
		"LocatingLengthCoefficients" -> {3, -3},
		"NonzeroCharacterCount" -> 3,
		"SourceRationals" -> {84/67, 74/59, 69/55, 64/51, 59/47, 54/43, 49/39, 39/31, 34/27, 29/23, 82/65, 77/61, 24/19, 67/53, 19/15, 52/41, 85/67, 80/63, 47/37, 75/59, 65/51, 88/69, 37/29, 60/47, 83/65, 78/61, 55/43, 32/25, 73/57, 41/32, 91/71, 50/39, 109/85, 127/99, 68/53, 86/67},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {5/4, 4/3},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 5/4 < q < 4/3],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {(*41/32 doesn't satisfy the gcd condition*)},
		"WordExceptionalRationals" -> {44/35, 14/11},
		"WordIntervalEndpoints" -> {5/4, 9/7},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 5/4 < q < 9/7 && q != 14/11 && q != 44/35 && CoprimeQ[Denominator[q], 2]],
		"WordStatus" -> "Conjecture"
	},
	(* 4 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, a - 1], Superscript[1, 1], Superscript[0, a - b - 1], Superscript[1, 1], Superscript[0, 2*a - 2*b - 1], Superscript[1, 1], Superscript[0, a - b - 1], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {5, -4},
		"LocatingLengthCoefficients" -> {5, -5},
		"NonzeroCharacterCount" -> 4,
		"SourceRationals" -> {20/13, 17/11, 14/9, 25/16, 11/7, 19/12, 35/22, 29/18, 21/13, 55/34, 144/89, 34/21, 13/8, 18/11, 23/14},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {3/2, 5/3},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 3/2 < q < 5/3 && CoprimeQ[Denominator[q], 5]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {},
		"WordExceptionalRationals" -> {},
		"WordIntervalEndpoints" -> {3/2, 5/3},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 3/2 < q < 5/3 && CoprimeQ[Denominator[q], 5]],
		"WordStatus" -> "Theorem"
	},
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 6*a - 7*b], Superscript[1, 1], Superscript[0, -1 - 3*a + 4*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 10*b], Superscript[1, 1], Superscript[0, -1 + 6*a - 7*b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {1, 0},
		"LocatingLengthCoefficients" -> {1, 0},
		"NonzeroCharacterCount" -> 4,
		"SourceRationals" -> {52/43, 86/71, 28/23},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {17/14, 11/9},
		"PowerFreeIntervalEndpoints" -> {6/5, 5/4},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 6/5 < q < 5/4 && q != 17/14 && q != 11/9],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> Missing["Unknown"],
		"WordExceptionalRationals" -> Missing["Unknown"],
		"WordIntervalEndpoints" -> Missing["Unknown"],
		"WordRationalTest" -> Missing["Unknown"],
		"WordStatus" -> None
	},
	(* 6 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 4*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {4, -2},
		"LocatingLengthCoefficients" -> {5, -4},
		"NonzeroCharacterCount" -> 6,
		"SourceRationals" -> {53/39, 52/35},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {7/5, 5/3},
		"PowerFreeIntervalEndpoints" -> {4/3, 2},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 4/3 < q < 2 && q != 7/5 && q != 5/3 && CoprimeQ[Denominator[q], 4]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> Missing["Unknown"],
		"WordExceptionalRationals" -> Missing["Unknown"],
		"WordIntervalEndpoints" -> Missing["Unknown"],
		"WordRationalTest" -> Missing["Unknown"],
		"WordStatus" -> None
	},
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 4*b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {4, -2},
		"LocatingLengthCoefficients" -> {5, -4},
		"NonzeroCharacterCount" -> 6,
		"SourceRationals" -> {10/7, 52/35},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {7/5, 5/3},
		"PowerFreeIntervalEndpoints" -> {4/3, 2},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 4/3 < q < 2 && q != 7/5 && q != 5/3 && CoprimeQ[Denominator[q], 4]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> Missing["Unknown"],
		"WordExceptionalRationals" -> Missing["Unknown"],
		"WordIntervalEndpoints" -> Missing["Unknown"],
		"WordRationalTest" -> Missing["Unknown"],
		"WordStatus" -> None
	},
	(* 8 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 5*a - 6*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 6*a + 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {5, -3},
		"LocatingLengthCoefficients" -> {6, -6},
		"NonzeroCharacterCount" -> 8,
		"SourceRationals" -> {},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {9/7},
		"PowerFreeIntervalEndpoints" -> {5/4, 4/3},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 5/4 < q < 4/3 && q != 9/7 && CoprimeQ[Denominator[q], 5]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> Missing["Unknown"],
		"WordExceptionalRationals" -> Missing["Unknown"],
		"WordIntervalEndpoints" -> Missing["Unknown"],
		"WordRationalTest" -> Missing["Unknown"],
		"WordStatus" -> None
	},
	(* 10 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 3*a + 4*b], Superscript[1, 1], Superscript[0, -1 + 5*a - 6*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {11, -10},
		"LocatingLengthCoefficients" -> {7, -7},
		"NonzeroCharacterCount" -> 10,
		"SourceRationals" -> {45/37, 50/41},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {23/19, 17/14, 11/9, 16/13},
		"PowerFreeIntervalEndpoints" -> {6/5, 5/4},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 6/5 < q < 5/4 && q != 23/19 && q != 17/14 && q != 11/9 && q != 16/13 && CoprimeQ[Denominator[q], 11]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> Missing["Unknown"],
		"WordExceptionalRationals" -> Missing["Unknown"],
		"WordIntervalEndpoints" -> Missing["Unknown"],
		"WordRationalTest" -> Missing["Unknown"],
		"WordStatus" -> None
	},
	(* 12 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 4*a + 5*b], Superscript[1, 1], Superscript[0, -1 + 6*a - 7*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 4*a + 5*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 4*a + 5*b], Superscript[1, 1], Superscript[0, -1 - 4*a + 5*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {7, -5},
		"LocatingLengthCoefficients" -> {5, -3},
		"NonzeroCharacterCount" -> 12,
		"SourceRationals" -> {84/71, 45/38, 77/65, 32/27, 51/43, 70/59, 19/16, 63/53, 44/37, 56/47, 31/26, 68/57, 37/31, 43/36, 49/41, 61/51, 73/61},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {13/11},
		"PowerFreeIntervalEndpoints" -> {7/6, 6/5},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 7/6 < q < 6/5 && q != 13/11 && CoprimeQ[Denominator[q], 7]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {},
		"WordExceptionalRationals" -> {},
		"WordIntervalEndpoints" -> {13/11, 6/5},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 13/11 < q < 6/5 && CoprimeQ[Denominator[q], 7]],
		"WordStatus" -> "Conjecture"
	},
	(* 13 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 3*a + 4*b], Superscript[1, 1], Superscript[0, -1 + 4*a - 4*b], Superscript[1, 1], Superscript[0, -1 - 3*a + 4*b], Superscript[1, 1], Superscript[0, -1 + 5*a - 6*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 3*a + 4*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 3*a + 4*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 2, 1]]
		]],
		"LengthCoefficients" -> {7, -4},
		"LocatingLengthCoefficients" -> {5, -5},
		"NonzeroCharacterCount" -> 13,
		"SourceRationals" -> {39/32, 11/9, 27/22, 21/17},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {6/5, 5/4},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 6/5 < q < 5/4 && CoprimeQ[Denominator[q], 7]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> Missing["Unknown"],
		"WordExceptionalRationals" -> Missing["Unknown"],
		"WordIntervalEndpoints" -> Missing["Unknown"],
		"WordRationalTest" -> Missing["Unknown"],
		"WordStatus" -> None
	},
	(* 14 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[n + 2, 1]]
		]],
		"LengthCoefficients" -> {8, -4},
		"LocatingLengthCoefficients" -> {1, 0},
		"NonzeroCharacterCount" -> 14,
		"SourceRationals" -> {58/45, 89/69, 97/75, 35/27, 74/57, 113/87, 121/93, 82/63, 43/33, 59/45, 67/51, 83/63, 91/69, 107/81, 115/87, 131/99},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {9/7, 4/3},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 9/7 <= q < 4/3 && CoprimeQ[Denominator[q], 8]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {},
		"WordExceptionalRationals" -> {},
		"WordIntervalEndpoints" -> {9/7, 4/3},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 9/7 < q < 4/3 && CoprimeQ[Denominator[q], 8] && Divisible[Denominator[q], 3]],
		"WordStatus" -> "Conjecture"
	},
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 6*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 8*a - 11*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 - 6*a + 9*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 6*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 4*a + 6*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + 6*a - 8*b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {6, -1},
		"LocatingLengthCoefficients" -> {6, -1},
		"NonzeroCharacterCount" -> 14,
		"SourceRationals" -> {24/17, 41/29},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {17/12},
		"PowerFreeExceptionalRationals" -> {7/5, 10/7},
		"PowerFreeIntervalEndpoints" -> {11/8, 3/2},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 11/8 < q < 3/2 && q != 7/5 && q != 10/7 && CoprimeQ[Denominator[q], 6]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> Missing["Unknown"],
		"WordExceptionalRationals" -> Missing["Unknown"],
		"WordIntervalEndpoints" -> Missing["Unknown"],
		"WordRationalTest" -> Missing["Unknown"],
		"WordStatus" -> None
	},
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 23*a + 33*b], Superscript[1, 1], Superscript[0, -1 + 25*a - 35*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 - 23*a + 33*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 23*a - 32*b], Superscript[1, 1], Superscript[0, -1 - 21*a + 30*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + 23*a - 32*b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {6, -1},
		"LocatingLengthCoefficients" -> {2, 0},
		"NonzeroCharacterCount" -> 14,
		"SourceRationals" -> {24/17, 58/41},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {65/46},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {7/5, 10/7},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 7/5 < q < 10/7 && CoprimeQ[Denominator[q], 6]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> Missing["Unknown"],
		"WordExceptionalRationals" -> Missing["Unknown"],
		"WordIntervalEndpoints" -> Missing["Unknown"],
		"WordRationalTest" -> Missing["Unknown"],
		"WordStatus" -> None
	},
	(* 16 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 6*a + 7*b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 - 6*a + 7*b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 6*a + 7*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 6*a + 7*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 6*a + 7*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {9, -7},
		"LocatingLengthCoefficients" -> {7, -7},
		"NonzeroCharacterCount" -> 16,
		"SourceRationals" -> {42/37, 67/59, 25/22, 33/29, 74/65, 49/43, 81/71, 97/85},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {9/8, 8/7},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 9/8 < q < 8/7 && CoprimeQ[Denominator[q], 9]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {},
		"WordExceptionalRationals" -> {},
		"WordIntervalEndpoints" -> {17/15, 8/7},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 17/15 < q < 8/7 && CoprimeQ[Denominator[q], 9]],
		"WordStatus" -> "Conjecture"
	},
	(* 18 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {10, -8},
		"LocatingLengthCoefficients" -> {6, -5},
		"NonzeroCharacterCount" -> 18,
		"SourceRationals" -> {149/133, 93/83, 102/91, 37/33, 46/41, 55/49, 64/57, 82/73, 91/81, 100/89, 109/97},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {19/17},
		"PowerFreeIntervalEndpoints" -> {10/9, 9/8},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 10/9 < q < 9/8 && q != 19/17 && CoprimeQ[Denominator[q], 10]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {},
		"WordExceptionalRationals" -> {},
		"WordIntervalEndpoints" -> {28/25, 9/8},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 28/25 < q < 9/8 && CoprimeQ[Denominator[q], 10]],
		"WordStatus" -> "Conjecture"
	},
	(* 20 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {11, -9},
		"LocatingLengthCoefficients" -> {4, -3},
		"NonzeroCharacterCount" -> 20,
		"SourceRationals" -> {52/47, 31/28, 72/65, 41/37},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {21/19},
		"PowerFreeIntervalEndpoints" -> {11/10, 10/9},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 11/10 < q < 10/9 && q != 21/19 && CoprimeQ[Denominator[q], 11]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {},
		"WordExceptionalRationals" -> {},
		"WordIntervalEndpoints" -> {21/19, 10/9},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 21/19 < q < 10/9 && CoprimeQ[Denominator[q], 11]],
		"WordStatus" -> "Conjecture"
	},
	(* 24 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 13*a - 14*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 13*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 13*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 13*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 13*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 11*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {13, -11},
		"LocatingLengthCoefficients" -> {4, -3},
		"NonzeroCharacterCount" -> 24,
		"SourceRationals" -> {62/57, 49/45},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {25/23},
		"PowerFreeIntervalEndpoints" -> {13/12, 12/11},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 13/12 < q < 12/11 && q != 25/23 && CoprimeQ[Denominator[q], 13]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {},
		"WordExceptionalRationals" -> {37/34},
		"WordIntervalEndpoints" -> {25/23, 12/11},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 25/23 < q < 12/11 && q != 37/34 && CoprimeQ[Denominator[q], 13]],
		"WordStatus" -> "Conjecture"
	},
	(* 26 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 5*a + 6*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 14*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 14*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 5*a + 6*b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {9, -4},
		"LocatingLengthCoefficients" -> {7, -6},
		"NonzeroCharacterCount" -> 26,
		"SourceRationals" -> {97/83, 69/59, 41/35},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {20/17},
		"PowerFreeExceptionalRationals" -> {13/11},
		"PowerFreeIntervalEndpoints" -> {7/6, 6/5},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 7/6 < q < 6/5 && q != 20/17 && q != 13/11 && CoprimeQ[Denominator[q], 9]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> Missing["Unknown"],
		"WordExceptionalRationals" -> Missing["Unknown"],
		"WordIntervalEndpoints" -> Missing["Unknown"],
		"WordRationalTest" -> Missing["Unknown"],
		"WordStatus" -> None
	},
	(* 29 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 3*a + 4*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 3*a + 4*b], Superscript[2, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 5*a + 6*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 5*a + 6*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 4*a + 5*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 5*a + 6*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 2, 1]]
		]],
		"LengthCoefficients" -> {14, -9},
		"LocatingLengthCoefficients" -> {6, -6},
		"NonzeroCharacterCount" -> 29,
		"SourceRationals" -> {111/97, 95/83, 79/69, 63/55, 47/41, 70/61, 31/27, 54/47, 77/67, 100/87},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {8/7, 6/5},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 8/7 < q < 6/5 && CoprimeQ[Denominator[q], 14]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {},
		"WordExceptionalRationals" -> {},
		"WordIntervalEndpoints" -> {8/7, 23/20},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 8/7 < q < 23/20 && CoprimeQ[Denominator[q], 14]],
		"WordStatus" -> "Conjecture"
	},
	(* 30 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 - 11*a + 13*b], Superscript[1, 1], Superscript[0, -1 + 14*a - 16*b], Superscript[1, 1], Superscript[0, -1 - 18*a + 21*b], Superscript[1, 1], Superscript[0, -1 + 20*a - 23*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 18*a + 21*b], Superscript[1, 1], Superscript[0, -1 + 14*a - 16*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 18*a + 21*b], Superscript[1, 1], Superscript[0, -1 + 14*a - 16*b], Superscript[1, 1], Superscript[0, -1 - 18*a + 21*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 21*a - 24*b], Superscript[1, 1], Superscript[0, -1 - 18*a + 21*b], Superscript[1, 1], Superscript[0, -1 + 14*a - 16*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 14*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 14*a - 16*b], Superscript[1, 1], Superscript[0, -1 - 18*a + 21*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 14*a - 16*b], Superscript[1, 1], Superscript[0, -1 - 18*a + 21*b], Superscript[1, 1], Superscript[0, -1 + 14*a - 16*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {10, -5},
		"LocatingLengthCoefficients" -> {1, 0},
		"NonzeroCharacterCount" -> 30,
		"SourceRationals" -> {112/97, 82/71, 89/77, 96/83, 59/51, 103/89},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {37/32},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {15/13, 22/19},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 15/13 < q < 22/19 && CoprimeQ[Denominator[q], 10]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {},
		"WordExceptionalRationals" -> {},
		"WordIntervalEndpoints" -> {15/13, 22/19},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 15/13 < q < 22/19 && CoprimeQ[Denominator[q], 10]],
		"WordStatus" -> "Conjecture"
	},
	(* 37 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 + 4*a - 5*b], Superscript[1, 1], Superscript[0, -1 - a + 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 + 5*a - 6*b], Superscript[1, 1], Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 + 4*a - 5*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 3*a + 4*b], Superscript[1, 1], Superscript[0, -1 + 5*a - 6*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 + 4*a - 5*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 2*a + 3*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 2, 1]]
		]],
		"LengthCoefficients" -> {24, -15},
		"LocatingLengthCoefficients" -> {2, 0},
		"NonzeroCharacterCount" -> 37,
		"SourceRationals" -> {76/59, 125/97, 107/83, 40/31, 71/55, 115/89, 84/65, 53/41, 22/17, 123/95, 79/61, 48/37, 61/47, 87/67, 95/73, 69/53, 56/43, 103/79, 30/23, 77/59, 111/85, 64/49, 17/13, 72/55, 127/97, 93/71, 38/29, 80/61, 46/35, 25/19, 54/41, 62/47, 33/25, 70/53, 78/59, 41/31, 86/65, 49/37, 57/43, 65/49, 73/55, 81/61},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {9/7, 4/3},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 9/7 < q < 4/3 && CoprimeQ[Denominator[q], 24]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {},
		"WordExceptionalRationals" -> {},
		"WordIntervalEndpoints" -> {9/7, 4/3},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 9/7 < q < 4/3 && CoprimeQ[Denominator[q], 24]],
		"WordStatus" -> "Theorem"
	},
	(* 38 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 19*a - 21*b], Superscript[1, 1], Superscript[0, -1 - 16*a + 18*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 16*a + 18*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 16*a + 18*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 16*a + 18*b], Superscript[1, 1], Superscript[0, -1 + 18*a - 20*b], Superscript[1, 1], Superscript[0, -1 - 16*a + 18*b], Superscript[1, 1], Superscript[0, -1 + 18*a - 20*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 16*a + 18*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 16*a + 18*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 16*a + 18*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {12, -7},
		"LocatingLengthCoefficients" -> {1, 0},
		"NonzeroCharacterCount" -> 38,
		"SourceRationals" -> {135/121, 48/43, 115/103, 153/137, 86/77},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {29/26},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {10/9, 19/17},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 10/9 < q < 19/17 && CoprimeQ[Denominator[q], 12]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {106/95},
		"WordExceptionalRationals" -> {106/95},
		"WordIntervalEndpoints" -> {29/26, 19/17},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 29/26 < q < 19/17 && q != 106/95 && CoprimeQ[Denominator[q], 12]],
		"WordStatus" -> "Conjecture"
	},
	(* 42 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 21*a - 23*b], Superscript[1, 1], Superscript[0, -1 - 18*a + 20*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 9*a + 10*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 18*a + 20*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 18*a + 20*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 18*a + 20*b], Superscript[1, 1], Superscript[0, -1 + 20*a - 22*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 18*a + 20*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 18*a + 20*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 18*a + 20*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 21*a - 23*b], Superscript[1, 1], Superscript[0, -1 - 19*a + 21*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {13, -8},
		"LocatingLengthCoefficients" -> {1, 0},
		"NonzeroCharacterCount" -> 42,
		"SourceRationals" -> {76/69, 65/59, 54/49},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {32/29},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {11/10, 21/19},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 11/10 < q < 21/19 && q != 32/29 && CoprimeQ[Denominator[q], 13]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {74/67},
		"WordExceptionalRationals" -> {32/29, 74/67},
		"WordIntervalEndpoints" -> {11/10, 21/19},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 11/10 < q < 21/19 && q != 32/29 && q != 74/67 && CoprimeQ[Denominator[q], 13]],
		"WordStatus" -> "Conjecture"
	},
	(* 46 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 - 9*a + 10*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 13*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 20*a + 22*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 13*b], Superscript[1, 1], Superscript[0, -1 - 20*a + 22*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 24*a - 26*b], Superscript[1, 1], Superscript[0, -1 - 20*a + 22*b], Superscript[1, 1], Superscript[0, -1 + 22*a - 24*b], Superscript[1, 1], Superscript[0, -1 - 20*a + 22*b], Superscript[1, 1], Superscript[0, -1 + 22*a - 24*b], Superscript[1, 1], Superscript[0, -1 - 20*a + 22*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 13*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 11*b], Superscript[1, 1], Superscript[0, -1 - 9*a + 10*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 23*a - 25*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 20*a + 22*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 12*a - 13*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 20*a + 22*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 13*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 13*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 13*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 13*b], Superscript[1, 1], Superscript[0, -1 - 20*a + 22*b], Superscript[1, 1], Superscript[0, -1 + 22*a - 24*b], Superscript[1, 1], Superscript[0, -1 - 9*a + 10*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {14, -9},
		"LocatingLengthCoefficients" -> {10, -10},
		"NonzeroCharacterCount" -> 46,
		"SourceRationals" -> {71/65, 106/97, 47/43, 93/85, 58/53, 104/95},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {35/32},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {12/11, 23/21},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 12/11 < q < 23/21 && CoprimeQ[Denominator[q], 14]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {82/75},
		"WordExceptionalRationals" -> {95/87, 82/75},
		"WordIntervalEndpoints" -> {12/11, 23/21},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 12/11 < q < 23/21 && q != 82/75 && q != 95/87 && CoprimeQ[Denominator[q], 14]],
		"WordStatus" -> "Conjecture"
	},
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 33*a - 36*b], Superscript[1, 1], Superscript[0, -1 - 30*a + 33*b], Superscript[1, 1], Superscript[0, -1 + 22*a - 24*b], Superscript[1, 1], Superscript[0, -1 - 20*a + 22*b], Superscript[1, 1], Superscript[0, -1 + 22*a - 24*b], Superscript[1, 1], Superscript[0, -1 - 20*a + 22*b], Superscript[1, 1], Superscript[0, -1 + 22*a - 24*b], Superscript[1, 1], Superscript[0, -1 - 20*a + 22*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 22*a - 24*b], Superscript[1, 1], Superscript[0, -1 - 30*a + 33*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 22*a - 24*b], Superscript[1, 1], Superscript[0, -1 - 30*a + 33*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 22*a - 24*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 19*a + 21*b], Superscript[1, 1], Superscript[0, -1 + 22*a - 24*b], Superscript[1, 1], Superscript[0, -1 - 30*a + 33*b], Superscript[1, 1], Superscript[0, -1 + 32*a - 35*b], Superscript[1, 1], Superscript[0, -1 - 30*a + 33*b], Superscript[1, 1], Superscript[0, -1 + 32*a - 35*b], Superscript[1, 1], Superscript[0, -1 - 30*a + 33*b], Superscript[1, 1], Superscript[0, -1 + 32*a - 35*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 30*a + 33*b], Superscript[1, 1], Superscript[0, -1 + 22*a - 24*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 30*a + 33*b], Superscript[1, 1], Superscript[0, -1 + 22*a - 24*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 30*a + 33*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {14, -9},
		"LocatingLengthCoefficients" -> {1, 0},
		"NonzeroCharacterCount" -> 46,
		"SourceRationals" -> {80/73, 91/83},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {57/52},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {23/21, 34/31},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 23/21 < q < 34/31 && CoprimeQ[Denominator[q], 14]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> Missing["Unknown"],
		"WordExceptionalRationals" -> Missing["Unknown"],
		"WordIntervalEndpoints" -> Missing["Unknown"],
		"WordRationalTest" -> Missing["Unknown"],
		"WordStatus" -> None
	},
	(* 54 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 25*a - 28*b], Superscript[1, 1], Superscript[0, -1 - 22*a + 25*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 22*a + 25*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 22*a + 25*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 6*a + 7*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 22*a + 25*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 22*a + 25*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 22*a + 25*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 6*a + 7*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 22*a + 25*b], Superscript[1, 1], Superscript[0, -1 + 24*a - 27*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 22*a + 25*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 22*a + 25*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 22*a + 25*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {13, -5},
		"LocatingLengthCoefficients" -> {1, 0},
		"NonzeroCharacterCount" -> 54,
		"SourceRationals" -> {107/95, 98/87, 89/79, 80/71, 71/63, 62/55, 53/47, 97/86, 79/70, 114/101, 131/116, 96/85, 61/54, 87/77, 113/100},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {35/31},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {9/8, 26/23},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 9/8 < q < 26/23 && q != 35/31 && CoprimeQ[Denominator[q], 13]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {},
		"WordExceptionalRationals" -> {35/31},
		"WordIntervalEndpoints" -> {9/8, 26/23},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 9/8 < q < 26/23 && q != 35/31 && CoprimeQ[Denominator[q], 13]],
		"WordStatus" -> "Conjecture"
	},
	(* 102 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 - 7*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 10*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 11*a + 14*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 10*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 13*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 14*a - 17*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 13*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 15*a - 18*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 14*a - 17*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 13*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 14*a - 17*b], Superscript[1, 1], Superscript[0, -1 - 11*a + 14*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 15*a - 18*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 10*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 12*a + 15*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 11*b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {38, -15},
		"LocatingLengthCoefficients" -> {2, 0},
		"NonzeroCharacterCount" -> 102,
		"SourceRationals" -> {104/85, 82/67, 60/49, 109/89, 87/71, 38/31, 65/53, 92/75, 119/97, 97/79, 43/35, 102/83, 134/109, 75/61, 198/161, 139/113, 171/139},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {27/22},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {11/9, 16/13},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 11/9 < q < 16/13 && CoprimeQ[Denominator[q], 38]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {107/87},
		"WordExceptionalRationals" -> {107/87},
		"WordIntervalEndpoints" -> {11/9, 16/13},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 11/9 < q < 16/13 && q != 107/87 && CoprimeQ[Denominator[q], 38]],
		"WordStatus" -> "Conjecture"
	},
	(* 158 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 13*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 13*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 6*a + 7*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 16*a - 18*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 15*a + 17*b], Superscript[1, 1], Superscript[0, -1 + 17*a - 19*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 6*a + 7*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 16*a - 18*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 16*a - 18*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 15*a + 17*b], Superscript[1, 1], Superscript[0, -1 + 17*a - 19*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 16*a - 18*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 16*a - 18*b], Superscript[1, 1], Superscript[0, -1 - 13*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 17*a - 19*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 16*a - 18*b], Superscript[1, 1], Superscript[0, -1 - 13*a + 15*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 - 6*a + 7*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 17*a - 19*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 - 6*a + 7*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 14*a + 16*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[n + 2, 1]]
		]],
		"LengthCoefficients" -> {53, -30},
		"LocatingLengthCoefficients" -> {8, -7},
		"NonzeroCharacterCount" -> 158,
		"SourceRationals" -> {95/84, 69/61, 112/99, 43/38, 103/91, 77/68, 94/83, 111/98},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {26/23},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {9/8, 17/15},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 9/8 < q < 17/15 && q != 26/23 && CoprimeQ[Denominator[q], 53]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {},
		"WordExceptionalRationals" -> {},
		"WordIntervalEndpoints" -> {26/23, 17/15},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 26/23 < q < 17/15 && CoprimeQ[Denominator[q], 53]],
		"WordStatus" -> "Conjecture"
	},
	(* 191 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 4*a + 5*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 - 4*a + 5*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 5*a + 6*b], Superscript[1, 1], Superscript[0, -1 + 6*a - 7*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 9*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 - 5*a + 6*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 - 9*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 14*b], Superscript[1, 1], Superscript[0, -1 - 9*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 13*a - 15*b], Superscript[1, 1], Superscript[0, -1 - 9*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 5*a + 6*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 6*a - 7*b], Superscript[1, 1], Superscript[0, -1 - 4*a + 5*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 9*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 5*a + 6*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 9*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 13*a - 15*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 5*a + 6*b], Superscript[1, 1], Superscript[0, -1 - 4*a + 5*b], Superscript[1, 1], Superscript[0, -1 + 13*a - 15*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 4*a + 5*b], Superscript[1, 1], Superscript[0, -1 + 13*a - 15*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 14*b], Superscript[1, 1], Superscript[0, -1 - 11*a + 13*b], Superscript[1, 1], Superscript[0, -1 + 13*a - 15*b], Superscript[1, 1], Superscript[0, -1 - 3*a + 4*b], Superscript[1, 1], Superscript[0, -1 - 9*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 14*b], Superscript[1, 1], Superscript[0, -1 - 11*a + 13*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 9*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 14*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 9*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 12*a - 14*b], Superscript[1, 1], Superscript[0, -1 - 9*a + 11*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 9*a + 11*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 13*a - 15*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 5*a + 6*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 8*a - 9*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 6*a - 7*b], Superscript[1, 1], Superscript[0, -1 - 3*a + 4*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 3*a + 4*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 5*a + 6*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 7*a - 8*b], Superscript[1, 1], Superscript[0, -1 - 10*a + 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[n + 2, 1]]
		]],
		"LengthCoefficients" -> {66, -28},
		"LocatingLengthCoefficients" -> {2, 0},
		"NonzeroCharacterCount" -> 191,
		"SourceRationals" -> {104/89, 48/41, 112/95, 72/61},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {},
		"PowerFreeExceptionalRationals" -> {20/17},
		"PowerFreeIntervalEndpoints" -> {7/6, 13/11},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 7/6 < q < 13/11 && q != 20/17 && CoprimeQ[Denominator[q], 66]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> Missing["Unknown"],
		"WordExceptionalRationals" -> Missing["Unknown"],
		"WordIntervalEndpoints" -> Missing["Unknown"],
		"WordRationalTest" -> Missing["Unknown"],
		"WordStatus" -> None
	},
	(* 279 nonzero characters *)
	{
		"Morphism" -> Function[q, With[{a = Numerator[q], b = Denominator[q]},
			n_ :> SymbolicWord[Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 26*a + 29*b], Superscript[1, 1], Superscript[0, -1 + 28*a - 31*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 24*a + 27*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 27*a - 30*b], Superscript[1, 1], Superscript[0, -1 - 24*a + 27*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 28*a - 31*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 27*a - 30*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 27*a - 30*b], Superscript[1, 1], Superscript[0, -1 - 24*a + 27*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 28*a - 31*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 27*a - 30*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 26*a + 29*b], Superscript[1, 1], Superscript[0, -1 + 28*a - 31*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 27*a - 30*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[2, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 - 24*a + 27*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + 11*a - 12*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 2*a - 2*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 7*a + 8*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 8*a + 9*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 27*a - 30*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 10*a - 11*b], Superscript[1, 1], Superscript[0, -1 + 3*a - 3*b], Superscript[1, 1], Superscript[0, -1 - 25*a + 28*b], Superscript[1, 1], Superscript[0, -1 + a - b], Superscript[1, 1], Superscript[0, -1 + 9*a - 10*b], Superscript[n + 1, 1]]
		]],
		"LengthCoefficients" -> {67, -30},
		"LocatingLengthCoefficients" -> {5, -4},
		"NonzeroCharacterCount" -> 279,
		"SourceRationals" -> {99/89, 79/71, 59/53, 108/97, 88/79, 146/131, 68/61, 97/87, 126/113, 155/139},
		(* a/b-power-freeness properties *)
		"LocatingLengthExceptionalRationals" -> {39/35},
		"PowerFreeExceptionalRationals" -> {},
		"PowerFreeIntervalEndpoints" -> {10/9, 29/26},
		"PowerFreeRationalTest" -> Function[q, Element[q, Rationals] && 10/9 < q < 29/26 && q != 39/35 && CoprimeQ[Denominator[q], 67]],
		(* conjectural or proved relationships to lexicographically least a/b-power-free words *)
		"WordAdditionalRationals" -> {89/80, 49/44},
		"WordExceptionalRationals" -> {89/80, 69/62, 49/44, 39/35},
		"WordIntervalEndpoints" -> {10/9, 29/26},
		"WordRationalTest" -> Function[q, Element[q, Rationals] && 10/9 < q < 29/26 && q != 39/35 && q != 49/44 && q != 69/62 && q != 89/80 && CoprimeQ[Denominator[q], 67]],
		"WordStatus" -> "Conjecture"
	}
}

End[]

Protect["SymbolicWords`*"]

EndPackage[]
