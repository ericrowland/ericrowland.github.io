(* ::Package:: *)

(* :Title: Cellular Automaton Boundaries *)

(* :Context: CellularAutomatonBoundaries` *)

(* :Author: Charles Brummitt and Eric Rowland *)

(* :Date: {2015, 10, 7} *)

(* :Package Version: 1.02 *)

(* :Mathematica Version: 8 *)

(* :Discussion:
	CellularAutomatonBoundaries is a collection of tools for studying boundaries of one-dimensional cellular automata.
	Documentation can be found at  http://people.hofstra.edu/Eric_Rowland/packages.html .
*)


BeginPackage["CellularAutomatonBoundaries`"]

CellularAutomatonBoundaries`Private`$SymbolList = {
	CreateIrregularBoundaryData,
	CreateRegularBoundaryData,
	IrregularBoundaryData,
	RegularBoundaryData,
	$CellularAutomatonDataDirectory
}


Unprotect["CellularAutomatonBoundaries`*"]

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


CreateIrregularBoundaryData::usage =
box[CreateIrregularBoundaryData["k", "d", "automata"]] <> " creates irregluar boundary CellularAutomatonData for " <> box["k"] <> "\[Hyphen]color rules depending on " <> box["d"] <> " cells listed in " <> box["automata"] <> "."

CreateRegularBoundaryData::usage =
box[CreateRegularBoundaryData["k", "d"]] <> " creates regular boundary CellularAutomatonData for " <> box["k"] <> "\[Hyphen]color rules depending on " <> box["d"] <> " cells."

IrregularBoundaryData::usage =
box[IrregularBoundaryData[{{"n", "k", "r"}, "init", Subscript["t", "max"]}, String["property"]]] <> " retrieves the value for the specified irregular boundary property for a cellular automaton."

RegularBoundaryData::usage =
box[RegularBoundaryData[{{"n", "k", "r"}, "init"}, String["property"]]] <> " retrieves the value for the specified regular boundary property for a cellular automaton."

$CellularAutomatonDataDirectory::usage =
"$CellularAutomatonDataDirectory gives the directory where CellularAutomatonData files are stored."

computeirregularboundary::usage =
box[irregularboundarydata["rule", "initialcondition", "tmax"]] <> " computes the best fits and random walk statistics of the boundary of the cellular " <>
"automaton and returns a dictionary with keys {\"BestFits\", \"Drift\", \"Diffusivity\", \"PecletNumber\", \"Randomness\"}."

getFits::usage =
box[getFits["boundary", "powerlawcutoff"]] <> " computes the best fits of the boundary to linear (a + b t), power law (a t^b and a t^b + c), and logarithmic (a Log[b t] + c) " <>
"expressions, keeping Logarithmic only if NonlinearModelFit doesn't return Missing[] and only those power law fits with exponent b satisfying |b-1| > powerlawcutoff. It returns a dictionary with keys "<>
"{\"Linear\", \"Power(2)\", \"Power(3)\", \"Logarithimic\"}";


CachedImport[filename_] := CachedImport[filename] = Import[filename]

CanonicalRotation[list_] :=
	FirstSortedElement[NestList[RotateLeft, list, Length[list] - 1]]

ColorCycles[{n_, k_, r_}] :=
Module[{graph},
	graph = IntegerDigits[n, k, k^(2 r + 1)][[k^(2 r + 1) - (k^(2 r + 1) - 1)/(k - 1) Range[0, k - 1]]];
	Union[Table[CanonicalRotation[FixedPointPeriod[graph[[# + 1]] &, i]], {i, 0, k - 1}]]
]

FirstSortedElement[list : _[__]] :=
	list[[First[Ordering[list, 1]]]]

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

(* This EquivalentRules includes left-right reflections. *)
EquivalentRules[{n_, k_, r_}] :=
With[{ruletable = RuleTable[{n, k, r}]},
	Union @@ Function[perm,
		With[{permuted = ruletable /. Thread[Range[0, k - 1] -> perm]},
			(Last /@ Sort[#].k^Range[0, k^(2 r + 1) - 1] &) /@
				{permuted, {Reverse[#1], #2} & @@@ permuted}
		]
	] /@ Permutations[Range[0, k - 1]]
]

FixedPointPeriod[f_, expr_] :=
Module[{list = {expr}, val = expr, i = 0},
	While[! MemberQ[list, val = f[val], {1}],
		AppendTo[list, val];
		i++
	];
	Take[list, {Position[list, val, {1}, 1][[1, 1]], -1}]
]

IndentedExport[filename_, data_] :=
	Export[filename, ToIndentedString[data], "Text"]

PeriodLength[list_] :=
Module[{length = 1},
	While[Drop[list, length] != Drop[list, -length],
		length++
	];
	length
]

RuleTable[{n_, k_, r_}] :=
	Thread[Tuples[Range[0, k - 1], 2 r + 1] -> Reverse[IntegerDigits[n, k, k^(2 r + 1)]]]

StringPower[s_, n_] :=
	StringJoin[ConstantArray[s, n]]

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
ToIndentedString[rulelists : {{__Rule} ..}, n_ : 0] :=
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

UnpadLength[list_, p_] :=
With[{first = Position[list, Except[p], {1}, 1, Heads -> False]},
	If[first == {},
		0,
		Plus[
			Length[list],
			-first[[1, 1]],
			-Position[Reverse[list], Except[p], {1}, 1, Heads -> False][[1, 1]],
			2
		]
	]
]


regularboundarydata[rule_, initialcondition_, {tmin_, tmax_}] :=
Module[{differencesequence, periodlength},
	differencesequence = Differences[
		UnpadLength[#, First[#]] & /@
			(* This All doesn't seem to slow things down as long as tmax is less than a few thousand. *)
			CellularAutomaton[rule, initialcondition, {{tmin, tmax}, All}]
	];
	periodlength = PeriodLength[differencesequence];
	If[periodlength < (tmax - tmin)/4,
		{
			"BoundaryWordPeriodLength" -> periodlength,
			"GrowthRate" -> Total[Take[differencesequence, periodlength]]/periodlength
		},
		Missing["Unknown"]
	]
]

computeirregularboundary[rule_, initialcondition_, tmax_] :=
Module[{differencesequence, D, U, Peclet, randomness},
	differencesequence = Differences[
		UnpadLength[#, First[#]] & /@
			(* This All doesn't seem to slow things down as long as tmax is less than a few thousand. *)
			CellularAutomaton[rule, initialcondition, {{0, tmax}, All}]
	];
	
	U = N@Total[Most@differencesequence] / (Length[differencesequence]-1);
		(* old definition: N@Mean[differencesequence/Range[Length[differencesequence]]];*)
	D = N@Variance[Most@Differences@differencesequence]; (* We use Most because sometimes the last element of differencesequence is really big *)
	Peclet = Quiet[Abs[U]/D,Power::infy];
	randomness = Quiet[D/Abs[U],Power::infy];
	

	{"BestFits"-> getFits[differencesequence],
	"Drift"-> U, "Diffusivity" -> D, "PecletNumber" -> Peclet, "Randomness" -> randomness}
]


getFits[boundary_List, powerlawcutoff_:0.01]:=
Module[{linFit, powerFit1, powerFit2, logFit, results, allFits, minAIC, resultFunction, mostBoundary},
	mostBoundary = Most[boundary];
	linFit = LinearModelFit[mostBoundary,t,t];
	powerFit1 = NonlinearModelFit[mostBoundary,{a t^b},{a,b},t];
	powerFit2 = NonlinearModelFit[mostBoundary,{a t^b+c},{a,b,c},t];
	logFit = Check[NonlinearModelFit[mostBoundary,{a Log[b t]+c},{a,b,c},t],Missing[],{NonlinearModelFit::nrlnum}];

	allFits={linFit, powerFit1, powerFit2, logFit};
	minAIC=Min[#["AIC"]&/@Select[allFits,FreeQ[#,Missing[]]&]];

	resultFunction[whichFit_, name_, minAICinput_, exponent_]:=
		{"FitName" -> name,
		"Fit" -> Normal[whichFit],
		"AdjustedRSquared" ->  whichFit["AdjustedRSquared"],
		"AIC" -> whichFit["AIC"],
		(*"AICc"-> linFit["AIC"]+(2 k (k+1))/(n-k-1)/.{k->2,n->Length[boundary]},*)
		(*AIC is already corrected for finite sample size, so we don't need AICc*)
		"ProbMinInfoLoss"->Exp[(minAICinput-whichFit["AIC"])/2],
		"Exponent" -> exponent};

	(*Always include a linear fit*)
	results = {resultFunction[linFit, "Linear", minAIC, 1]};

	(*If the power law fit a t^b has exponent t^b with |b-1|>powerlawcutoff
		and if no super small numbers appear in the fit (< 10^-10)
		then include the power law fit*)
	If[Abs[(b/.powerFit1["BestFitParameters"])-1]>=powerlawcutoff && Normal[powerFit1]==Chop[Normal[powerFit1]],
		AppendTo[results,resultFunction[powerFit1,"Power(2)", minAIC, (b/.powerFit1["BestFitParameters"])]]];

	(*If the power law fit a t^b + c has |b-1|>powerlawcutoff, include it*)
	If[Abs[(b/.powerFit2["BestFitParameters"])-1]>=powerlawcutoff,
		AppendTo[results,resultFunction[powerFit2,"Power(3)", minAIC, (b/.powerFit2["BestFitParameters"])]]];

	(*If the logarithmic fit a Log[b t]+c does not create Missing[] errors, include it*)
	If[FreeQ[logFit,Missing[]],
		AppendTo[results,resultFunction[logFit,"Log", minAIC, Missing["NotAvailable"]]]];

	(*Sort fits by R^2*Exp[-(minAIC-AIC)/2]*)
	Sort[results,("AdjustedRSquared"/.Rest@#1)*("ProbMinInfoLoss"/.Rest@#1)>("AdjustedRSquared"/.Rest@#2)*("ProbMinInfoLoss"/.Rest@#2)&]
]


General::nodir = "$CellularAutomatonDataDirectory is not a valid directory."

CreateIrregularBoundaryData[k_, d_, rulesandinitialconditions_, OptionsPattern[]] :=
Module[
	{
		filename = OptionValue["FileName"],
		tmax = OptionValue["TimeSpec"],
		n,
		initialcondition,
		newdata,
		gooddirectoryQ = True
	},
	Catch[
		If[MatchQ[filename, Automatic | _String] && !(StringQ[$CellularAutomatonDataDirectory] && DirectoryQ[$CellularAutomatonDataDirectory]),
			gooddirectoryQ = False; Throw[{}]
		];
		If[filename === Automatic,
			filename = "IrregularBoundary-" <> ToString[k] <> "-" <> ToString[d] <> "-" <> ToString[tmax] <> ".m"
			(*,
			If[MemberQ[{All, "UnpredictableAutomata", "IrregularAutomata", "NewAutomata"}, rulenumbers],
				filename = "IrregularBoundary-" <> ToString[k] <> "-" <> ToString[d] <> "-generated.m",
				(*"UnpredictableAutomata"|"IrregularAutomata"|"NewAutomata",
				filename = "IrregularBoundary-" <> ToString[k] <> "-" <> ToString[d] <> "-newautomata-generated.m",
				True,*)
				goodfilenameQ = False; Throw[{}]
			]*)
		];
		Quiet[
			newdata = Reap[
				Do[
					n = First[ruleinit];
					initialcondition = Last[ruleinit];
					If[n == First[EquivalentRules[{n, k, (d - 1)/2}]],
						Sow[{n, initialcondition} ->
							 computeirregularboundary[
										{n, k, (d - 1)/2},
										{Prepend[#1, #2], #2} & @@ initialcondition,
										tmax
									]
						]
					],
					{ruleinit, rulesandinitialconditions}
				]
			][[2, 1]]
		,{NonlinearModelFit::cvmit, NonlinearModelFit::nrlnum, FittedModel::bdfit, NonlinearModelFit::sszero}]
	];
	If[StringQ[filename],
		filename = FileNameJoin[{$CellularAutomatonDataDirectory, filename}];
		IndentedExport[filename, newdata]
		,
		newdata
	] /; gooddirectoryQ || Message[CreateIrregularBoundaryData::nodir]
]
Options[CreateIrregularBoundaryData] = {
	"FileName" -> Automatic,
	"TimeSpec" -> 500
}
SyntaxInformation[CreateIrregularBoundaryData] = {"ArgumentsPattern" -> {_, _, _, OptionsPattern[]}}

CreateRegularBoundaryData[k_, d_, OptionsPattern[]] :=
Module[
	{
		filename = OptionValue["FileName"],
		initialconditionspec = OptionValue["InitialCondition"],
		rulenumbers = OptionValue["RuleNumbers"],
		explicitrulenumbersQ = ListQ[OptionValue["RuleNumbers"]],
		timespecs = OptionValue["TimeSpecs"],
		initialconditions,
		tspecs,
		data,
		newdata,
		gooddirectoryQ = True,
		goodfilenameQ = True
	},
	Catch[
		If[MatchQ[filename, Automatic | _String] && !(StringQ[$CellularAutomatonDataDirectory] && DirectoryQ[$CellularAutomatonDataDirectory]),
			gooddirectoryQ = False; Throw[{}]
		];
		If[filename === Automatic,
			If[rulenumbers === All,
				filename = ToString[k] <> "-" <> ToString[d] <> "-generated.m",
				goodfilenameQ = False; Throw[{}]
			]
		];
		newdata = Reap[
			Do[
				If[explicitrulenumbersQ || n == EquivalentRuleRelationships[{n, k, (d - 1)/2}][[1, 1]],
					initialconditions = Switch[initialconditionspec,
						"SingleCell",
							Join @@ Function[backgroundcolor,
								Function[cellcolor, {{cellcolor}, backgroundcolor}] /@
									DeleteCases[Range[0, k - 1], backgroundcolor]
							] /@ Join @@ ColorCycles[{n, k, (d - 1)/2}],
						{__Integer},
							Function[backgroundcolor, {initialconditionspec, backgroundcolor}] /@
								Join @@ ColorCycles[{n, k, (d - 1)/2}],
						{{__Integer}, _Integer},
							{initialconditionspec},
						{{{__Integer}, _Integer} ..},
							initialconditionspec,
						_,
							{}
					];
					Sow[n ->
						Table[
							tspecs = timespecs;
							data = Missing["Unknown"];
							While[MatchQ[data, _Missing] && tspecs != {},
								data = regularboundarydata[
									{n, k, (d - 1)/2},
									{Prepend[#1, #2], #2} & @@ initialcondition,
									First[tspecs]
								];
								tspecs = Rest[tspecs]
							];
							initialcondition -> data
							,
							{initialcondition, initialconditions}
						]
					]
				],
				Evaluate[Replace[rulenumbers, {
					All :> {n, 0, k^k^d - 1},
					Interval[{nmin_, nmax_}] :> {n, nmin, nmax},
					numbers_List :> {n, numbers},
					number_Integer :> {n, {number}},
					_ :> {n, {}}
				}]]
			]
		][[2, 1]]
	];
	If[StringQ[filename],
		filename = FileNameJoin[{$CellularAutomatonDataDirectory, filename}];
		IndentedExport[filename, newdata]
		,
		newdata
	] /; And[
		gooddirectoryQ || Message[CreateRegularBoundaryData::nodir],
		goodfilenameQ || Message[CreateRegularBoundaryData::filename]
	]
]
Options[CreateRegularBoundaryData] = {
	"FileName" -> Automatic,
	"InitialCondition" -> "SingleCell",
	"RuleNumbers" -> All,
	"TimeSpecs" -> {{20, 100}, {50, 300}, {200, 600}, {400, 1000}}
}
SyntaxInformation[CreateRegularBoundaryData] = {"ArgumentsPattern" -> {_, _, OptionsPattern[]}}
CreateRegularBoundaryData::filename = "No FileName specified."

(* Note that this retrieves data only for an explicit automaton and not the minimal equivalent automaton. *)
IrregularBoundaryData[{{n_, k_, r_}, initialcondition_, time_}, property_] /;
	(StringQ[$CellularAutomatonDataDirectory] && DirectoryQ[$CellularAutomatonDataDirectory]) || Message[IrregularBoundaryData::nodir] :=
	property /. ({n, initialcondition} /.
		Import[FileNameJoin[{$CellularAutomatonDataDirectory, "IrregularBoundary-" <> ToString[k] <> "-" <> ToString[2 r + 1] <> "-" <> ToString[time] <> ".m"}]]
	)
SyntaxInformation[IrregularBoundaryData] = {"ArgumentsPattern" -> {{{_, _, _}, _, _}, _}}

RegularBoundaryData[{{n_, k_, r_}, {foreground_List, backgroundcolor_Integer}}, property_] /;
	(StringQ[$CellularAutomatonDataDirectory] && DirectoryQ[$CellularAutomatonDataDirectory]) || Message[RegularBoundaryData::nodir] :=
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
				CachedImport[FileNameJoin[{$CellularAutomatonDataDirectory, ToString[k] <> "-" <> ToString[2 r + 1] <> "-generated.m"}]]
			],
			_ -> Missing["NotAvailable"]
		]
	];
	If[MatchQ[initialconditiondata, _Missing],
		initialconditiondata
		,
		propertyvalue = Replace[
			property,
			Append[
				initialconditiondata,
				_ -> Missing["NotAvailable"]
			]
		];
		If[MatchQ[propertyvalue, _Missing],
			Switch[{property, initialconditiondata},
				{"Exponent", {___, "BoundaryWordPeriodLength" -> _Integer, ___, "GrowthRate" -> 0, ___}},
					0,
				{"Exponent", {___, "GrowthRate" -> Except[0], ___}},
					1,
				_,
					propertyvalue
			],
			propertyvalue
		]
	]
]
SyntaxInformation[RegularBoundaryData] = {"ArgumentsPattern" -> {{{_, _, _}, _}, _}}


End[]

Protect["CellularAutomatonBoundaries`*"]
Unprotect[$CellularAutomatonDataDirectory]

EndPackage[]
