(* :Title: Integer Sequences *)

(* :Context: IntegerSequences` *)

(* :Author: Eric Rowland *)

(* :Date: {2019, 10, 12} *)

(* :Package Version: 1.52 *)

(* :Mathematica Version: 12 *)

(* :Discussion:
	IntegerSequences is a package for identifying and computing with integer sequences from a variety of classes.
	It is available from  https://github.com/ericrowland/IntegerSequences .
	Documentation can be found at  https://ericrowland.github.io/packages.html .
*)

(* :Acknowledgements:
	Discussions with Reem Yassawi were instrumental in implementing many of the algorithms in this package.
	The code for AutomatonDeterminize was adapted from Michel Rigo's package EAT: http://www.discmath.ulg.ac.be/publi.html#eat
*)

BeginPackage["IntegerSequences`"]

(* If appropriate, new symbols should also be added to the appropriate down value of SequenceNumerationSystemList. *)
IntegerSequences`Private`$SymbolList = {
	AlgebraicSequence,
	AlgebraicSequenceReduce,
	AperyNumber,
	AutomaticSequence,
	AutomaticSequenceAutomaton,
	AutomaticSequenceReduce,
	Automaton,
	AutomatonAdjacencyMatrix,
	AutomatonDeterminize,
	AutomatonGraph,
	AutomatonInputAlphabet,
	AutomatonMinimize,
	AutomatonOutputAlphabet,
	AutomatonOutputRules,
	AutomatonProduct,
	AutomatonQ,
	AutomatonReverse,
	AutomatonStateCount,
	AutomatonStateList,
	BaumSweet,
	Cartier,
	CauchyProduct,
	ClearMotzkinNumberCache,
	CompleteAutomatonQ,
	CompressStateNames,
	ConstantTermSequence,
	ConstantTermSequenceReduce,
	DeterministicAutomatonQ,
	DiagonalSequence,
	DiagonalSequenceReduce,
	DigitGet,
	DigitList,
	DigitsCount,
	ExponentialFit,
	FactorForm,
	FactorGrid,
	FindAutomaticSequenceAutomaton,
	FindAutomaticSequenceFunction,
	FindAutomaticSequenceRecurrence,
	FindPolynomial,
	FindQuasiPolynomial,
	FindRegularSequenceFunction,
	FindRegularSequenceRecurrence,
	FlattenInputAlphabet,
	FromCoefficientList,
	FromDigitList,
	FromRecurrence,
	GatherEdges,
	GeneratingFunctionRelations,
	HashStateNames,
	ImportMotzkinNumber,
	IndexedStateNames,
	InputAlphabet,
	IntegerPrepend,
	IntermediateFunction,
	JacobsthalNumber,
	LaurentPolynomialCoefficientList,
	LeadingZeros,
(*
	LinearNumerationSystem,
	LinearNumerationSystemQ,
*)
(*
	LinearRecurrenceTable,
*)
	MaxDenominator,
	MorphicSequence,
	MorphicSequenceReduce,
	MorphismAdjacencyMatrix,
	MorphismPower,
	MotzkinNumber,
(*
	OEISData,
	OEISSequence,
*)
	OEISWebLookup,
	OrePolynomial,
	Radical,
	ReduceAutomaton,
	RegularSequence,
	RegularSequenceGeneratorTable,
	RegularSequenceMatrixForm,
	RegularSequenceMatrixLength,
	RegularSequenceRecurrence,
	RegularSequenceReduce,
	SequenceComplexity,
	SequenceRiffle,
	SeriesRoot,
	SeriesSolve,
	StateStorage,
	SternBrocot,
(*
	SynchronizedSequence,
*)
	TransitionSequence,
	Tribonacci,
	$CacheMotzkinNumbers,
	$MotzkinNumberDirectory
}


Unprotect["IntegerSequences`*"]

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


AlgebraicSequence::usage =
box[AlgebraicSequence[SeriesRoot[{"f", Subscript["y", 0]}]]["n"]] <> " gives the " <> box["n"] <> "th coefficient in the power series solution " <> box["y"] <> " of the equation " <> box["f"["y"] == 0] <> " approximated by " <> box[Subscript["y", 0]] <> ".\n" <>
box[AlgebraicSequence["f", "x"]["n"]] <> " uses " <> box[Subscript["y", 0] = 0 + O["x"]^1] <> "."
(*
box[AlgebraicSequence["f", SubscriptList["x", {1, 2, "...", "d"}]][SubscriptSequence["n", {1, 2, "...", "d"}]]] <> " gives the coefficient of a " <> box["d"] <> "\[Hyphen]dimensional algebraic sequence."
*)

AlgebraicSequenceReduce::usage =
box[AlgebraicSequenceReduce["expr", "n"]] <> " attempts to reduce " <> box["expr"] <> " to a single AlgebraicSequence object as a function of " <> box["n"] <> "."

AperyNumber::usage =
box[AperyNumber["n"]] <> " gives the " <> box["n"] <> "th Ap\[EAcute]ry number " <> box[Subscript["A", "n"]] <> "."

AutomaticSequence::usage =
box[AutomaticSequence["M", "k"]["n"]] <> " evaluates an automaton " <> box["M"] <> " on the base\[Hyphen]" <> box["k"] <> " digits of " <> box["n"] <> ", starting with the least significant digit.\n" <>
box[AutomaticSequence["M", SubscriptList["k", {1, 2, "...", "d"}]][SubscriptSequence["n", {1, 2, "...", "d"}]]] <> " gives the value of a " <> box["d"] <> "\[Hyphen]dimensional (" <> box[SubscriptSequence["k", {1, 2, "...", "d"}]] <> ")\[Hyphen]automatic sequence.\n" <>
box[AutomaticSequence["M"]["n"]] <> " infers the base " <> box["k"] <> " from " <> box["M"] <> "."

AutomaticSequenceAutomaton::usage =
box[AutomaticSequenceAutomaton[AutomaticSequence["M", "k"]["n"]]] <> " extracts the automaton from an AutomaticSequence object."

AutomaticSequenceReduce::usage =
box[AutomaticSequenceReduce["expr", "n"]] <> " attempts to reduce " <> box["expr"] <> " to a single AutomaticSequence object as a function of " <> box["n"] <> "."
(*
box[AutomaticSequenceReduce["expr", "n", "k"]] <> " attempts to reduce " <> box["expr"] <> " to a " <> box["k"] <> "\[Hyphen]automatic sequence."
*)

Automaton::usage =
box[Automaton[{"\[Ellipsis]", {Subscript["s", "i"] -> Subscript["s", "j"], "label"}, "\[Ellipsis]"}, "init"]] <> " represents an automaton with initial state " <> box["init"] <> " and labeled transition rules " <> box[Subscript["s", "i"] -> Subscript["s", "j"]] <> " between states.\n" <>
box[Automaton["rule", "init", {"\[Ellipsis]", Subscript["s", "i"] -> Subscript["v", "i"], "\[Ellipsis]"}]] <> " assigns the output " <> box[Subscript["v", "i"]] <> " to the state " <> box[Subscript["s", "i"]] <> ".\n" <>
box[Automaton["rule", SubscriptList["init", {1, 2, "..."}], "outputrules"]] <> " represents a non\[Hyphen]deterministic automaton with multiple initial states.\n" <>
box[Automaton["rule", "init", "outputrules"]["input"]] <> " gives the output corresponding to the state reached after transitioning according to the entries of the list " <> box["input"] <> "."

AutomatonAdjacencyMatrix::usage =
box[AutomatonAdjacencyMatrix["M"]] <> " gives the vertex\[Dash]vertex adjacency matrix of the automaton " <> box["M"] <> "."

AutomatonDeterminize::usage =
box[AutomatonDeterminize["M"]] <> " gives an automaton that, when fed " <> box["list"] <> ", outputs a list of all output values that can reached by traversing edges according to " <> box["list"] <> " in a non\[Hyphen]deterministic automaton " <> box["M"] <> ".\n" <>
box[AutomatonDeterminize["M", "f"]] <> " applies " <> box["f"] <> " to the determinized automaton's output lists."

AutomatonGraph::usage =
box[AutomatonGraph["M"]] <> " gives the directed graph of an automaton " <> box["M"] <> "."

AutomatonInputAlphabet::usage =
box[AutomatonInputAlphabet["M"]] <> " gives the input alphabet of an automaton " <> box["M"] <> "."

AutomatonMinimize::usage =
box[AutomatonMinimize["M"]] <> " gives a minimal automaton that agrees with " <> box["M"] <> " on all input."

AutomatonOutputAlphabet::usage =
box[AutomatonOutputAlphabet["M"]] <> " gives a list of possible output values of an automaton " <> box["M"] <> "."

AutomatonOutputRules::usage =
box[AutomatonOutputRules["M"]] <> " gives the replacement rules that assign states of an automaton " <> box["M"] <> " to their corresponding outputs."

AutomatonProduct::usage =
box[AutomatonProduct[Subscript["M", 1], Subscript["M", 2]]] <> " gives an automaton that outputs " <> box[{Subscript["M", 1]["list"], Subscript["M", 2]["list"]}] <> " when fed " <> box["list"] <> ".\n" <>
box[AutomatonProduct[Subscript["M", 1], Subscript["M", 2], "f"]] <> " gives an automaton that outputs " <> box["f"[{Subscript["M", 1]["list"], Subscript["M", 2]["list"]}]] <> " when fed " <> box["list"] <> "."

AutomatonQ::usage =
box[AutomatonQ["M"]] <> " yields True if " <> box["M"] <> " is a valid automaton object, and False otherwise."

AutomatonReverse::usage =
box[AutomatonReverse["M"]] <> " gives an automaton that computes " <> box["M"["input"]] <> " when fed " <> box[Reverse["input"]] <> "."

AutomatonStateCount::usage =
box[AutomatonStateCount["M"]] <> " gives the number of states in an automaton " <> box["M"] <> "."

AutomatonStateList::usage =
box[AutomatonStateList["M"]] <> " gives the list of states in an automaton " <> box["M"] <> "."

BaumSweet::usage =
box[BaumSweet["n"]] <> " gives the " <> box["n"] <> "th term in the Baum\[Dash]Sweet sequence."

Cartier::usage =
box[Cartier["poly", "vars", "m", "residues"]] <> " picks out the monomials of " <> box["poly"] <> " whose exponents are congruent to " <> box["residues"] <> " modulo " <> box["m"] <> " and quotients the exponents by " <> box["m"] <> "."

CauchyProduct::usage =
box[CauchyProduct[SubscriptList["a", {0, 1, "...", "k"}], SubscriptList["b", {0, 1, "...", "k"}]]] <> " gives the Cauchy product of two sequences."

ChristolPolynomial::usage =
box[ChristolPolynomial["M", {"x", "y"}]] <> " gives a polynomial satisfied modulo " <> box["p"] <> " by the generating function of the " <> box["p"] <> "\[Hyphen]automatic sequence generated by an automaton " <> box["M"] <> "."

ClearMotzkinNumberCache::usage =
box[ClearMotzkinNumberCache[]] <> " clears the cache of stored Motzkin numbers."

CompleteAutomatonQ::usage =
box[CompleteAutomatonQ["M"]] <> " yields True if " <> box["M"] <> " is an automaton where every state has at least one out\[Hyphen]transition for each letter of the input alphabet, and False otherwise."

CompressStateNames::usage =
"CompressStateNames is an option for AutomaticSequenceReduce that specifies whether to compress state names when possible so that equivalent states are more likely to have the same name."

ConstantTermSequence::usage =
box[ConstantTermSequence["f", "vars"]["n"]] <> " gives the constant term in the Laurent polynomial " <> box["f"^"n"] <> ".\n" <>
box[ConstantTermSequence["f", "g", "vars"]["n"]] <> " gives the constant term in " <> box["f"^"n" * "g"] <> "."

ConstantTermSequenceReduce::usage =
box[ConstantTermSequenceReduce["expr", "n"]] <> " attempts to reduce " <> box["expr"] <> " to a single ConstantTermSequence object as a function of " <> box["n"] <> "."

DeterministicAutomatonQ::usage =
box[DeterministicAutomatonQ["M"]] <> " yields True if " <> box["M"] <> " is a deterministic automaton, and False otherwise."

DiagonalSequence::usage =
box[DiagonalSequence["expr", "vars"]["n"]] <> " gives the " <> box["n"] <> "th diagonal coefficient in the power series expansion of the rational expression " <> box["expr"] <> ".\n" <>
box[DiagonalSequence["expr", SubscriptList["vars", {1, 2, "...", "d"}]][SubscriptSequence["n", {1, 2, "...", "d"}]]] <> " gives a value of the " <> box["d"] <> "\[Hyphen]dimensional diagonal obtained by collapsing each list of variables."

DiagonalSequenceReduce::usage =
box[DiagonalSequenceReduce["expr", "n"]] <> " attempts to reduce " <> box["expr"] <> " to a single DiagonalSequence object as a function of " <> box["n"] <> "."

DigitGet::usage =
box[DigitGet["n", "b", "i"]] <> " gives the coefficient of " <> box["b"^"i"] <> " in the base\[Hyphen]" <> box["b"] <> " representation of " <> box["n"] <> ".\n" <>
box[DigitGet["n", "B", "i"]] <> " gives the " <> box["i"] <> "th digit in the numeration system " <> box["B"] <> "."

DigitList::usage =
box[DigitList["n"]] <> " gives a list of the digits in the standard decimal representation of " <> box["n"] <> ", where successive digits increase in significance.\n" <>
box[DigitList["n", "b"]] <> " gives the standard base\[Hyphen]" <> box["b"] <> " representation of " <> box["n"] <> ".\n" <>
box[DigitList["n", SubscriptList["b", {0, 1, "...", "m"}]]] <> " uses the mixed radix with bases " <> box[SubscriptSequence["b", {0, 1, "...", "m"}]] <> ".\n" <>
box[DigitList["n", "B"]] <> " gives the canonical representation of " <> box["n"] <> " in the numeration system " <> box["B"] <> ".\n" <>
box[DigitList["n", "B", "len"]] <> " pads the list on the right with zeros to give a list of length " <> box["len"] <> "."

DigitsCount::usage =
box[DigitsCount["n", "b", "d"]] <> " gives the number of " <> box["d"] <> " digits in the standard base\[Hyphen]" <> box["b"] <> " representation of " <> box["n"] <> ".\n" <>
box[DigitsCount["n", "b", "digitlist"]] <> " gives the number of appearances of a block of digits in the standard base\[Hyphen]" <> box["b"] <> " representation of " <> box["n"] <> ", where successive digits increase in significance."

ExponentialFit::usage =
box[ExponentialFit["data", "x"]] <> " finds a least\[Hyphen]squares fit of the form " <> box["a" * "b"^"x"] <> " to a list of data.\n" <>
box[ExponentialFit["data", "x", "d"]] <> " indexes terms beginning at " <> box["d"] <> "."

FactorForm::usage =
box[FactorForm["n"]] <> " writes integers, rationals, and Gaussian integers as products of their prime factors."

FactorGrid::usage =
box[FactorGrid["list"]] <> " displays a grid containing the order to which all primes dividing at least one of the Gaussian rational numbers in " <> box["list"] <> " divide each.\n" <>
box[FactorGrid["list", "zero"]] <> " replaces each 0 in the table with " <> box["zero"] <> " rather than with Null."

FindAutomaticSequenceAutomaton::usage =
box[FindAutomaticSequenceAutomaton[SubscriptList["a", {0, 1, "..."}], "k"]] <> " attempts to find an automaton which reproduces the sequence " <> box[Subscript["a", "n"]] <> " when fed the base\[Hyphen]" <> box["k"] <> " digits of " <> box["n"] <> ", starting with the least significant digit.\n" <>
box[FindAutomaticSequenceAutomaton["array", SubscriptList["k", {1, 2, "...", "d"}]]] <> " finds an automaton which reproduces a " <> box["d"] <> "\[Hyphen]dimensional sequence in bases " <> box[SubscriptSequence["k", {1, 2, "...", "d"}]] <> "."

FindAutomaticSequenceFunction::usage =
box[FindAutomaticSequenceFunction[SubscriptList["a", {0, 1, "..."}], "k"]] <> " attempts to find a " <> box["k"] <> "\[Hyphen]automatic sequence which reproduces the sequence " <> box[Subscript["a", "n"]] <> ".\n" <>
box[FindAutomaticSequenceFunction["array", SubscriptList["k", {1, 2, "...", "d"}]]] <> " finds a " <> box["d"] <> "\[Hyphen]dimensional (" <> box[SubscriptSequence["k", {1, 2, "...", "d"}]] <> ")\[Hyphen]automatic sequence which reproduces a full array of values.\n" <>
box[FindAutomaticSequenceFunction["array", "kspec", "n"]] <> " gives the function applied to " <> box["n"] <> "."

FindAutomaticSequenceRecurrence::usage =
box[FindAutomaticSequenceRecurrence[SubscriptList["a", {0, 1, "..."}], "k", "s"["n"]]] <> " attempts to find equalities between subsequences of the sequence " <> box[Subscript["a", "n"]] <> " of the form " <> box["s"["k"^"e" * "n" + "i"]] <> " that determine the sequence.\n" <>
box[FindAutomaticSequenceRecurrence["array", SubscriptList["k", {1, 2, "...", "d"}], "s"[SubscriptSequence["n", {1, 2, "...", "d"}]]]] <> " finds equalities between subarrays of a " <> box["d"] <> "\[Hyphen]dimensional sequence in bases " <> box[SubscriptSequence["k", {1, 2, "...", "d"}]] <> "."

FindPolynomial::usage =
box[FindPolynomial[SubscriptList["a", {1, 2, "..."}], "x"]] <> " constructs an interpolating polynomial in " <> box["x"] <> " which reproduces the function values " <> box[Subscript["a", "i"]] <> " at successive integer values " <> box[1, 2, "\[Ellipsis]"] <> " of " <> box["x"] <> ".\n" <>
box[FindPolynomial[{Subscript["a", "d"], Subscript["a", "d"+1], "\[Ellipsis]"}, "x", "d"]] <> " indexes terms beginning at " <> box["d"] <> ".\n" <>
box[FindPolynomial["array", {"x", "y", "\[Ellipsis]"}, SubscriptList["d", {"x", "y", "..."}]]] <> " gives a multivariate polynomial which provides an exact fit to a full array of values."

FindQuasiPolynomial::usage =
box[FindQuasiPolynomial[SubscriptList["a", {1, 2, "..."}], "x", "m"]] <> " constructs an interpolating polynomial in " <> box["x"] <> " for each residue class of " <> box["x"] <> " modulo " <> box["m"] <> ".\n" <>
box[FindQuasiPolynomial[{Subscript["a", "d"], Subscript["a", "d"+1], "\[Ellipsis]"}, "x", "m", "d"]] <> " indexes terms beginning at " <> box["d"] <> "."

FindRegularSequenceFunction::usage =
box[FindRegularSequenceFunction[SubscriptList["a", {0, 1, "..."}], "k"]] <> " attempts to find a " <> box["k"] <> "\[Hyphen]regular sequence which reproduces the sequence " <> box[Subscript["a", "n"]] <> ".\n" <>
box[FindRegularSequenceFunction["array", SubscriptList["k", {1, 2, "...", "d"}]]] <> " finds a " <> box["d"] <> "\[Hyphen]dimensional (" <> box[SubscriptSequence["k", {1, 2, "...", "d"}]] <> ")\[Hyphen]regular sequence which reproduces a full array of values.\n" <>
box[FindRegularSequenceFunction["array", "kspec", "n"]] <> " gives the function applied to " <> box["n"] <> "."

FindRegularSequenceRecurrence::usage =
box[FindRegularSequenceRecurrence[SubscriptList["a", {0, 1, "..."}], "k", "s"["n"]]] <> " attempts to find linear relations between subsequences of the sequence " <> box[Subscript["a", "n"]] <> " of the form " <> box["s"["k"^"e" * "n" + "i"]] <> " that determine the sequence.\n" <>
box[FindRegularSequenceRecurrence["array", SubscriptList["k", {1, 2, "...", "d"}], "s"[SubscriptSequence["n", {1, 2, "...", "d"}]]]] <> " finds relations between subarrays of a " <> box["d"] <> "\[Hyphen]dimensional sequence in bases " <> box[SubscriptSequence["k", {1, 2, "...", "d"}]] <> "."

FlattenInputAlphabet::usage =
"FlattenInputAlphabet is an option for FindAutomaticSequenceAutomaton and related functions that specifies whether to replace the input alphabet " <> box[{{0}, {1}, "\[Ellipsis]", {"k"-1}}] <> " with " <> box[{0, 1, "\[Ellipsis]", "k"-1}] <> "."

FromCoefficientList::usage =
box[FromCoefficientList["list", "var"]] <> " constructs a polynomial in " <> box["var"] <> " from its coefficient list.\n" <>
box[FromCoefficientList["array", SubscriptList["var", {1, 2, "..."}]]] <> " constructs a multivariate polynomial from its coefficient array."

FromDigitList::usage =
box[FromDigitList["list", "b"]] <> " constructs an integer from the list of its base\[Hyphen]" <> box["b"] <> " digits, where successive digits increase in significance.\n" <>
box[FromDigitList["list", SubscriptList["b", {0, 1, "...", "m"}]]] <> " uses the mixed radix with bases " <> box[SubscriptSequence["b", {0, 1, "...", "m"}]] <> ".\n" <>
box[FromDigitList["list", "B"]] <> " constructs an integer from its representation in the numeration system " <> box["B"] <> "."

FromRecurrence::usage =
box[FromRecurrence["eqns", "s"["n"]]] <> " makes " <> box["s"] <> " into a function satisfying the recurrence equations " <> box["eqns"] <> " of fixed order."

GatherEdges::usage =
"GatherEdges is an option for AutomatonGraph that specifies whether to combine multiple edges into a single edge."

GeneratingFunctionRelations::usage =
box[GeneratingFunctionRelations[SubscriptList["eqn", {1, 2, "..."}], "s"[SubscriptSequence["n", {1, 2, "...", "k"}]], "f"[SubscriptSequence["x", {1, 2, "...", "k"}]]]] <> " gives equations satisfied by the multivariate generating function " <> box["f"[SubscriptSequence["x", {1, 2, "...", "k"}]]] <> " of the sequence " <> box["s"[SubscriptSequence["n", {1, 2, "...", "k"}]]] <> " satisfying a linear system of partial recurrence equations."

HashStateNames::usage =
"HashStateNames is an option for AutomaticSequenceReduce and other automaton construction functions that specifies whether states should be considered equivalent if their hash values coincide."

ImportMotzkinNumber::usage =
box[ImportMotzkinNumber["n"]] <> " loads into cache the (" <> box["n" - 1] <> ")st and " <> box["n"] <> "th Motzkin numbers from $MotzkinNumberDirectory, if available."

IndexedStateNames::usage =
"IndexedStateNames is an option for FindAutomaticSequenceAutomaton and related functions that specifies whether to replace state names with integers."

InputAlphabet::usage =
"InputAlphabet is an option for Automaton that specifies the input alphabet."

IntegerPrepend::usage =
box[IntegerPrepend["n", "b", "digitlist"]] <> " gives the integer obtained by prepending " <> box["digitlist"] <> " to the base\[Hyphen]" <> box["b"] <> " digits of " <> box["n"] <> ".\n" <>
box[IntegerPrepend["n", "B", "digitlist"]] <> " prepends in the numeration system " <> box["B"] <> "."

IntermediateFunction::usage =
"IntermediateFunction is an option for FindPolynomial that specifies a function to apply at each intermediate step."
(*
"IntermediateFunction is an option for FindPolynomial and LinearRecurrenceTable that specifies a function to apply at each intermediate step."
*)

JacobsthalNumber::usage =
box[JacobsthalNumber["n"]] <> " gives the " <> box["n"] <> "th Jacobsthal number " <> box[Subscript["J", "n"]] <> "."

LaurentPolynomialCoefficientList::usage =
box[LaurentPolynomialCoefficientList["poly", "var"]] <> " gives a list of coefficients of powers of " <> box["var"] <> " in the Laurent polynomial " <> box["poly"] <> ".\n" <>
box[LaurentPolynomialCoefficientList["poly", "var", SubscriptList["e", {"min", "max"}]]] <> " gives a list of coefficients of powers of " <> box["var"] <> " in " <> box["poly"] <> ", starting with " <> box[Subscript["e", "min"]] <> " and ending with " <> box[Subscript["e", "max"]] <> ".\n" <>
box[LaurentPolynomialCoefficientList["poly", SubscriptList["var", {1, 2, "..."}], {{Subscript["e", 1, "min"], Subscript["e", 1, "max"]}, {Subscript["e", 2, "min"], Subscript["e", 2, "max"]}, "\[Ellipsis]"}]] <> " gives an array of the coefficients of the " <> box[Subscript["var", "i"]] <> "."

LeadingZeros::usage =
"LeadingZeros is an option for DigitsCount that specifies whether to include leading zeros."

LinearNumerationSystem::usage =
box[LinearNumerationSystem["ker", "init"]] <> " represents a linear positional numeration system with kernel " <> box["ker"] <> " starting with initial values " <> box["init"] <> "."

LinearNumerationSystemQ::usage =
box[LinearNumerationSystemQ["B"]] <> " yields True if " <> box["B"] <> " is a linear positional numeration system, and False otherwise."

LinearRecurrenceTable::usage =
box[LinearRecurrenceTable["ker", "init", "n"]] <> " gives the sequence of length " <> box["n"] <> " obtained by iterating the linear recurrence with coefficients " <> box["ker"] <> " starting with initial values " <> box["init"] <> ".\n" <>
box[LinearRecurrenceTable["ker", "init", SubscriptList["n", {"min", "max"}]]] <> " yields terms " <> box[Subscript["n", "min"]] <> " through " <> box[Subscript["n", "max"]] <> " in the linear recurrence sequence.\n" <>
box[LinearRecurrenceTable["ker", "init", "nspec", "f"]] <> " applies the function " <> box["f"] <> " to each term after it is computed."

MaxDenominator::usage =
"MaxDenominator is an option for SeriesSolve that specifies the maximum denominator to allow in the exponents of solutions."

MorphicSequence::usage =
box[MorphicSequence["rule", "init"]["n"]] <> " gives the " <> box["n"] <> "th term in the fixed point, beginning with " <> box["init"] <> ", of the morphism " <> box["rule"] <> ".\n" <>
box[MorphicSequence["rule", "init", {"\[Ellipsis]", Subscript["s", "i"] -> Subscript["v", "i"], "\[Ellipsis]"}]["n"]] <> " outputs " <> box[Subscript["v", "i"]] <> " if the " <> box["n"] <> "th term is " <> box[Subscript["s", "i"]] <> ".\n" <>
box[MorphicSequence["rule", "init", "outputrules"][SubscriptSequence["n", {1, 2, "...", "d"}]]] <> " gives the value of a " <> box["d"] <> "\[Hyphen]dimensional morphic sequence."

(* xxx implement this? *)
MorphicSequenceMorphism::usage =
box[MorphicSequence[MorphicSequence["subs", "k"]["n"]]] <> " extracts the morphism from a MorphicSequence object."

MorphicSequenceReduce::usage =
box[MorphicSequenceReduce["expr", "n"]] <> " attempts to reduce " <> box["expr"] <> " to a single MorphicSequence object as a function of " <> box["n"] <> ".\n" <>
box[MorphicSequenceReduce["expr", "n", "k"]] <> " attempts to reduce " <> box["expr"] <> " to a " <> box["k"] <> "\[Hyphen]uniform morphic sequence."

MorphismAdjacencyMatrix::usage =
box[MorphismAdjacencyMatrix["\[Phi]"]] <> " gives the letter\[Dash]letter adjacency matrix of the morphism " <> box["\[Phi]"] <> ".\n" <>
box[MorphismAdjacencyMatrix["\[Phi]", "alphabet"]] <> " uses the letter order specified by " <> box["alphabet"] <> "."

MorphismPower::usage =
box[MorphismPower["\[Phi]", "n"]] <> " gives the " <> box["n"] <> "th power of the morphism " <> box["\[Phi]"] <> "."

MotzkinNumber::usage =
box[MotzkinNumber["n"]] <> " gives the " <> box["n"] <> "th Motzkin number " <> box[Subscript["M", "n"]] <> "."

OEISData::usage =
box[OEISData[String["anum"], String["property"]]] <> " gives the value of the specified property for the sequence " <> box["anum"] <> " indexed by The On\[Hyphen]Line Encyclopedia of Integer Sequences."

OEISSequence::usage =
box[OEISSequence[String["anum"]]["n"]] <> " gives the " <> box["n"] <> "th term of the sequence " <> box["anum"] <> " indexed by The On\[Hyphen]Line Encyclopedia of Integer Sequences."

OEISWebLookup::usage =
box[OEISWebLookup[SubscriptList["s", {1, 2, "..."}]]] <> " looks up terms of a sequence in The On\[Hyphen]Line Encyclopedia of Integer Sequences web search.\n" <>
box[OEISWebLookup[String["anum"]]] <> " looks up a sequence by its A\[Hyphen]number."

OrePolynomial::usage =
box[OrePolynomial["poly", "x", "n"]] <> " gives a multiple of " <> box["poly"] <> " whose exponents are powers of " <> box["n"] <> ".\n" <>
box[OrePolynomial["poly", {Subscript["x", 1], Subscript["x", 2], "\[Ellipsis]", Subscript["x", "k"], "y"}, "n"]] <> " gives a multiple of " <> box["poly"] <> " whose exponents in " <> box["y"] <> " are powers of " <> box["n"] <> "."

Radical::usage =
box[Radical["n"]] <> " gives the product of the prime divisors of " <> box["n"] <> "."

ReduceAutomaton::usage =
box[ReduceAutomaton["expr", "k", "vars"]] <> " reduces the statement " <> box["expr"] <> " over the domain of non\[Hyphen]negative integers to an automaton that outputs the truth value of " <> box["expr"] <> " when fed the base\[Hyphen]" <> box["k"] <> " digits of " <> box["vars"] <> " starting with the least significant digits.\n" <>
box[ReduceAutomaton["expr", "k"]] <> " gives an automaton for an expression in which all variables are quantified."

RegularSequence::usage =
box[RegularSequence["u", {Subscript["m", 0], Subscript["m", 1], "\[Ellipsis]", Subscript["m", "k"-1]}, "v", "k"]["n"]] <> " gives " <> box[Dot["u", Subscript["m", Subscript["n", 0]], Subscript["m", Subscript["n", 1]], "\[CenterEllipsis]", Subscript["m", Subscript["n", "l"]], "v"]] <> ", where " <> box["n" == Subscript["n", "l"] "\[CenterEllipsis]" Subscript["n", 1] Subscript["n", 0]] <> " in base " <> box["k"] <> ".\n" <>
box[RegularSequence["u", "matrixarray", "v", SubscriptList["k", {1, 2, "...", "d"}]][SubscriptSequence["n", {1, 2, "...", "d"}]]] <> " gives the value of a " <> box["d"] <> "\[Hyphen]dimensional (" <> box[SubscriptSequence["k", {1, 2, "...", "d"}]] <> ")\[Hyphen]regular sequence.\n" <>
box[RegularSequence["u", "matrixarray", "v"]["n"]] <> " infers the base " <> box["k"] <> " from " <> box["matrixarray"] <> "."
(*
box[RegularSequence["u", "matrixlist", "v"][SubscriptList["n", {1, 2, "..."}]]] <> " gives terms " <> box[SubscriptSequence["n", {1, 2, "..."}]] <> " of a one\[Hyphen]dimensional " <> box["k"] <> "\[Hyphen]regular sequence."
*)

RegularSequenceGeneratorTable::usage =
box[RegularSequenceGeneratorTable[RegularSequence["u", "matrixlist", "v"], "nmax"]] <> " gives terms 0 through " <> box["nmax"] <> " of the generator sequences for the given regular sequence representation.\n" <>
box[RegularSequenceGeneratorTable[RegularSequence["u", "matrixarray", "v"], SubscriptList["nmax", {1, 2, "...", "d"}]]] <> " gives the initial " <> box[(Subscript["nmax", 1] + 1) "\[Times]" (Subscript["nmax", 2] + 1) "\[Times]" "\[CenterEllipsis]" "\[Times]" (Subscript["nmax", "d"] + 1)] <> " array of each generator."

RegularSequenceMatrixForm::usage =
box[RegularSequenceMatrixForm["expr"]] <> " prints with regular sequences in " <> box["expr"] <> " in matrix form."

RegularSequenceMatrixLength::usage =
box[RegularSequenceMatrixLength[RegularSequence["u", "matrixarray", "v"]]] <> " gives the number of generator sequences for the given regular sequence representation."

RegularSequenceRecurrence::usage =
box[RegularSequenceRecurrence[RegularSequence["u", "matrixlist", "v"], "s"["n"]]] <> " gives the linear relations between subsequences of the generator sequences " <> box[Subscript["a", "i"]["n"]] <> " for the given representation of a regular sequence.\n" <>
box[RegularSequenceRecurrence[RegularSequence["u", "matrixarray", "v"], "s"[SubscriptSequence["n", {1, 2, "...", "d"}]]]] <> " gives relations for a " <> box["d"] <> "\[Hyphen]dimensional regular sequence."

RegularSequenceReduce::usage =
box[RegularSequenceReduce["expr", "n"]] <> " attempts to reduce " <> box["expr"] <> " to a single RegularSequence object as a function of " <> box["n"] <> ".\n" <>
box[RegularSequenceReduce["expr", "n", "k"]] <> " attempts to reduce " <> box["expr"] <> " to a " <> box["k"] <> "\[Hyphen]regular sequence."

If[$VersionNumber < 10.2,
RudinShapiro::usage =
box[RudinShapiro["n"]] <> " gives the " <> box["n"] <> "th term in the Rudin\[Dash]Shapiro sequence."
]

SequenceComplexity::usage =
box[SequenceComplexity["sequence"]] <> " gives the complexity of " <> box["sequence"] <> " in its given form."

SequenceRiffle::usage =
box[SequenceRiffle[SubscriptList["f", {1, 2, "...", "m"}], "x"]] <> " forms a Piecewise expression in " <> box["x"] <> " that represents the expressions " <> box[SubscriptSequence["f", {1, 2, "...", "m"}]] <> " on residue classes modulo " <> box["m"] <> "."

SeriesRoot::usage =
box[SeriesRoot[{"f", Subscript["y", 0]}]] <> " represents the power series solution " <> box["y"] <> " of the polynomial equation " <> box["f"["y"] == 0] <> " approximated by " <> box[Subscript["y", 0]] <> "."

SeriesSolve::usage =
box[SeriesSolve["eqn", "f[x]", {"x", Subscript["x", 0], "n"}]] <> " attemps to solve " <> box["eqn"] <> " for power series " <> box["f"["x"]] <> " about the point " <> box["x" = Subscript["x", 0]] <> " to order " <> box[("x" - Subscript["x", 0])^"n"] <> "."

StateStorage::usage =
"StateStorage is an option for AutomaticSequenceReduce and other automaton construction functions that specifies whether states should be stored in memory or written to disk."

SternBrocot::usage =
box[SternBrocot["n"]] <> " gives the " <> box["n"] <> "th term in the Stern\[Dash]Brocot sequence."

SynchronizedSequence::usage =
box[SynchronizedSequence["M"]["n"]] <> " gives a [XXX the least?] non\[Hyphen]negative integer " <> box["m"] <> " such that the automaton " <> box["M"] <> " evaluates to True when fed the base\[Hyphen]" <> box["k"] <> " digits of (" <> box["n", "m"] <> ") starting with the least significant digits."
(* multidimensional version
box[SynchronizedSequence["M"][SubscriptSequence["n", {1, 2, "...", "d"}]]] <> " XXX gives the value of a " <> box["d"] <> "\[Hyphen]dimensional synchronized sequence."
*)

If[$VersionNumber < 10.2,
ThueMorse::usage =
box[ThueMorse["n"]] <> " gives the " <> box["n"] <> "th term in the Thue\[Dash]Morse sequence."
]

TransitionSequence::usage =
box[TransitionSequence[SubscriptSequence["a", {0, 1, "..."}]]] <> " represents a sequence of input letters corresponding to a single transition in a non\[Hyphen]deterministic automaton."

Tribonacci::usage =
box[Tribonacci["n"]] <> " gives the " <> box["n"] <> "th Tribonacci number."

$CacheMotzkinNumbers::usage =
"$CacheMotzkinNumbers specifies whether MotzkinNumber should cache all values it computes.  Set it to False to only cache the highest two values."

$MotzkinNumberDirectory::usage =
"$MotzkinNumberDirectory gives the directory where Motzkin numbers are stored."


If[$VersionNumber < 10,
	DeleteDuplicatesBy[list_, f_] := First /@ GatherBy[list, f];
(* DuplicateFreeQ actually exists in V9.
	DuplicateFreeQ[list_] := UnsameQ @@@ list;
*)
	FirstCase[list_, pattern_, default_ : Missing["NotFound"]] := First[Replace[Cases[list, pattern, {1}, 1], {} :> {default}]];
	SubsetQ[list1_, list2_] := Complement[list2, list1] == {}
]

If[$VersionNumber < 10.2,
	MissingQ[expression_] := MatchQ[expression, _Missing]
]

If[$VersionNumber < 11.2,
	TwoWayRule[x_, y_] := Normal[SparseArray[{x -> y, y -> x, i_ :> i}]]
]

Monitor::abort = "Monitor breaks Abort and Catch in version " <> ToString[$VersionNumber] <> ".  Use version 11 or later for monitoring."


BlockDiagonalMatrix[matrices : {__?MatrixQ}] :=
With[{nonemptymatrices = DeleteCases[matrices, {{}}]},
	ArrayFlatten[
		DiagonalMatrix[Range[Length[nonemptymatrices]]] /.
			Thread[Range[Length[nonemptymatrices]] -> nonemptymatrices]
	]
]

Cartier0[polynomial_, variables_, k_] :=
	FromCoefficientRules[
		MapAt[#/k &, 1] /@ Select[LaurentPolynomialCoefficientRules[polynomial, variables], And @@ Divisible[First[#], k] &],
		variables
	]

(* This assumes that all exponents are divisible by k. *)
Cartier0WithoutSelect[polynomial_, variables_, k_] :=
	FromCoefficientRules[
		MapAt[#/k &, 1] /@ LaurentPolynomialCoefficientRules[polynomial, variables],
		variables
	]
SymbolicCartier0WithoutSelect[polynomial_, variables_, k_] :=
	FromCoefficientRules[
		MapAt[#/k &, 1] /@ GeneralCoefficientRules[polynomial, variables],
		variables
	]

(* CongruentMonomialTimes multiplies two polynomials,
   keeping only monomials with exponents that are congruent to each other (according to a certain diagonal). *)
CongruentMonomialTimes[factor1monomiallist_, binnedfactor2monomiallists_, p_, variablepartition_, Modulus -> modulus_] :=
	Expand[
		Total[Times[
			Replace[
				(* Bin monomials by the differences of their exponents modulo p (according to the diagonal we're interested in). *)
				Last[Reap[
					Function[monomial,
						Sow[
							monomial,
							{Mod[Join @@ (Exponent[monomial, First[#]] - Exponent[monomial, Rest[#]] &) /@ variablepartition, p]}
						];
					] /@ factor1monomiallist;,
					Tuples[Range[0, p - 1], Total[Length /@ variablepartition] - Length[variablepartition]]
				]],
				{{} -> 0, {list_} :> Total[list]},
				{1}
			],
			binnedfactor2monomiallists
		]],
		Modulus -> modulus
	]

(* This assumes the expression is in expanded form. *)
ConstantTerm[polynomial_Plus, variables_List] :=
With[{constantterm = First[polynomial]},
	If[FreeQ[constantterm, Alternatives @@ variables], constantterm, 0]
]
ConstantTerm[monomial_, variables_List] :=
	If[FreeQ[monomial, Alternatives @@ variables], monomial, 0]

(* CoprimeDivisor[n, m] gives the largest divisor of n that is relatively prime to m. *)
CoprimeDivisor[n_Integer?Positive, m_Integer] := n/FixedPoint[GCD[m #, n] &, 1]

SetAttributes[DiscretePower, {Listable, NumericFunction, OneIdentity}]
DiscretePower[0, 0] = 1
DiscretePower[a_, b_] := a^b

FastFactorList[product_Times] :=
	Replace[
		List @@ product,
		{
			power_Power :> {First[power], Rest[power]},
			expression_ :> {expression, 1}
		},
		{1}
	]
FastFactorList[power_Power] :=
	{{First[power], Rest[power]}}
FastFactorList[expression_] :=
	{{expression, 1}}

(* This assumes the expression is in expanded form. *)
FastMonomialList[polynomial_Plus] := List @@ polynomial
FastMonomialList[0 | 0.] = {}
FastMonomialList[monomial_] := {monomial}

FirstPositionLevel1[expression_, pattern_, default_ : Missing["NotFound"]] :=
	First[FirstPosition[expression, pattern, {default}, {1}, Heads -> False]]

FragileTogether[expr_Plus] :=
With[{numerators = Numerator[List @@ expr], denominators = Denominator[List @@ expr]},
	Total[MapIndexed[#1 Times @@ Delete[denominators, First[#2]] &, numerators]] / Times @@ denominators
]
FragileTogether[expr_] := expr

(* Unlike CoefficientRules, GeneralCoefficientRules supports rational (and negative integer) exponents. *)
(* This assumes the expression is in expanded form. *)
GeneralCoefficientRules[expression_, variables_List] :=
	Normal[GroupBy[
		Exponent[#, variables] -> (# /. Alternatives @@ variables -> 1) & /@
			FastMonomialList[expression],
		First -> Last,
		Total
	]]

(* This assumes that the basis function is increasing and that  basisfunction[0] == 1 . *)
GreedyPartitionDigitList[n_Integer?Positive, basisfunction_] :=
Module[{remaining = n, indexplus1, quotient},
	Normal[SparseArray[Reap[
		(* Initially we don't have an upper bound on the index, so we must start at the bottom and increase. *)
		indexplus1 = 1;
		While[basisfunction[indexplus1] <= remaining, indexplus1++];
		{quotient, remaining} = QuotientRemainder[remaining, basisfunction[indexplus1 - 1]];
		Sow[indexplus1 -> quotient];
		(* Now we have an upper bound, so we can start there and decrease. *)
		While[remaining > 0,
			While[basisfunction[indexplus1] > remaining, indexplus1--];
			indexplus1++;
			{quotient, remaining} = QuotientRemainder[remaining, basisfunction[indexplus1 - 1]];
			Sow[indexplus1 -> quotient]
		]
	][[2, 1]]]]
]
GreedyPartitionDigitList[0, _] :=
	{}

(*
(* InsertPart creates a list where the new element appears at the given positions. *)
InsertAt[list_List, element_, positions : {{_Integer} ...}] :=
With[{length = Length[list] + Length[positions]},
	Normal[SparseArray[
		Thread[Complement[Range[length], First /@ positions] -> list],
		length,
		element
	]]
]
*)
(* InsertPart creates a list where the new elements appear at the given positions. *)
InsertPart[list_List, (positions : {{_Integer} ...}) -> element_] :=
With[{length = Length[list] + Length[positions]},
	Normal[SparseArray[
		Thread[Complement[List /@ Range[length], positions] -> list],
		length,
		element
	]]
]
InsertPart[{}, {}] :=
	{}
InsertPart[list_List, rules : {({_Integer} -> _) ...}] :=
With[{length = Length[list] + Length[rules]},
	Normal[SparseArray[
		Join[
			Thread[Complement[List /@ Range[length], First /@ rules] -> list],
			rules
		]
	]]
]

(* LaurentPolynomialCoefficient doesn't thread over lists, like Coefficient does. *)
(* The single-variable case could be handled by the general case, but including this down value improves speed. *)
LaurentPolynomialCoefficient[expression_, {variable_}, {exponent_}] :=
	Coefficient[expression, variable, exponent]
(* This is actually faster than Coefficient (when the exponents are non-zero). *)
(* XXX Not sure what that note means; Coefficient doesn't do the same thing. *)
LaurentPolynomialCoefficient[expression_, variables_List, exponents_List] :=
	Fold[
		Function[{polynomial, variableexponentpair},
			Coefficient[polynomial, First[variableexponentpair], Last[variableexponentpair]]
		],
		expression,
		Transpose[{variables, exponents}]
	]
(* xxx much slower
LaurentPolynomialCoefficient[expression_, variables_List, exponents_List] :=
	Replace[
		exponents,
		Append[
			LaurentPolynomialCoefficientRules[expression, variables],
			_ -> 0
		]
	]
*)
(* xxx also slower
LaurentPolynomialCoefficient[expression_, variables_List, exponents_List] :=
With[{exponent0variablepattern = Alternatives @@ Pick[variables, exponents, 0]},
	Coefficient[
		expression,
		Times @@ (DeleteCases[variables, exponent0variablepattern]^DeleteCases[exponents, 0])
	] /. exponent0variablepattern -> 1
]
*)

(* NOTE: If there are symbolic coefficients this doesn't behave ideally:
   LaurentPolynomialCoefficientRules[a x + b x, {x}]  evaluates to  {{1} -> a, {1} -> b} .
   Use GeneralCoefficientRules instead.
*)
(*
An alternative way of doing this would be to add some power of O[x] to convert it into a series and then extract the coefficient list:
The advantage would be that the coefficients would appear in order of exponent (although CoefficientRules reverses the order).
*)
(* Or I could scale each variable up so that we have a polynomial, as in LaurentPolynomialQ. *)
(* This assumes the expression is in expanded form. *)
(* Also this assumes that the expression is a Laurent polynomial in the variables. *)
LaurentPolynomialCoefficientRules[expression_, variables_List] :=
	Exponent[#, variables] -> (# /. Alternatives @@ variables -> 1) & /@
		FastMonomialList[expression]

(* xxx this name isn't ideal because the behavior doesn't parallel SeriesMod ... but we are modding out in some sense *)
LaurentPolynomialMod[expression_, variables_List, annihilatordata_, modulus_] :=
	Fold[
		Function[{polynomial, annihilator},
			Expand[polynomial - Quotient[LaurentPolynomialCoefficient[polynomial, variables, annihilator[[4]]], annihilator[[1]]] annihilator[[5]], Modulus -> modulus]
		],
		expression,
		annihilatordata
	]

(* TODO These evaluate to True:
	IntegerSequences`Private`LaurentPolynomialQ[x^(1/2) + x^(3/2), {x}]
	IntegerSequences`Private`LaurentPolynomialQ[x^a, {x}]
*)
LaurentPolynomialQ[0, _List] :=
	True
LaurentPolynomialQ[expression_, variables_List] :=
With[{exponents = Exponent[expression, variables, List]},
	And[
		MatchQ[exponents, {{___Integer} ..}],
		PolynomialQ[
			Cancel[Times @@ (variables^-(Min /@ exponents)) expression],
			variables
		]
	]
]

(* LaurentPolynomialPowerAnnihilators computes a basis for the vector space of polynomials  a[x]  such that the constant term of  a[x]*f[x]^n  is zero for all  n >= 0 ,
   and a[x] has nonzero coefficients corresponding to exponents outside the range [-r, -l] if the MinMax exponents of f[x] is {l, r}. *)
(* It's only implemented for univariate polynomials, and it assumes the smallest exponent is negative and the largest exponent is positive. *)
LaurentPolynomialPowerAnnihilators[polynomial_, variable_, OptionsPattern[]] :=
Module[{minexponent, maxexponent, exponentgcd, scaledpolynomial, modulus, annihilatorexponentminmax, annihilators, list, a, c, i, maxpower, power, lambda},
	{minexponent, maxexponent} = Exponent[polynomial, variable, MinMax[{##}] &];
	exponentgcd = Exponent[polynomial, variable, GCD];
	scaledpolynomial = polynomial /. variable -> variable^(1/exponentgcd);
	modulus = OptionValue[Modulus];
	annihilators = Join[
		(* Annihilators that arise from representations of the polynomial as a linear combination of powers of another polynomial. *)
(*
EchoFunction[DeleteCases[ModularRowReduce[#, modulus], {0 ..}] &][
*)
		Join @@ (*EchoFunction[Mod[#, modulus] &]@*)Table[
			If[maxpower == 1,
				{Reverse[LaurentPolynomialCoefficientList[variable D[polynomial, variable], variable, {minexponent, maxexponent}]]}
				,
				annihilatorexponentminmax = {minexponent, maxexponent}/maxpower;
				annihilators = {{
					Thread[Subscript[c, Range[maxpower]]],
					Dot[
						Replace[
							Thread[Subscript[a, Range @@ annihilatorexponentminmax]],
							(* Set the constant term to be 0 and the leading coefficient to be 1. *)
							{Subscript[a, 0] -> 0, Subscript[a, Last[annihilatorexponentminmax]] -> 1},
							{1}
						],
						variable^(Range @@ annihilatorexponentminmax)
					]
				}};
				Do[
					annihilators = Join @@ Function[{coefficients, annihilator},
						list = LaurentPolynomialCoefficientList[
							polynomial - Take[coefficients, {power, maxpower}].annihilator^Range[power, maxpower],
							variable,
							power annihilatorexponentminmax
						];
						{coefficients, annihilator} /. # & /@ Cases[
							Solve[
								Equal @@ Join[
									Take[list, -First[annihilatorexponentminmax]],
									Take[list, -Last[annihilatorexponentminmax]],
									{0}
								],
								Modulus -> modulus
							],
							{(_ -> _Integer | _Rational) ..}
						]
					] @@@ annihilators,
					{power, maxpower, 1, -1}
				];
				Function[{coefficients, annihilator},
(* discard the coefficient list since we just care about the annihilator, not the representation
					{
						Prepend[coefficients, Expand[polynomial - coefficients.Table[annihilator^power, {power, 1, maxpower}]]],
						annihilator
					}
*)
					Reverse[LaurentPolynomialCoefficientList[variable D[annihilator, variable], variable, {minexponent, maxexponent}]]
				] @@@ annihilators
			],
			{maxpower, Divisors[GCD[minexponent, maxexponent]]}
(*
]
*)
		],
		(* Annihilators that arise from 0 coefficients in the polynomial. *)
		Table[
			UnitVector[maxexponent - minexponent + 1, Rescale[i, {minexponent, maxexponent}, {1, maxexponent - minexponent + 1}]],
			{i, Select[Range[-maxexponent, -minexponent], !Divisible[#, exponentgcd] &]}
		],
		(* Annihilators that arise from symmetries in the polynomial. *)
(* doesn't happen since we've chosen  exponentgcd  maximal
		If[scaledpolynomial === (scaledpolynomial /. variable -> -variable),
			Join @@ Table[
				UnitVector[maxexponent - minexponent + 1, Rescale[i, {minexponent, maxexponent}/exponentgcd, {1, maxexponent - minexponent + 1}]],
				{i, Select[Range[-maxexponent/exponentgcd, -minexponent/exponentgcd], OddQ]}
			],
			{}
		],
*)
		list = If[modulus == 0,
			(lambda /. # &) /@ SolveAlways[scaledpolynomial == (scaledpolynomial /. variable -> lambda/variable), variable],
(* xxx not efficient *)
(* when there are multiple solutions, do we actually need them all?  in the one example i looked at, we don't *)
			list = Select[
				Range[0, modulus - 1],
(* xxx could the Equal ever evaluate to False before getting a chance to reduce and determine congruence modulo  modulus ? *)
				CoprimeQ[#, modulus] && Expand[scaledpolynomial == (scaledpolynomial /. variable -> #/variable), Modulus -> modulus] &
			]
		];
		Join @@
			(Table[
				-UnitVector[maxexponent - minexponent + 1, Rescale[-i, {minexponent, maxexponent}/exponentgcd, {1, maxexponent - minexponent + 1}]] +
					#^i UnitVector[maxexponent - minexponent + 1, Rescale[i, {minexponent, maxexponent}/exponentgcd, {1, maxexponent - minexponent + 1}]],
(* xxx is this right? *)
				{i, 1, Max[-minexponent, maxexponent]/exponentgcd}
			] &) /@ list
	];
	DeleteCases[
(* xxx if the modulus is prime, should I use  RowReduce[annihilators, Modulus -> modulus] ?*)
		If[modulus == 0,
			RowReduce[annihilators],
			ModularRowReduce[annihilators, modulus]
		],
		{0 ..}
	]
]
Options[LaurentPolynomialPowerAnnihilators] = {Modulus -> 0}

(* The sign of LineSide indicates the side (1 for Left, -1 for Right) of a directed line (passing through two given points, in order) that a point lies on. *)
LineSide[{{point1x_, point1y_}, {point2x_, point2y_}}, {x_, y_}] :=
	Subtract[
		(point2x - point1x) (y - point1y),
		(point2y - point1y) (x - point1x)
	]

(* not in use
(* TODO Better name? *)
ListMapAt[f_, expression_, position_] :=
	MapAt[f, #, position] & /@ expression
*)

MapAcross[functions_List, arguments_List] /; Length[functions] == Length[arguments] :=
	MapThread[#1[#2] &, {functions, arguments}]

(*
SlowModularExtendedGCDMatrix[a_, b_, modulus_] :=
With[
	{firstrow = Replace[
		Mod[Last[ExtendedGCD[a, b]], modulus],
		{0, 0} -> {1, 1}
	]},
	{
		firstrow,
		SelectFirst[
			Tuples[Range[0, modulus - 1], 2],
			Function[secondrow,
				Mod[secondrow.{a, b}, modulus] == 0 && Det[{firstrow, secondrow}, Modulus -> modulus] == 1
			]
		]
	}
]
*)

(* ModularExtendedGCDMatrix[a, b, modulus]  gives a 2x2 matrix satisfying
   Det[matrix, Modulus -> modulus] == 1 && Mod[matrix.{a, b} - {GCD[a, b], 0}, modulus] == {0, 0} . *)
(* XXX It can happen that the gcd contains a factor that is relatively prime to the modulus, right?  So that we should maybe divide by it?  Is that handled by ModularUnitInverse?
   Buchmann--Neis address this, but Storjohann--Mulders don't. *)
ModularExtendedGCDMatrix[0, 0, _] :=
	IdentityMatrix[2]
ModularExtendedGCDMatrix[a_, b_, modulus_] :=
Module[{gcd, coefficients},
	{gcd, coefficients} = ExtendedGCD[a, b];
(* XXX Maybe it would be slightly more efficient to not apply Mod here because the output matrix gets Dot[]ted and then Mod[]ded. *)
	Mod[{coefficients, {-b, a}/gcd}, modulus]
]

ModularStabilization[a_, b_, modulus_] :=
	CoprimeDivisor @@ ({modulus, a}/GCD[a, b, modulus])

(* ModularUnitInverse[n, modulus]  gives an integer  unitinverse  satisfying
   Mod[unitinverse n, modulus] == GCD[n, modulus] && CoprimeQ[unitinverse, modulus] . *)
ModularUnitInverse[n_, modulus_] /; !Divisible[n, modulus] :=
Module[{gcd, quotient, inverse},
	gcd = GCD[n, modulus];
	quotient = modulus/gcd;
	inverse = PowerMod[n/gcd, -1, quotient];
(* XXX Maybe it would be slightly more efficient to not apply Mod here because the output gets multiplied and then Mod[]ded. *)
	Mod[inverse + ModularStabilization[inverse, quotient, modulus] quotient, modulus]
]

(* This is only implemented for prime power moduli.
ModularRowReduce[m_, modulus_] :=
Module[{p, matrix = m, pivotcolumnindex, pivotrowindex = 1, columnvaluations, minvaluation, oldpivotentry, pivotentry, invertiblemultiple, pivotrow},
	p = First[NumberTheory`PrimePower[modulus]];
	Do[
		columnvaluations = IntegerExponent[#[[pivotcolumnindex]], p] & /@ Drop[matrix, pivotrowindex - 1];
		minvaluation = Min[columnvaluations];
		If[minvaluation != Infinity,
			(* Permute rows. *)
			matrix = Swap[
				matrix,
				{
					pivotrowindex,
					(* We need to specify the level here; otherwise 1 is matched in DirectedInfinity[1]. *)
					FirstPositionLevel1[columnvaluations, minvaluation] + pivotrowindex - 1
				}
			];
			oldpivotentry = matrix[[pivotrowindex, pivotcolumnindex]];
			pivotentry = p^IntegerExponent[oldpivotentry, p];
			(* The pivot entry isn't necessarily invertible modulo the modulus, but dividing as integers gives the invertible multiple by which they differ. *)
			invertiblemultiple = PowerMod[oldpivotentry/pivotentry, -1, modulus];
(* XXX Does wrapping this in  Mod[ , modulus]  help or hurt in terms of speed? *)
			pivotrow = invertiblemultiple matrix[[pivotrowindex]];
			matrix = Mod[
				Join[
					(# - Quotient[#[[pivotcolumnindex]], pivotentry] pivotrow &) /@ Take[matrix, pivotrowindex - 1],
					{pivotrow},
					(* The pivot entry isn't necessarily invertible modulo the modulus, but dividing as integers gives the appropriate multiple of the pivot row. *)
					(# - #[[pivotcolumnindex]]/pivotentry pivotrow &) /@ Drop[matrix, pivotrowindex]
				],
				modulus
			];
			pivotrowindex++
		],
		{pivotcolumnindex, 1, Length[First[matrix]]}
	];
	matrix
]
*)
(* algorithm from Storjohann--Mulders *)
(* not in use *)
ModularRowReduce[m_?MatrixQ, modulus_] :=
Module[{matrix = m, rowcount, columncount, pivotrow, pivotentry, columnindex, rowindex},
	{rowcount, columncount} = Dimensions[matrix];
	If[rowcount < columncount,
		matrix = PadRight[matrix, {columncount, columncount}]
	];
	(* Put the matrix in upper triangular form. *)
	Do[
		(* Clear an entry below the diagonal by applying an invertible matrix that replaces the diagonal entry above it with their gcd. *)
		matrix[[{columnindex, rowindex}]] = Mod[
			ModularExtendedGCDMatrix[matrix[[columnindex, columnindex]], matrix[[rowindex, columnindex]], modulus].matrix[[{columnindex, rowindex}]],
			modulus
		],
		{columnindex, 1, columncount},
		{rowindex, columnindex + 1, Length[matrix]}
	];
	(* Put the matrix in Howell form. *)
	matrix = PadRight[matrix, {Length[matrix] + 1, columncount}];
(*
Print["upper triangular form:"];
Print[matrix//MatrixForm];
*)
	Do[
(*
Print["pivoting on row ", columnindex];
*)
		If[matrix[[columnindex, columnindex]] != 0,
			(* Remove the invertible factor of the pivot entry. *)
(* XXX Does wrapping this in  Mod[ , modulus]  help or hurt in terms of speed? *)
			pivotrow = Mod[
				ModularUnitInverse[matrix[[columnindex, columnindex]], modulus] matrix[[columnindex]],
				modulus
			];
(*
Print["pivot row: ", pivotrow];
*)
			pivotentry = pivotrow[[columnindex]];
			matrix = Mod[
				Join[
					(# - Quotient[#[[columnindex]], pivotentry] pivotrow &) /@ Take[matrix, columnindex - 1],
					{pivotrow},
					(*(# - #[[pivotcolumnindex]]/pivotentry pivotrow &) /@ *)Take[matrix, {columnindex + 1, -2}],
					{(modulus/GCD[pivotentry, modulus]) pivotrow}
				],
				modulus
			]
			,
			matrix[[-1]] = matrix[[columnindex]]
		];
(*
Print[matrix//MatrixForm];
Print["begin inner loop (affecting last row)"];
*)
		Do[
(*
Print[Tab, "row ", rowindex];
*)
			(* Clear an entry in the bottom row by applying an invertible matrix that replaces an entry above it with their gcd. *)
			matrix[[{rowindex, -1}]] = Mod[
				ModularExtendedGCDMatrix[matrix[[rowindex, rowindex]], matrix[[-1, rowindex]], modulus].matrix[[{rowindex, -1}]],
				modulus
			](*;Print[Tab, matrix//MatrixForm]*),
			{rowindex, columnindex + 1, columncount}
		]
		,
		{columnindex, 1, columncount}
	];
	(* Move zero rows to the bottom. *)
	PadRight[DeleteCases[matrix, {0 ..}], {columncount, columncount}]
]

(*
ModularNullSpace[matrix_, modulus_] :=
Module[{dimensions = Dimensions[matrix], nullspacesolution, Ccount, variables, x},
	variables = Thread[Subscript[x, Range[Last[dimensions]]]];
	nullspacesolution = First[Solve[matrix.variables == ConstantArray[0, First[dimensions]], variables, Modulus -> modulus]];
	If[Length[nullspacesolution] == 0,
		IdentityMatrix[Last[dimensions]]
		,
		Ccount = Replace[
			Max[Cases[nullspacesolution, C[i_] :> i, Infinity]],
			-Infinity -> 0
		];
		Transpose[(Function[i, Coefficient[#, C[i]]] /@ Range[Ccount] &) /@ (variables /. nullspacesolution)]
	]
]
*)
(* code from danl *)
ModularNullSpace[matrix_, modulus_] :=
Module[{newmat, nulls, nr, nc},
	{nr, nc} = Dimensions[matrix];
	newmat = Transpose[Join[matrix, modulus IdentityMatrix[nr], 2]];
	newmat = Join[newmat, IdentityMatrix[Length[newmat]], 2];
	nulls = Select[
		HermiteDecomposition[newmat][[2]],
		#[[1 ;; nr]] == ConstantArray[0, nr] &
	];
	DeleteCases[Mod[nulls[[All, nr + 1 ;; nr + nc]], modulus], {(0) ..}]
]

(* not in use; similar to ModularNullSpaceVector; replaced by VectorReduceMod
(* This subtracts from a vector an element of the null space of a matrix that agrees with the vector on entries corresponding to non-pivot columns.
   It assumes the matrix is in row echelon form and has no zero rows. *)
ModularNullSpaceReduce[vector_, matrix_, pivotcolumnindices_, modulus_] :=
Module[{annihilator = {}, rowindex, columnindex, pivotentry},
	{rowindex, columnindex} = Dimensions[matrix];
	While[columnindex > 0,
		If[MemberQ[pivotcolumnindices, columnindex],
			pivotentry = matrix[[rowindex, columnindex]];
			PrependTo[
				annihilator,
				vector[[columnindex]] - Mod[
					(* This  +  came from  (-1)*(-1) . *)
					vector[[columnindex]] + (Drop[matrix[[rowindex]], columnindex]/pivotentry).annihilator,
					modulus/pivotentry
				]
			];
			rowindex--
			,
			PrependTo[annihilator, vector[[columnindex]]]
		];
		columnindex--
	];
	Mod[vector - annihilator, modulus]
]
*)

(* ModularNullSpaceVector finds an element of the null space of a matrix that agrees with a given vector on entries corresponding to non-pivot columns.
   It assumes the matrix is in row echelon form and has no zero rows. *)
(* XXX TODO This gives a vector with non-integer entries:
In[290]:= IntegerSequences`Private`ModularNullSpaceVector[{0, 0, 0, 1}, {{1, 0, 1, 1}, {0, 1, 1, 3}, {0, 0, 2, 7}}, {1, 2, 3}, 8]
Out[290]= {13/2, 9/2, 1/2, 1}
*)
ModularNullSpaceVector[vector_, matrix_, pivotcolumnindices_, modulus_] :=
Module[{annihilator = {}, rowindex, columnindex, pivotentry},
	{rowindex, columnindex} = Dimensions[matrix];
	While[columnindex > 0,
		If[MemberQ[pivotcolumnindices, columnindex],
			pivotentry = matrix[[rowindex, columnindex]];
			PrependTo[
				annihilator,
				Mod[
					(-Drop[matrix[[rowindex]], columnindex]/pivotentry).annihilator,
					modulus/pivotentry
				]
			];
			rowindex--
			,
			PrependTo[annihilator, vector[[columnindex]]]
		];
		columnindex--
	];
	annihilator
]

(* PlausibleVariableQ[n + 2]  and  PlausibleVariableQ[n^2]  evaluate to  True . *)
PlausibleVariableQ[n_] :=
	!ListQ[n] && !NumericQ[n]

RaggedArrayDepth[array_] :=
Module[{depth = Depth[array], i = 0},
	While[
		(* This depth check prevents an infinite loop for  RaggedArrayDepth[{}] . *)
		i <= depth - 2 && !MemberQ[array, Except[_List], {i}],
		i++
	];
	i
]

SetAttributes[RationalExponent, Listable]
RationalExponent[r : _Integer | _Rational, 0] := 0
RationalExponent[r : _Integer | _Rational, 1] := Infinity
RationalExponent[n_Integer, b_Integer?Positive] :=
	IntegerExponent[n, b]
RationalExponent[r_Rational, b_Integer?Positive] :=
	IntegerExponent[Numerator[r], b] - IntegerExponent[Denominator[r], b]

SetAttributes[RationalMod, Listable]
RationalMod[r : _Integer | _Rational, modulus_Integer?Positive, offset_Integer : 0] /; CoprimeQ[Denominator[r], modulus] :=
	Mod[Numerator[r] PowerMod[Denominator[r], -1, modulus], modulus, offset]

Swap[expression_, {i_, j_}] :=
	ReplacePart[
		expression,
		{
			i -> expression[[j]],
			j -> expression[[i]]
		}
	]

Trim[array_List] :=
	Trim[array, {1, RaggedArrayDepth[array] - 1}]
Trim[array_, {levelmin_Integer?NonNegative, levelmax_Integer?NonNegative}] :=
	Fold[
		Function[{expr, level},
			With[{length = Min[Map[Length, expr, {level}]]},
				Map[Take[#, length] &, expr, {level}]
			]
		],
		array,
		Range[levelmin, levelmax]
	]

Unriffle[{}, m : (_Integer?Positive) : 2] := ConstantArray[{}, m]
Unriffle[list_List, m : (_Integer?Positive) : 2] :=
Module[{p},
	Transpose[Partition[list, m, m, {1, 1}, p]] /. p -> Sequence[]
]

UnpadRight[array_, pattern_ : 0] :=
	UnpadRight[array, pattern, ArrayDepth[array]]
UnpadRight[array_, pattern_, level_Integer?Positive] :=
	UnpadRight[array, pattern, {1, level}]
UnpadRight[array_, pattern_, {level_Integer?Positive}] :=
	UnpadRight[array, pattern, {level, level}]
UnpadRight[list_List, pattern_, {1, 1}] :=
	Drop[list, -LengthWhile[Reverse[list], MatchQ[pattern]]]
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

(* should this be ModularVectorReduce?  Anyway it should parallel LaurentPolynomialMod *)
VectorReduceMod[vector_, annihilatordata_, modulus_] :=
	Fold[
		Function[{v, annihilator},
			Expand[v - Quotient[v[[annihilator[[2]]]], annihilator[[1]]] annihilator[[3]], Modulus -> modulus]
		],
		vector,
		annihilatordata
	]


ExtractSubarray[array_, sequencespec_, numerationsystemlist_, (*arraydimensions_, *)dimensions_] :=
With[
	{indices = MapThread[
		Function[{prefix, numerationsystem, (*arraydimension, *)length},
			(* Compute all integers in range whose representations begin with a certain prefix. *)
(*
			Select[
				Range[0, arraydimension - 1],
				DigitList[#, numerationsystem, Length[prefix]] == prefix &,
				(* This is Infinity for the maximal subarray. *)
				length
			] + 1
*)
(*
			NumerationSystemRange[0, arraydimension - 1, prefix, numerationsystem] + 1
*)
			(* Here we use the fact that the prefix is uniformly extendable. *)
			(* TODO This almost certainly works only for linear numeration systems and may even be assuming something stronger. *)
(* TODO Does the testing done by IntegerPrepend impact performance significantly? *)
			IntegerPrepend[#, numerationsystem, prefix] + 1 & /@ Range[0, length - 1]
		],
		{sequencespec, numerationsystemlist, (*arraydimensions, *)dimensions}
	]},
	If[MemberQ[indices, {}],
(*
(* This is for numeration systems for which CanonicalPrefixQ doesn't actually work and returns True even for some noncanonical prefixes. *)
Print[
	Extract[sequencespec, Position[indices, {}, {1}]],
	" seem to not be canonical prefixes in the numeration systems ",
	Extract[numerationsystemlist, Position[indices, {}, {1}]]
];
*)
		$Failed,
		Part[array, Sequence @@ indices]
	]
]

ExtractMaximalSubarray[array_, sequencespec_, numerationsystemlist_, arraydimensions_] :=
With[
	{dimensions = MapThread[
		Function[{prefix, numerationsystem, arraydimension},
(* simpler but slower version
			Length[Select[Range[0, arraydimension - 1], DigitList[#, numerationsystem, Length[prefix]] == prefix &]]
*)
			(* TODO This almost certainly works only for linear numeration systems and may even be assuming something stronger. *)
			If[arraydimension - 1 < FromDigitList[prefix, numerationsystem],
				0,
				FromDigitList[
					Drop[
						(If[Length[#] >= Length[prefix], #, PadRight[#, Length[prefix]]] &)[
							DigitList[
								arraydimension - 1 - FromDigitList[prefix, numerationsystem],
								numerationsystem
							]
						],
						Length[prefix]
					],
					numerationsystem
				] + 1
			]
		],
		{sequencespec, numerationsystemlist, arraydimensions}
	]},
	ExtractSubarray[array, sequencespec, numerationsystemlist, dimensions]
]

FindSequenceRelations[array_, numerationsystemlist_List, sequencetype_, OptionsPattern[]] :=
Module[
	{
		dimension = Length[numerationsystemlist],
		arraydimensions,
		basissequences = {},
		basissequencedimensions = {},
		redundantsequencechains = {},
		basisterms = {},
		relations = {},
		currentsequence,
		remainingsequences,
		currentsequenceterms,
		newbasisterms,
		currentsequencerelations,
		newrelationinfo,
		dimensions,
(*
		$redunant,
*)
		failed
	},
	failed = Catch[
		(* This allows the terms of an automatic sequence to be lists. *)
		arraydimensions = Take[Dimensions[array], dimension];
		(* Each kernel sequence is specified by a list of  d  lists containing the representations of residues in the  d  numeration systems.
		   Even for dimension  d >= 2  these prefixes all have the same length (corresponding to the "exponent").
		   We only allow prefixes to which appending every canonical representation results in a canonical representation;
		   that way we can extract a subsequence without keeping an explicit record of the indices. *)
		remainingsequences = {ConstantArray[{}, dimension]};
		If[TrueQ[OptionValue[Monitor]] && 10 < $VersionNumber < 11,
			Message[Monitor::abort]
		];
		If[TrueQ[OptionValue[Monitor]] && !(10 < $VersionNumber < 11), Monitor, List][
			While[remainingsequences != {},
				currentsequence = First[remainingsequences];
(*
Print[currentsequence];
*)
				remainingsequences = Rest[remainingsequences];
(* old
				If[!MatchQ[currentsequence, _$redunant],
					(* We have already processed the (equivalent) parent of this sequence. *)
					currentsequence = First[currentsequence];
(*
Print[ArithmeticSubsequences[currentsequence, numerationsystemlist]];
*)
					AppendTo[redundantsequencechains, Most /@ currentsequence -> currentsequence];
					remainingsequences = Join[
						remainingsequences,
						Replace[
							ArithmeticSubsequences[currentsequence, numerationsystemlist],
							(* Add a wrapper to record that this kernel sequence is equivalent to its parent. *)
							{only_} :> {$redunant[only]}
						]
					];
					Continue[]
				];
*)
				If[!UniformlyExtendableSubsequenceQ[currentsequence, numerationsystemlist],
					(* Instead of processing this sequence now, we process its extension later. *)
					Replace[
						ArithmeticSubsequences[currentsequence, numerationsystemlist],
						{onlysubsequence_} :> AppendTo[redundantsequencechains, currentsequence -> onlysubsequence]
					];
					remainingsequences = Join[
						remainingsequences,
						ArithmeticSubsequences[currentsequence, numerationsystemlist]
					];
					Continue[]
				];
				If[Or @@ MapThread[FromDigitList[#1, #2] + 1 > #3 &, {currentsequence, numerationsystemlist, arraydimensions}],
					(* We won't be able to extract any terms from the array.  This occurs in the following.
					   FindAutomaticSequenceAutomaton[{1}, 2]
					   FindRegularSequenceFunction[{1}, 2]
					   With[{p = 5}, FindAutomaticSequenceAutomaton[Table[Mod[Sum[Binomial[n, k]^2, {k, 0, n}], p], {n, 0, 100}], p]] *)
					Throw[True]
				];
				currentsequenceterms = ExtractMaximalSubarray[array, currentsequence, numerationsystemlist, arraydimensions];
				If[currentsequenceterms === $Failed,
					Continue[]
				];
(* xxx this doesn't really seem to be a problem
(* Is trimming here really ideal?  In a general numeration system, it's conceivable that the current sequence has fewer known terms than a later sequence
   we haven't mapped yet.  If that sequence agrees with a basis sequence as currently chopped but not for all terms we have,
   then this is going to produce a relation which we could tell is incorrect.  For automatic sequences this can be fixed,
   but for regular sequences it's a bigger problem -- we'd either have to row reduce a bunch of different matrices (with different numbers of terms)
   or perform a second check of the relation for all terms, not just the ones being carried in the truncated list.
   But we shouldn't be TOO clever because every finite list is the prefix of a k-automatic and k-regular sequence, and we don't want to always return;
   if we're maximally clever then we'll also need a threshold for deciding when to report.  Right? *)
*)
				newbasisterms = Trim[Append[basisterms, currentsequenceterms]];
				Switch[sequencetype,
					"AutomaticSequence",
						(* Identify sequences previously known to be independent that have become dependent due to truncation.
						   Their presence isn't fatal as long as future sequences have no relation to them; allowing them lets the following evaluate.
						   FindAutomaticSequenceAutomaton[Mod[MotzkinNumber[Range[0, 2^7 - 1]], 8], 2] *)
						currentsequencerelations = First /@ Position[newbasisterms, Last[newbasisterms], {1}, Heads -> False];
						Switch[currentsequencerelations,
							{__, _, _},
								(* The current sequence is dependent on the known basis sequences, but we don't know which. *)
								Throw[True],
							{_, _} /;
									(* Do a final verification to prevent truncation errors (not necessary in base k but can arise in general numeration systems).
									   If the test fails then the current sequence is really new, since it doesn't agree with any other basis sequence. *)
									(
										newrelationinfo = basissequences[[First[currentsequencerelations]]];
										dimensions = MapThread[
											Min,
											{Dimensions[currentsequenceterms], basissequencedimensions[[First[currentsequencerelations]]]}
										];
										Or[
											dimensions == Dimensions[Last[newbasisterms]],
											(* We really only need to check terms that we haven't already verified, but they're not easy to extract. *)
											Equal[
												Take[currentsequenceterms, Sequence @@ dimensions],
												ExtractSubarray[array, newrelationinfo, numerationsystemlist, (*arraydimensions, *)dimensions]
											]
										]
									),
								(* The current sequence is dependent on the known basis sequences, and we know which. *)
								AppendTo[relations, currentsequence -> newrelationinfo],
							_,
								(* The current sequence is independent of the known basis sequences, so add it as a new basis sequence. *)
								AppendTo[basissequences, currentsequence];
								AppendTo[basissequencedimensions, Dimensions[currentsequenceterms]];
								basisterms = newbasisterms;
								remainingsequences = Join[
									remainingsequences,
(* old
									Replace[
										ArithmeticSubsequences[currentsequence, numerationsystemlist],
										(* Add a wrapper to record that this kernel sequence is equivalent to its parent. *)
										{only_} :> {$redunant[only]}
									]
*)
									ArithmeticSubsequences[currentsequence, numerationsystemlist]
								]
						],
					"RegularSequence",
						(* Identify sequences previously known to be independent that have become dependent due to truncation.
						   Their presence isn't fatal as long as future sequences have no relation to them. *)
						currentsequencerelations = DeleteCases[
							(* I probably shouldn't need to row reduce from scratch every time, since all information in row reducing
							   moves down and to the right.  But because of the flattening necessary for multidimensional sequences
							   there's no easy way of removing the undesired rows from the reduced matrix. *)
							RowReduce[Transpose[Flatten[#, dimension - 1] & /@ newbasisterms]],
(* Here's where I could restrict to only look for relations between prefixes that have the same suffix extensions.
   (How does that interact with the redundantsequencechains business?)
   But now I decided I'm going to only consider fully extendable prefixes everywhere.
							RowReduce[Transpose[
								Flatten[#, dimension - 1] & /@ FlatPick[
									newbasisterms,
									SubsequenceClass[#, numerationsystemlist] & /@ Append[basissequences, currentsequence],
									SubsequenceClass[currentsequence, numerationsystemlist]
								]
							]],
*)
							{___, 0}
						];
(*
Print[Tab, MatrixForm@currentsequencerelations];
*)
						Switch[currentsequencerelations,
							{___, {0 ..., 1, ___, Except[0], __}, ___},
								(* The current sequence is dependent on the known basis sequences, but we don't know which. *)
(*
Print[Tab, Style["throwing:", Red]];
Print[Tab, MatrixForm@currentsequencerelations];
*)
								Throw[True],
							{{0 ..., 1, 0 ..., _} ..} /;
									(* Do a final verification to prevent truncation errors (not necessary in base k but can arise in general numeration systems).
									   If the test fails then the current sequence is really independent of all others, since xxx TODO *)
									(
										newrelationinfo = Replace[
											currentsequencerelations,
											{zeros : (0 ...), 1, ___, coefficient_} :>
												(Length[{zeros}] + 1 -> coefficient),
											{1}
										];
										dimensions = MapThread[
											Min,
											Join[
												{Dimensions[currentsequenceterms]},
												basissequencedimensions[[First /@ newrelationinfo]]
											]
										];
										Or[
											dimensions == Dimensions[Last[newbasisterms]],
											(* We really only need to check terms that we haven't already verified, but they're not easy to extract. *)
											Equal[
												Take[currentsequenceterms, Sequence @@ dimensions],
												Dot[
													Last /@ newrelationinfo,
													ExtractSubarray[array, #, numerationsystemlist, (*arraydimensions, *)dimensions] & /@
														basissequences[[First /@ newrelationinfo]]
												]
											]
										]
									),
								(* The current sequence is dependent on the known basis sequences, and we know which. *)
(*
Print[Tab, Style["new relation:", Red]];
Print[Tab, currentsequence -> Normal[SparseArray[newrelationinfo]]];
*)
								AppendTo[relations, currentsequence -> Normal[SparseArray[newrelationinfo]]],
							{} /;
									(* Do a final verification to prevent truncation errors (not necessary in base k but can arise in general numeration systems).
									   If the test fails then the current sequence is really independent of all others, since xxx TODO *)
									Or[
										Dimensions[currentsequencerelations] == Dimensions[Last[newbasisterms]],
										(* We really only need to check terms that we haven't already verified, but they're not easy to extract. *)
										currentsequencerelations == ConstantArray[0, Dimensions[currentsequencerelations]]
									],
								(* The current sequence is the zero sequence. *)
								AppendTo[relations, currentsequence -> {}],
							_,
(*
Print[Tab, Style["adding new sequence", Red]];
If[currentsequence == {{1,0,0}},
	Print[Tab, MatrixForm@currentsequencerelations];
];
*)
								(* The current sequence is independent of the known basis sequences, so add it as a new basis sequence. *)
								AppendTo[basissequences, currentsequence];
								AppendTo[basissequencedimensions, Dimensions[currentsequenceterms]];
								basisterms = newbasisterms;
								remainingsequences = Join[
									remainingsequences,
(* old
									Replace[
										ArithmeticSubsequences[currentsequence, numerationsystemlist],
										(* Add a wrapper to record that this kernel sequence is equivalent to its parent. *)
										{only_} :> {$redunant[only]}
									]
*)
									ArithmeticSubsequences[currentsequence, numerationsystemlist]
								]
						]
				]
			],
			Column[{
				Row[{"Number of basis elements: ", Length[basissequences]}],
				Row[{"Number of relations: ", Length[relations]}],
				Row[{"Number of remaining sequences: ", Length[remainingsequences] + 1}]
			}]
		];
		False
	];
(* This is useful for printing partial relations.
If[TrueQ[OptionValue[Monitor]],
	Print["basissequences: ", Map[Row, basissequences, {2}](*Interpretation[Multicolumn[Map[Row, basissequences, {2}]], Evaluate@basissequences]*)];
	Print["relations: ",
		Switch[sequencetype,
			"AutomaticSequence",
				Multicolumn[Map[Row, relations, {3}], 4],
			"RegularSequence",
				Multicolumn[MapAt[Row /@ # &, #, 1] & /@ MapAt[PadRight[#, Length[basissequences]] &, 2] /@ relations, 4]
(* this isn't right
Equal @@@ Map[
	SymbolicSubsequence[#, numerationsystemlist, Global`s[Global`n]] &,
	relations,
	{2}
]
*)
		]
	];
	If[redundantsequencechains != {},
		Print["redundantsequencechains: ", Column[Map[Row, redundantsequencechains, {3}]]]
	]
];
*)
	{
		If[failed,
			$Failed,
			Switch[sequencetype,
				"AutomaticSequence",
					relations,
				"RegularSequence",
					MapAt[PadRight[#, Length[basissequences]] &, 2] /@ relations
			]
		],
		basissequences,
		redundantsequencechains
	}
]
Options[FindSequenceRelations] = {Monitor -> False}

$BaumSweetAutomaton =
	Automaton[
		{{1 -> 2, 0}, {1 -> 1, 1}, {2 -> 1, 0}, {2 -> 3, 1}, {3 -> 3, 0}, {3 -> 3, 1}},
		1,
		{1 -> 1, 2 -> 1, 3 -> 0}
	]
$RudinShapiroAutomaton =
	Automaton[
		{{1 -> 1, 0}, {1 -> 2, 1}, {2 -> 1, 0}, {2 -> 3, 1}, {3 -> 4, 0}, {3 -> 2, 1}, {4 -> 4, 0}, {4 -> 3, 1}},
		1,
		{1 -> 1, 2 -> 1, 3 -> -1, 4 -> -1}
	]
$ThueMorseAutomaton =
	Automaton[
		{{1 -> 1, 0}, {1 -> 2, 1}, {2 -> 2, 0}, {2 -> 1, 1}},
		1,
		{1 -> 0, 2 -> 1}
	]

$AutomatonOutputRulesPattern =
	Except[
		(* This doesn't exclude options inside a list, such as {InputAlphabet -> {a, b}}. *)
		InputAlphabet -> _,
		{(_Rule | _RuleDelayed) ...} | _Rule | _RuleDelayed | _?AssociationQ | _?DispatchQ
	]

IndexAutomaton[automaton_Automaton] :=
With[{statelist = AutomatonStateList[automaton]},
	AutomatonStateReplace[automaton, Thread[statelist -> Range[Length[statelist]]]]
]

(* AutomatonInputAlphabetInsert adds variables that don't affect the automaton behavior (or are all zeros, or whatever depending on the fourth argument). *)
AutomatonInputAlphabetInsert[
	Automaton[edges_, initialstate_, outputrules_, InputAlphabet -> inputalphabet_],
	numerationsystem_?PositiveNumerationSystemQ,
	freevariablepositions_,
	paddingvalue_
] :=
	Automaton[
		MapAt[InsertPart[#, freevariablepositions -> paddingvalue] &, 2] /@ edges,
		initialstate,
		outputrules,
		InputAlphabet -> Sort[Join @@ Outer[
			InsertPart[#1, Thread[freevariablepositions -> #2]] &,
			inputalphabet,
			Tuples[NumerationSystemDigitList[numerationsystem], Length[freevariablepositions]],
			1
		]]
	]

(* TODO AutomatonInputSymbolQ doesn't necessarily return True for every pattern-free expression, but we're using it as though it does. *)
AutomatonInputSymbolQ[list_List] := And @@ AutomatonInputSymbolQ /@ list
AutomatonInputSymbolQ[_?AtomQ] := True
AutomatonInputSymbolQ[_?NumericQ] := True
(*
AutomatonInputSymbolQ[TransitionSequence[]] := True
*)
AutomatonInputSymbolQ[_] := False

(* AutomatonPadRight turns rejecting states from which an accepting state can be reached by reading some (positive) number of 0 tuples into accepting states,
   so that all representations of integers are accepted. *)
AutomatonPadRight[
	automaton : Automaton[edges_, initialstate_, outputrules_List, InputAlphabet -> inputalphabet_],
	arity_
] :=
Module[{statelist, acceptingstatelist, graph},
	statelist = AutomatonStateList[automaton];
	acceptingstatelist = Select[statelist, Replace[#, outputrules] &];
	graph = Graph[statelist, Reverse /@ First /@ Select[edges, MatchQ[ConstantArray[0, arity], Last[#]] &]];
	Automaton[
		edges,
		initialstate,
		DeleteDuplicatesBy[
			(* This requires  outputrules  to be a list. *)
			Join[Thread[Complement[VertexOutComponent[graph, acceptingstatelist], acceptingstatelist] -> True], outputrules],
			First
		],
		InputAlphabet -> inputalphabet
	]
]

(* This again assumes that all the edge labels have the same length (with no Repeated patterns or anything funny). *)
AutomatonPermute[
	Automaton[edges_, initialstate_, outputrules_, InputAlphabet -> inputalphabet_],
	variables_,
	permutation_
] :=
	Automaton[
		MapAt[Permute[#, permutation] &, 2] /@ edges,
		initialstate,
		outputrules,
		InputAlphabet -> (Permute[#, permutation] &) /@ inputalphabet
	]

AutomatonReachableStateList[
	Automaton[edges_, initialstate_, ___],
	inputalphabet_
] :=
	VertexOutComponent[
		Graph[
			If[MatchQ[edges, {{_, _?AutomatonInputSymbolQ} ..}],
				(* No edge labels contain patterns. *)
				Cases[edges, {rule_, Alternatives @@ inputalphabet} :> rule]
				,
				(* Some edge labels contain patterns. *)
				(* MemberQ supports patterns in its second argument, so this works with general edge labels (including patterns). *)
				First /@ Select[edges, MemberQ[inputalphabet, Last[#]] &]
			]
		],
		initialstate
	]

(* AutomatonStateReplace renames the states in an automaton. *)
AutomatonStateReplace[
	automaton : Automaton[edges_, initialstate_, outputrules : $AutomatonOutputRulesPattern, automatonoptions___],
	rules_
] :=
	Automaton[
		MapAt[Replace[#, rules, {1}] &, 1] /@ edges,
		Replace[initialstate, rules],
		(* This expands any output rules with patterns. *)
(* This version doesn't work because of the way  Function[n, Replace[n, s_ :> s] -> n][1]  evaluates.
		Function[state, Replace[state, rules] -> Replace[state, outputrules]] /@ AutomatonStateList[automaton],
*)
		(Replace[#, rules] -> Replace[#, outputrules] &) /@ AutomatonStateList[automaton],
		automatonoptions
	]
AutomatonStateReplace[
	Automaton[edges_, initialstate_, automatonoptions___],
	rules_
] :=
	Automaton[
		MapAt[Replace[#, rules, {1}] &, 1] /@ edges,
		Replace[initialstate, rules],
		automatonoptions
	]


(*** numeration system support functions ***)

(* ArithmeticSubsequences determines the possible ways of extending a tuple of prefixes by one digit each so that there exist canonical representations with the new prefixes. *)
ArithmeticSubsequences[prefixlist_, numerationsystemlist_] :=
	Tuples[MapThread[
		Function[{prefix, numerationsystem},
			Select[
				Append[prefix, #] & /@ NumerationSystemDigitList[numerationsystem],
				CanonicalPrefixQ[#, numerationsystem] &
			]
		],
		{prefixlist, numerationsystemlist}
	]]

(* As currently used, this only needs to check for a bad pattern at the end of the prefix.  It also assumes that the alphabet is correct. *)
(* All the numeration systems we currently support have the property that if a kernel sequence has a unique arithmetic subsequence,
   then that subsequence has at least two arithmetic subsequences.  That is, chains of redundant sequences always have length 2.
   If we add a system where this isn't the case (e.g. 1 is always followed by 00) then I'll have to generalize the use of  redundantsequencechains  throughout. *)
CanonicalPrefixQ[{___, 1, 1}, "Fibonacci"] :=
	False
CanonicalPrefixQ[{___, 1, 1, 1}, "Tribonacci"] :=
	False
(*
CanonicalPrefixQ[{__, _, 2}, LinearNumerationSystem[{2, 0, 0, -1}, {1, 3, 7, 14}]] :=
	False
*)
(* I guess in general there will be an automaton accepting the canonical representations.
CanonicalPrefixQ[prefix_, LinearNumerationSystem[kernel_, initialterms_]] :=
	xxx
*)
CanonicalPrefixQ[_, _] :=
	True

(* not in use
(* ExtendSubsequence appends zeros until a uniformly extendable sequence is obtained.
   For the numeration systems currently implemented, it could get by with appending zeros at most once. *)
ExtendSubsequence[prefixlist_, numerationsystemlist_] :=
Module[{extendedprefixlist = prefixlist},
	While[!UniformlyExtendableSubsequenceQ[extendedprefixlist, numerationsystemlist],
		extendedprefixlist = Append[#, 0] & /@ prefixlist
	];
	extendedprefixlist
]
*)

(* Ideally we would support base 1 throughout.  But every numeration system supported by RegularSequence needs to have a 0 digit so we can pad to arbitrary length.
   Base 1 will also mess up the $redunant stuff in FindSequenceRelations (although this is commented out now, so maybe it's okay?). *)
NumerationSystemBasisFunction[base_Integer /; Abs[base] >= 2] :=
	base^# &
NumerationSystemBasisFunction["Fibonacci"] =
	Fibonacci[# + 2] &
NumerationSystemBasisFunction["Tribonacci"] =
	Tribonacci[# + 3] &
(*
NumerationSystemBasisFunction[LinearNumerationSystem[{2, 0, 0, -1}, {1, 3, 7, 14}]] =
	TribonacciPartialSum
*)
NumerationSystemBasisFunction[LinearNumerationSystem[kernel_, initialterms_]] := NumerationSystemBasisFunction[LinearNumerationSystem[kernel, initialterms]] =
(* LinearRecurrence is slower than MatrixPower for computing a single term.
	First[LinearRecurrence[kernel, initialterms, {# + 1, # + 1}]] &
*)
(* xxx But this is still too slow for use in ExtractSubarray.
   We need to remember values, so maybe I need a NumerationSystemBasisElement instead, which I think is what I had earlier. *)
With[{matrix = Append[Rest[IdentityMatrix[Length[kernel]]], Reverse[kernel]]},
	First[MatrixPower[matrix, #].initialterms] &
]

(* If we introduce any numeration system where the digit list does not contain 0, then PadRight in RegularSequence will need to change.
   More generally, if the digit list isn't {0, 1, ..., m} then we'll need to look up the position of each digit in the digit list before passing to Part to extract matrices or terms in an array. *)
NumerationSystemDigitList[base_Integer /; Abs[base] >= 2] :=
	Range[0, Abs[base] - 1]
NumerationSystemDigitList["Fibonacci" | "Tribonacci"] :=
	{0, 1}
(*
NumerationSystemDigitList[LinearNumerationSystem[{2, 0, 0, -1}, {1, 3, 7, 14}]] :=
	{0, 1, 2}
*)
(* For a general linear numeration system the nth digit can be at most  Floor[(U_{n+1} - 1)/U_n] .  But how do I compute the max of those?  (Or even bound that max from above?)
NumerationSystemDigitList[LinearNumerationSystem[kernel_, initialterms_]] :=
	Range[0, xxx]
*)

(* not in use
(* This almost certainly only works for linear numeration systems and may even be assuming something stronger. *)
NumerationSystemRange[(*nmin_Integer?NonNegative*)0, nmax_Integer, prefix_List, numerationsystem_?PositiveNumerationSystemQ] /;
		SubsetQ[NumerationSystemDigitList[numerationsystem], prefix] && UniformlyExtendablePrefixQ[prefix, numerationsystem] :=
(*
Module[{n = 0, sequenceelement},
(*
	SelectFirst[Range[n, 0, -1], DigitList[#1, numerationsystem, Length[prefix]] == prefix &]
*)
	Reap[
		While[True,
			(* This is essentially IntegerPrepend, but IntegerPrepend would execute a test each time.  [not anymore]
			   TODO Would the performance really take a noticable hit? *)
			sequenceelement = FromDigitList[Join[prefix, DigitList[n, numerationsystem]], numerationsystem];
			If[sequenceelement > nmax, Break[]];
			Sow[sequenceelement];
			n++
		]
	][[2, 1]]
]
*)
	If[nmax < FromDigitList[prefix, numerationsystem],
		{},
(* TODO Does the testing done by IntegerPrepend impact performance significantly? [no test anymore] *)
		IntegerPrepend[#, numerationsystem, prefix] & /@ Range[
			0,
(*
			SelectFirst[Range[nmax, 0, -1], DigitList[#1, numerationsystem, Length[prefix]] == prefix &]
*)
			FromDigitList[
				Drop[
					(If[Length[#] >= Length[prefix], #, PadRight[#, Length[prefix]]] &)[
						DigitList[nmax - FromDigitList[prefix, numerationsystem], numerationsystem]
					],
					Length[prefix]
				],
				numerationsystem
			]
		]
	]
*)

NumerationSystemQ[base_Integer /; Abs[base] >= 2] :=
	True
(* Tribonacci is commented out here because ReduceAutomaton doesn't fully support it.  Actually TimesAutomaton doesn't even support Fibonacci. *)
NumerationSystemQ["Fibonacci"(* | "Tribonacci"*)] :=
	True
NumerationSystemQ[_] :=
	False

(* not in use
(* PrefixClass determines which prefixes are extendable by the same set of words. *)
PrefixClass[_, base_Integer /; base >= 2] :=
	0
PrefixClass[{} | {___, 0}, "Fibonacci"] :=
	0
PrefixClass[{___, 1}, "Fibonacci"] :=
	1
PrefixClass[{} | {___, 0}, "Tribonacci"] :=
	0
PrefixClass[{1} | {___, 0, 1}, "Tribonacci"] :=
	1
PrefixClass[{___, 1, 1}, "Tribonacci"] :=
	2

SubsequenceClass[prefixlist_, numerationsystemlist_] :=
	MapThread[
		PrefixClass,
		{
			(* XXX Do we need to extend prefixes with unique extensions?  For example, in Tribonacci we append 0 to prefixes ending in 11. *)
			prefixlist,
			numerationsystemlist
		}
	]
*)

(* Ideally we wouldn't need PositiveNumerationSystemQ because everything that passes NumerationSystemQ would be supported. *)
PositiveNumerationSystemQ[base_Integer /; base >= 2] :=
	True
(* Tribonacci is commented out here because ReduceAutomaton doesn't fully support it.  Actually TimesAutomaton doesn't even support Fibonacci. *)
PositiveNumerationSystemQ["Fibonacci"(* | "Tribonacci"*)] :=
	True
(*
PositiveNumerationSystemQ[LinearNumerationSystem[{2, 0, 0, -1}, {1, 3, 7, 14}]] :=
	True
*)
PositiveNumerationSystemQ[_] :=
	False

(* The specification {prefix1, prefix2, ...} represents the kernel sequence a[k1^Length[prefix1] n1 + FromDigitList[prefix1, k1], ...]. *)
SymbolicSubsequence[prefixlist_, numerationsystemlist_, a_[nsequence__]] :=
	a @@ MapThread[
		IntegerPrepend,
		{
			{nsequence},
(* xxx I suspect I don't want to extend here anymore.
			(* Extend prefixes with unique extensions.  For example, in Tribonacci we append 0 to prefixes ending in 11. *)
			Replace[
				ArithmeticSubsequences[prefixlist, numerationsystemlist],
				{
					{only_} :> only,
					_ :> prefixlist
				}
			],
*)
			numerationsystemlist,
			prefixlist
		}
	]

(* xxx temp (for speed) until we remember values of basis elements for linear numeration systems
TribonacciPartialSum[n_] := TribonacciPartialSum[n] =
	First[MatrixPower[{{0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}, {-1, 0, 0, 2}}, n].{1, 3, 7, 14}]
*)

(* UniformlyExtendablePrefixQ determines whether a canonical prefix is extendable by all canonical suffixes. *)
UniformlyExtendablePrefixQ[{___, 1}, "Fibonacci" | "Tribonacci"] :=
	False
UniformlyExtendablePrefixQ[_, _] :=
	True

UniformlyExtendableSubsequenceQ[prefixlist_, numerationsystemlist_] :=
	And @@ MapThread[
		UniformlyExtendablePrefixQ,
		{
			prefixlist,
			numerationsystemlist
		}
	]

(*** end numeration system support functions ***)


AutomaticSequenceNumerationSystemList[AutomaticSequence[_, numerationsystemlist_List]] :=
	numerationsystemlist
AutomaticSequenceNumerationSystemList[AutomaticSequence[_, numerationsystem_]] :=
	{numerationsystem}
(* This determines the numeration system from the input alphabet, but it doesn't check that every digit actually appears in the input alphabet. *)
AutomaticSequenceNumerationSystemList[AutomaticSequence[automaton_]] :=
With[{inputalphabet = AutomatonInputAlphabet[automaton]},
	Replace[
		Which[
			MatchQ[inputalphabet, {__Integer?NonNegative}],
				{Max[inputalphabet] + 1},
			MatchQ[inputalphabet, {{__Integer?NonNegative} ..}] && Equal @@ Length /@ inputalphabet,
				Max /@ Transpose[inputalphabet] + 1,
			True,
				$Failed
		],
		{___, 1, ___} -> $Failed
	]
]

RegularSequenceNumerationSystemList[RegularSequence[_, _, _, numerationsystemlist_List]] :=
	numerationsystemlist
RegularSequenceNumerationSystemList[RegularSequence[_, _, _, numerationsystem_]] :=
	{numerationsystem}
RegularSequenceNumerationSystemList[RegularSequence[_, matrixarray_, _]] :=
	Drop[Dimensions[matrixarray], -2]

RegularSequenceEqualLengthsQ[RegularSequence[u_, matrixarray_, v_, ___]] :=
	Equal @@ DeleteCases[
		Join[
			Flatten[Map[Dimensions, matrixarray, {ArrayDepth[matrixarray] - 2}]],
			{
				If[MatchQ[u, _List], Length[u], Missing["Unknown"]],
				If[MatchQ[v, _List], Length[v], Missing["Unknown"]]
			}
		],
		_Missing
	]

RegularSequenceObjectQ[sequence : RegularSequence[_?VectorQ, matrixarray : {__}, _?VectorQ]] :=
	And[
(* necessary or redundant?  doesn't it actually need to be >= 3?
		ArrayDepth[matrixarray] >= 2,
*)
		ArrayQ[matrixarray, ArrayDepth[matrixarray] - 2, MatrixQ],
		RegularSequenceEqualLengthsQ[sequence]
	]
RegularSequenceObjectQ[sequence : RegularSequence[_?VectorQ, matrixarray : {__}, _?VectorQ, numerationsystemlist : {__?NumerationSystemQ}]] :=
	And[
(* necessary or redundant?  doesn't it actually need to be >= 3?
		ArrayDepth[matrixarray] >= 2,
*)
		ArrayQ[matrixarray, ArrayDepth[matrixarray] - 2, MatrixQ],
		Drop[Dimensions[matrixarray], -2] == (Length[NumerationSystemDigitList[#]] &) /@ numerationsystemlist,
		RegularSequenceEqualLengthsQ[sequence]
	]
RegularSequenceObjectQ[RegularSequence[u_, matrixarray_, v_, numerationsystem : Except[_List]]] :=
	RegularSequenceObjectQ[RegularSequence[u, matrixarray, v, {numerationsystem}]]
RegularSequenceObjectQ[_] = False

SequenceNumerationSystemList[(BaumSweet | RudinShapiro | ThueMorse | SternBrocot | BitLength | BitShiftRight)[argument_], n_] /; !FreeQ[argument, n] :=
	{2}
(* These don't test that the numeration system is valid, since the functions that call SequenceNumerationSystemList include a test. *)
(* XXX right?  related: *)
(* XXX Check that  s  is free of n?  Or just assume it is because if not that will be detected later? *)
SequenceNumerationSystemList[(sequence_AutomaticSequence)[argument_], n_] /; !FreeQ[argument, n] :=
With[{numerationsystemlist = AutomaticSequenceNumerationSystemList[sequence]},
	numerationsystemlist /; numerationsystemlist =!= $Failed
]
SequenceNumerationSystemList[(sequence_RegularSequence)[argument_], n_] /; !FreeQ[argument, n] :=
With[{numerationsystemlist = RegularSequenceNumerationSystemList[sequence]},
	numerationsystemlist /; numerationsystemlist =!= $Failed
]
(* xxx is this note (basically copied from PAdics`) relevant here? *)
(* SequenceNumerationSystemList just extracts the explicit numeration system argument without checking that other arguments involve the same numeration system.
   If other arguments use different numeration systems then RegularSequenceReduce just won't evaluate.  We could have RegularSequenceQ. *)
SequenceNumerationSystemList[
	Alternatives[
		DigitCount[argument_, base_, _],
		(IntegerExponent | IntegerLength)[argument_, base_ : 10]
	],
	n_
] /; !FreeQ[argument, n] :=
	{base}
SequenceNumerationSystemList[expression : _Plus | _Power | _Times | _Equal | _Greater | _GreaterEqual | _Less | _LessEqual | _Unequal | _Inequality, n_] :=
Module[{candidates, numerationsystemlist, failed},
	failed = Catch[
		candidates = SequenceNumerationSystemList[#, n] & /@ List @@ expression;
		If[MemberQ[candidates, _SequenceNumerationSystemList],
			Throw[True]
		];
		If[MatchQ[candidates, {Automatic ..}],
			numerationsystemlist = Automatic; Throw[False]
		];
		candidates = DeleteCases[candidates, Automatic];
		If[! Equal @@ Length /@ candidates,
			Throw[True]
		];
		numerationsystemlist = Which[
			SameQ @@ #,
				First[#],
			MatchQ[#, {__Integer}] && TrueQ[Element[FullSimplify[Log[Min[#], #]], Rationals]],
				Min[#],
			True,
				Throw[True]
		] & /@
			Transpose[candidates];
		False
	];
	numerationsystemlist /; !failed
]
SequenceNumerationSystemList[polynomial_, n_] /; PolynomialQ[polynomial, n] :=
	Automatic
SequenceNumerationSystemList[expression_, n_] /; FreeQ[expression, n] :=
	Automatic


(*** series support functions ***)

(* This evaluates to Missing["NotFound"] for the 0 polynomial. *)
FirstNonZeroCoefficientRule[expression_, variable_, OptionsPattern[]] :=
Module[{zeroq},
	SelectFirst[
		Sort[
			GeneralCoefficientRules[Expand[expression, Modulus -> OptionValue[Modulus]], {variable}],
			NumericalOrder[#1[[1, 1]], #2[[1, 1]]] &
		],
		If[$VersionNumber >= 12,
			(* This emits SeriesSolve::ztest1 instead of PossibleZeroQ::ztest1, but a bug prevents it from working pre-12. *)
			(
				Quiet[
					Check[
						zeroq = PossibleZeroQ[#[[2]], Method -> OptionValue[Method]],
						Message[SeriesSolve::ztest1, #[[2]]],
						PossibleZeroQ::ztest1
					],
					PossibleZeroQ::ztest1
				];
				!zeroq
			) &,
			!PossibleZeroQ[#[[2]], Method -> OptionValue[Method]] &
		]
	]
]
(* draft of code that works more generally on series-expandable expressions
FirstNonZeroCoefficientRule[expression_, variable_, OptionsPattern[]] :=
Module[{seriesaccuracyminus1 = 1},
	If[FreeQ[expression, variable],
		0 or 1,
		While[xxx,
			Replace[
				Series[expression, {variable, 0, seriesaccuracyminus1}],
				{
					SeriesData[variable, 0, coefficients_ /; !FreeQ[coefficients, variable], _, _, _] :>
						not a valid coefficient,
					SeriesData[variable, 0, {}, _, _, _] :>
						(seriesaccuracyminus1 = 2 seriesaccuracyminus1)
					SeriesData[variable, 0, {__}, minexponent_, _, denominator_] :>
						minexponent/denominator /; first coefficient is nonzero,
(*
					constant_ /; FreeQ[constant, variable] :>
						xxx,
*)
					_Series :>
						xxx
				}
			]
		]
	];
	SelectFirst[
		Sort[
			GeneralCoefficientRules[Expand[expression, Modulus -> OptionValue[Modulus]], {variable}],
			NumericalOrder[#1[[1, 1]], #2[[1, 1]]] &
		],
		!PossibleZeroQ[#[[2]], Method -> OptionValue[Method]] &
	]
]
*)
Options[FirstNonZeroCoefficientRule] = {Method -> Automatic, Modulus -> 0}

ImplicitFunctionTheoremPolynomialQ[expression_, x_, y_, OptionsPattern[]] :=
	And[
		PolynomialQ[expression, {x, y}],
		With[{modulus = OptionValue[Modulus]},
			If[modulus == 0,
				And[
					(* This condition is equivalent to the existence of a power series solution with constant term 0. *)
					(expression /. x | y -> 0) == 0,
					(D[expression, y] /. x | y -> 0) != 0
				],
				And[
					(* This condition is equivalent to the existence of a power series solution with constant term 0. *)
					Mod[expression /. x | y -> 0, modulus] == 0,
					Mod[D[expression, y] /. x | y -> 0, modulus] != 0
(* xxx or do we need this?
					GCD[D[expression, y] /. x | y -> 0, modulus] == 1
*)
				]
			]
		]
	]
Options[ImplicitFunctionTheoremPolynomialQ] = {Method -> Automatic, Modulus -> 0}

(* ImplicitFunctionTheoremRoot shifts a power series root (dropping terms) until its polynomial satisfies the conditions of the implicit function theorem,
   with the shifted root as the unique root. *)
(* ImplicitFunctionTheoremRoot doesn't terminate if the root is a multiple root of the polynomial. *)
(* We don't check that the series is actually a root of the polynomial. *)
(* xxx TODO support general series center x0 *)
ImplicitFunctionTheoremRoot[
	SeriesRoot[
		{polynomialfunction_Function, rootapproximation : HoldPattern[SeriesData][x_, x0 : 0, _List, _, _, 1]},
		options : OptionsPattern[]
	]
] :=
Module[{modulus, root, rootdata, polynomial, shiftedpolynomial, serieslist, shiftlength, y, failed},
	failed = Catch[
		modulus = OptionValue[SeriesRoot, {options}, Modulus];
		root = rootapproximation;
		rootdata = {Normal[root], SeriesAccuracy[root] - 1};
		polynomial = polynomialfunction[y];
		y = SelectFirst[
			RotateRight[Symbol /@ CharacterRange["\[FormalA]", "\[FormalZ]"], 2],
			FreeQ[polynomial, #] &,
(* xxx this exposes y... need to choose a symbol that isn't already in  polynomial .  one nice thing about AlgebraicSequence not using a Function was that i could just reuse the same variables
   should it take GeneratedParameters or something?  what does DifferenceRoot do if there's a conflict? *)
			y
		];
		shiftedpolynomial = polynomial;
		shiftlength = 0;
		While[
			!And[
				(* This prevents the wrong root from being returned when the polynomial satisfies the implicit function theorem but not for the specified root. *)
				Or[
					shiftlength >= 1,
					(First[rootdata] /. x -> x0) == 0
				],
				ImplicitFunctionTheoremPolynomialQ[shiftedpolynomial, x, y, Modulus -> modulus]
			],
			shiftlength++;
			serieslist = SeriesRootSeriesList[
				{{y, polynomial}, rootdata},
				{x, x0, shiftlength - 1},
				Modulus -> modulus
			];
			If[Length[DeleteDuplicates[serieslist]] != 1,
				Throw[True]
			];
			root = First[serieslist];
			(* If we've computed more of the root than was input, update  rootdata . *)
			If[SeriesAccuracy[root] > Last[rootdata] + 1,
				rootdata = {Normal[root], SeriesAccuracy[root] - 1};
			];
(* but really I don't want SeriesData objects from SeriesRootSeriesList; I want the polynomials *)
(* this assumes SeriesRootSeriesList output a SeriesData with the requested accuracy and not more; but i think that's a safe assumption *)
			shiftedpolynomial = polynomial /. y -> Normal[root] + x^(SeriesAccuracy[root] - 1) y;
(* xxx use PolynomialQuotientRemainder here?  PolynomialMod crashes the kernel in some situations. *)
(* xxx probably also need to use the modulus here *)
			While[PolynomialMod[shiftedpolynomial, x] === 0,
				shiftedpolynomial = Cancel[shiftedpolynomial/x]
			]
		];
		False
	];
	{
		If[{options} === {},
			SeriesRoot[Function @@ {y, shiftedpolynomial}, x],
			SeriesRoot[Function @@ {y, shiftedpolynomial}, x, Modulus -> modulus]
		],
		(* This is the polynomial that was chopped from the series. *)
		If[shiftlength == 0,
			0,
			Normal[root]
		],
		shiftlength
	} /; !failed
]

(* This assumes the exponents of y are non-negative integers, so that CoefficientRules evaluates as expected. *)
(* The output is a list whose elements are  -slope -> coefficient , sorted by decreasing exponent (negative slope). *)
NewtonPolygonEdgeCoefficientRules[polynomial_, x_, y_, OptionsPattern[]] :=
Module[{coefficientrules, convexhullcorner},
	coefficientrules = Function[
		{yexponentlist, coefficient},
		(If[MissingQ[#],
			Nothing,
			{First[yexponentlist], #[[1, 1]]} -> #[[2]]
		] &)[
			FirstNonZeroCoefficientRule[coefficient, x, Method -> OptionValue[Method], Modulus -> OptionValue[Modulus]]
		]
	] @@@ Sort[CoefficientRules[polynomial, y, Modulus -> OptionValue[Modulus]]];
	If[Length[coefficientrules] <= 1,
		{}
		,
		convexhullcorner = First[coefficientrules];
		Reap[While[
			True,
			Replace[
				Select[
					coefficientrules,
					Function[pointcoefficientpair,
						And[
							pointcoefficientpair[[1, 1]] > convexhullcorner[[1, 1]],
							AllTrue[coefficientrules, LineSide[{First[convexhullcorner], First[pointcoefficientpair]}, First[#]] >= 0 &]
						]
					]
				],
				{
					{} :>
						Break[],
					pairs_ :>
						(
							Sow[Rule[
								-Divide @@ Reverse[First[convexhullcorner] - First[Last[pairs]]],
								Total[Last /@ Join[{convexhullcorner}, pairs]]
							]];
							convexhullcorner = Last[pairs]
						)
				}
			]
		]][[2, 1]]
	]
]
Options[NewtonPolygonEdgeCoefficientRules] = {Method -> Automatic, Modulus -> 0}

(* TODO Rename this to SeriesLength? *)
(* SeriesAccuracy gives the number of known terms in a power series.
   This is the exponent in O[x]^seriesaccuracy.
   This is also 1 plus the maximum exponent known.
   This is also  seriesaccuracy  in the output of  Series[f, {x, x0, seriesaccuracy - 1}] . *)
SeriesAccuracy[HoldPattern[SeriesData][_, _, _List, _, seriesaccuracy_, 1]] :=
	seriesaccuracy

(* This assumes the input is a power series (not a Laurent series). *)
(* TODO Bug: IntegerSequences`Private`SeriesDimensions[Series[1/(1 - x - y) + z, {x, 0, 3}, {y, 0, 5}, {z, 0, 0}]] returns unevaluated. *)
SeriesDimensions[Except[_List | _SeriesData]] :=
	{}
SeriesDimensions[series_SeriesData] :=
	SeriesDimensions[{series}]
SeriesDimensions[serieslist : {HoldPattern[SeriesData][variable_, _, {__SeriesData}, _, _, 1] ..}] :=
With[{innerdimensions = SeriesDimensions[Join @@ serieslist[[All, 3]]]},
	Join[{Min[serieslist[[All, 5]]]}, innerdimensions] /; ListQ[innerdimensions]
]
SeriesDimensions[serieslist : {HoldPattern[SeriesData][variable_, _, {Except[_SeriesData] ...}, _, _, 1] ..}] :=
	{Min[serieslist[[All, 5]]]}

SetAttributes[SeriesMod, Listable]
(* TODO These contain exposed symbols:
	 IntegerSequences`Private`SeriesMod[SeriesData[x, 0, {1, 1/2, 3/2}, 0, 3, 1], 2]
	 IntegerSequences`Private`SeriesMod[SeriesData[x, 0, {a, a, a}, 0, 3, 1], 2]
*)
SeriesMod[r : _Integer | _Rational, modulus_Integer?Positive] :=
	RationalMod[r, modulus]
SeriesMod[series_SeriesData, modulus_Integer?Positive] :=
	MapAt[SeriesMod[#, modulus] &, series, 3]

(* This checks that if two modulus specifications are received then they are the same. *)
SeriesRootAlgebraicSequenceModulus[
	AlgebraicSequence[
		SeriesRoot[_, seriesrootoptions : OptionsPattern[]],
		algebraicsequenceoptions : OptionsPattern[]
	]
] :=
	Replace[
		DeleteCases[
			{
				OptionValue[AlgebraicSequence, {algebraicsequenceoptions}, Modulus],
				OptionValue[SeriesRoot, {seriesrootoptions}, Modulus]
			},
			0
		],
		{
			{} :> 0,
			{m_} :> m,
			{m_, m_} :> m,
			{m1_, m2_} :> (Message[AlgebraicSequence::mmod, m1, m2]; $Failed)
		}
	]

SeriesRootAlgebraicSequenceObjectQ[
	sequence : AlgebraicSequence[
		seriesroot : SeriesRoot[_, seriesrootoptions : OptionsPattern[]],
		algebraicsequenceoptions : OptionsPattern[]
	]
] :=
With[{modulus = SeriesRootAlgebraicSequenceModulus[sequence]},
	And[
		IntegerQ[modulus],
		If[MemberQ[seriesroot, Modulus -> _],
			SeriesRootQ[seriesroot],
			SeriesRootQ[Append[seriesroot, Modulus -> modulus]]
		]
	]
]
SeriesRootAlgebraicSequenceObjectQ[_] :=
	False

SeriesRootQ[
	SeriesRoot[
		{polynomialfunction_Function, root : HoldPattern[SeriesData][x_, x0_, _List, _, _, 1]},
		options : OptionsPattern[]
	]
] :=
Module[{modulus, seriesvariables, y},
	modulus = OptionValue[SeriesRoot, {options}, Modulus];
	seriesvariables = SeriesVariables[root];
	And[
		(* We're not currently testing this for the inner series. *)
		FreeQ[x0, x],
		PolynomialQ[polynomialfunction[y], Append[seriesvariables, y]],
(* not sufficient when there are multiple variables
		MatchQ[
			If[modulus == 0,
				polynomialfunction[root],
				SeriesMod[polynomialfunction[root], modulus]
			],
			HoldPattern[SeriesData][x, x0, {}, _, _, 1]
		]
*)
(* Use Normal before modding so that I could use Expand instead of SeriesMod? *)
		SameQ[
			Normal[If[modulus == 0,
				polynomialfunction[root],
				SeriesMod[polynomialfunction[root], modulus]
			]],
			0
		]
	]
]
SeriesRootQ[_] :=
	False

(* SeriesRootSeriesList gives all extensions of an approximate root. *)
(* The input should be a polynomial in  x,y . *)
(* Each approximate root is represented by a polynomial (possibly with rational exponents) along with the maximum exponent known. *)
SeriesRootSeriesList[{{y_, poly_}, root : {_, _}}, {x_, x0_, seriesaccuracyminus1_}, OptionsPattern[]] :=
Module[{polynomial, modulus, serieslist, coefficientrules, solutions, xminusx0, newcoefficient, c},
	polynomial = poly /. x -> xminusx0 + x0;
	modulus = OptionValue[Modulus];
	If[modulus == 0,
		c = C
	];
	serieslist = FixedPoint[
		Join @@ Function[{approximation, maxexponent},
			If[maxexponent >= seriesaccuracyminus1,
				{{approximation, maxexponent}}
				,
				coefficientrules = Select[
(* TODO issue messages from AlgebraicSequence if called from there instead of SeriesSolve? *)
					NewtonPolygonEdgeCoefficientRules[
						polynomial /. y -> approximation + newcoefficient y,
						xminusx0,
						y,
						Method -> OptionValue[Method],
						Modulus -> modulus
					],
					First[#] > maxexponent &
				];
				If[coefficientrules == {},
					{{approximation, seriesaccuracyminus1}}
					,
					coefficientrules = Select[
						coefficientrules,
						Denominator[First[#]] <= OptionValue[MaxDenominator] &
					];
					Join @@ Function[{exponent, coefficient},
						solutions = DeleteDuplicates[Solve[
							coefficient == 0,
							newcoefficient,
							Cubics -> False,
							GeneratedParameters -> c,
							Modulus -> modulus,
							Quartics -> False
						]];
						If[!FreeQ[solutions, c[1]],
							solutions = DeleteDuplicates[Replace[
								solutions,
								{newcoefficient -> value_ /; !FreeQ[value, c[1]]} :>
									Sequence @@ Table[
										{newcoefficient -> Mod[value, modulus]},
										{c[1], 0, modulus - 1}
									],
								{1}
							]]
						];
						If[MatchQ[solutions, {{}} | _Solve],
(* TODO issue messages from AlgebraicSequence if called from there instead of SeriesSolve? *)
							Message[SeriesSolve::soln, approximation /. xminusx0 -> x - x0];
							(* If this occurs on the first iteration, then Series emits Series::serlim because  maxexponent==-Infinity . *)
							(* If  FreeQ[approximation, xminusx0] , then it won't be affected by Series here and will receive full accuracy at the end. *)
							{{Series[approximation /. xminusx0 -> x - x0, {x, x0, maxexponent}], seriesaccuracyminus1}}
							,
							(* We Map here because Solve can evaluate to {} for positive modulus. *)
							({approximation + newcoefficient xminusx0^exponent /. #, exponent} &) /@
								DeleteCases[
									RootReduce[solutions],
									{newcoefficient -> 0 | 0.} /; exponent != coefficientrules[[1, 1]] || maxexponent == -Infinity
								]
						]
					] @@@ coefficientrules
				]
			]
		] @@@ # &,
		{root /. x -> xminusx0 + x0}
	];
	serieslist = Replace[
		Series[First[#] /. xminusx0 -> x - x0, {x, x0, seriesaccuracyminus1}],
		constant_ /; FreeQ[constant, x] :>
			(* The accuracy here is too high (and the last argument is wrong) if the Puiseux denominator is greater than 1.
			   For example: SeriesSolve[1 - x - 2 f[x] + f[x]^2 == 0, f[x], {x, 0, 0}] *)
			SeriesData[x, x0, {constant}, 0, seriesaccuracyminus1 + 1, 1]
	] & /@ serieslist
]
Options[SeriesRootSeriesList] = {MaxDenominator -> Infinity, Method -> Automatic, Modulus -> 0}

SeriesVariables[expression_] :=
	DeleteDuplicates[Reverse[
		Cases[expression, HoldPattern[SeriesData][variable_, __] :> variable, {0, Infinity}]
	]]

ZeroSeries[x_, seriesaccuracy_] :=
	SeriesData[x, 0, {}, seriesaccuracy, seriesaccuracy, 1]

(*** end series support functions ***)


(sequence : AlgebraicSequence[
	SeriesRoot[{polynomialfunction_Function, root : HoldPattern[SeriesData][x_, x0_, __]}, OptionsPattern[]],
	OptionsPattern[]
]?SeriesRootAlgebraicSequenceObjectQ)[n_Integer?NonNegative] :=
Module[{modulus, serieslist, y, failed},
	failed = Catch[
		modulus = SeriesRootAlgebraicSequenceModulus[sequence];
		serieslist = SeriesRootSeriesList[
			{{y, polynomialfunction[y]}, {Normal[root], SeriesAccuracy[root] - 1}},
			{x, x0, n},
			MaxDenominator -> 1,
			Modulus -> modulus
		];
		If[Length[DeleteDuplicates[serieslist]] != 1,
			Message[AlgebraicSequence::soln, polynomialfunction, root]; Throw[True]
		];
		False
	];
	Coefficient[First[serieslist], x, n] /; !failed
]
(* Unique solution with constant term 0, by the implicit function theorem. *)
AlgebraicSequence[
	polynomialfunction_Function,
	x : Except[_Rule],
	OptionsPattern[]
][n_Integer?NonNegative] :=
Module[{polynomial, serieslist, y, failed},
	failed = Catch[
		polynomial = polynomialfunction[y];
		If[!ImplicitFunctionTheoremPolynomialQ[polynomial, x, y, Modulus -> OptionValue[Modulus]],
			Message[AlgebraicSequence::ift, polynomialfunction]; Throw[True]
		];
		serieslist = SeriesRootSeriesList[
			{{y, polynomial}, {0, 0}},
			{x, 0, n},
			MaxDenominator -> 1,
			Modulus -> OptionValue[Modulus]
		];
		If[Length[DeleteDuplicates[serieslist]] != 1,
			(* Does this occur? *)
			Message[AlgebraicSequence::soln, polynomialfunction, ZeroSeries[x, 1]]; Throw[True]
		];
		False
	];
	Coefficient[First[serieslist], x, n] /; !failed
]
Options[AlgebraicSequence] = {Modulus -> 0}
SyntaxInformation[AlgebraicSequence] = {"ArgumentsPattern" -> {_, _., OptionsPattern[]}}
AlgebraicSequence::ift = "Polynomial function `1` does not satisfy the conditions of implicit function theorem. Use SeriesRoot to identify a series."
AlgebraicSequence::mmod = "Two distinct moduli `1` and `2` received."
(* Should this message also indicate that there may be no roots? *)
AlgebraicSequence::soln = "Polynomial function `1` has multiple roots near `2`. Specify more terms."

AlgebraicSequenceReduce[
	(sequence : CatalanNumber | MotzkinNumber | Fibonacci | JacobsthalNumber | LucasL | Tribonacci)[n_],
	{n_?PlausibleVariableQ}
] :=
	AlgebraicSequence[
		SeriesRoot[{
			Switch[sequence,
				CatalanNumber,
					Function[\[FormalY], \[FormalX] \[FormalY]^2 - \[FormalY] + 1],
				MotzkinNumber,
					Function[\[FormalY], \[FormalX]^2 \[FormalY]^2 + (\[FormalX] - 1) \[FormalY] + 1],
				Fibonacci,
					Function[\[FormalY], (1 - \[FormalX] - \[FormalX]^2) \[FormalY] - \[FormalX]],
				JacobsthalNumber,
					Function[\[FormalY], (1 - \[FormalX] - 2 \[FormalX]^2) \[FormalY] - \[FormalX]],
				LucasL,
					Function[\[FormalY], (1 - \[FormalX] - \[FormalX]^2) \[FormalY] - (2 - \[FormalX])],
				Tribonacci,
					Function[\[FormalY], (1 - \[FormalX] - \[FormalX]^2 - \[FormalX]^3) \[FormalY] - \[FormalX]^2]
			],
			ZeroSeries[\[FormalX], 0]
		}]
	][n]
(* XXX ConstantRecursiveSequence (which can then handle Fibonacci, LucasL, JacobsthalNumber, Tribonacci, PolygonalNumber, polynomials, etc. and linear combinations) *)
AlgebraicSequenceReduce[
	AlgebraicSequence[polynomialfunction_Function, x : Except[_Rule, _?PlausibleVariableQ], options : OptionsPattern[]][n_],
	{n_?PlausibleVariableQ}
] /; ImplicitFunctionTheoremPolynomialQ[polynomialfunction[\[FormalY]], x, \[FormalY], options] :=
	AlgebraicSequence[
		SeriesRoot[{
			polynomialfunction,
			ZeroSeries[x, 1]
		}],
		options
	][n]
AlgebraicSequenceReduce[
	sequence : (AlgebraicSequence[_, OptionsPattern[]]?SeriesRootAlgebraicSequenceObjectQ)[nsequence__],
	{nsequence__?PlausibleVariableQ}
] :=
	sequence
(* TODO This doesn't use the output rules of the automaton, if present. *)
(* TODO Support edge patterns? *)
(* Multidimensional version? *)
(* With the Modulus option set, the output is a polynomial which is congruent to  0  when  y^i  is replaced with  f(x^i) .
	Probably the only useful settings for Modulus are  0  and powers of  p . *)
(* xxx are there problems if the sequence terms are symbolic involving \[FormalX] or \[FormalY]? *)
AlgebraicSequenceReduce[
	sequence : _AutomaticSequence[n_],
	{n_?PlausibleVariableQ},
	OptionsPattern[]
] :=
Module[
	{
		automaton, initialstate, inputalphabet, p, modulus, kernelrelationships, statecount, rules, lastrow, polynomial, state,
		f, i, x = \[FormalX], y = \[FormalY], z, failed
	},
	failed = Catch[
(* xxx check that  sequence  is a valid automatic sequence object? *)
		automaton = AutomaticSequenceAutomaton[sequence];
		initialstate = automaton[[2]];
		inputalphabet = AutomatonInputAlphabet[automaton];
		If[!MatchQ[inputalphabet, {__Integer}],
			Throw[True]
		];
		p = Max[inputalphabet] + 1;
		If[!PrimeQ[p],
			Message[AlgebraicSequenceReduce::prime, p, sequence]; Throw[True]
		];
		If[Sort[inputalphabet] =!= Range[0, p - 1],
			Throw[True]
		];
(* xxx i don't remember why  modulus  can be different from  p *)
		modulus = Replace[OptionValue[Modulus], Automatic -> p];
		If[!IntegerQ[modulus],
			Message[AlgebraicSequenceReduce::mod]; Throw[True]
		];
		kernelrelationships = Normal[GroupBy[
			Reverse[First[automaton]],
			#[[1, 1]] &,
			(#[[1, 2]] &) /@ SortBy[#, Last] &
		]];
		(* Check that the automaton is deterministic. *)
		If[Union[Length /@ Last /@ kernelrelationships] =!= {p},
			Throw[True]
		];
		statecount = Length[kernelrelationships];
(* xxx better name than rules? *)
		rules = (RuleDelayed @@ {f[First[#], z_], Total[MapIndexed[z^(#2[[1]] - 1) f[#1, z^p] &, Last[#]]]} &) /@ kernelrelationships;
(* TODO
Check that the output alphabet is {0, ..., p-1}?
If the output alphabet size is greater than p, then we'll need to do row reduction over F_q, and even now for F_p I'm not sure it's correct because it could divide by p at some intermediate step.
Should I RowReduce modulo  modulus ?  This would have an impact on the PolynomialMod later; may not need it.
Should I use NullSpace rather than RowReduce?
*)
		lastrow = Last[RowReduce[ArrayFlatten[{{
			Reverse[
				MapIndexed[
					Table[
						Coefficient[#1, f[state, x^p^First[#2]]],
						{state, First /@ kernelrelationships}
					] /. x -> x^p^(statecount + 1 - First[#2]) &,
					Collect[Rest[NestList[# /. rules &, f[initialstate, x], statecount + 1]], _f]
				]
			],
			-IdentityMatrix[statecount + 1]
		}}]]];
		If[!MatchQ[Take[lastrow, statecount], {0 ..}],
(* TODO Can this happen?  Does the identity matrix necessarily prevent it?
			Print["this can happen"]; *) Message[AlgebraicSequenceReduce::mat]
		];
		(* TODO Give Modulus to Cancel?  PolynomialLCM? *)
		(* Cancel any powers of p appearing in numerators and denominators; otherwise the output can end up being the zero polynomial. *)
		lastrow = Cancel[lastrow];
		lastrow = Drop[PolynomialMod[(PolynomialLCM @@ Denominator /@ lastrow) lastrow, modulus], statecount];
		polynomial = lastrow.Table[y^p^i, {i, 0, statecount}];
		If[!ImplicitFunctionTheoremPolynomialQ[polynomial, x, y, Modulus -> p],
			(* Does this occur?  Probably not the right message, since the user can't control this polynomial. *)
			Message[AlgebraicSequenceReduce::ift, Function @@ {y, polynomial}]; Throw[True]
(* but then how many terms do we need? *)
		];
		False
	];
	AlgebraicSequence[
		Function @@ {y, polynomial},
		\[FormalX],
		Modulus -> p (* what goes here - p or modulus? *)
	][n] /; !failed
]
AlgebraicSequenceReduce[
	originalsequence_[n_],
	n_?PlausibleVariableQ,
	options : OptionsPattern[]
] :=
With[{sequence = AlgebraicSequenceReduce[originalsequence[n], {n}, options]},
	sequence /; !MatchQ[sequence, _AlgebraicSequenceReduce]
]
Options[AlgebraicSequenceReduce] = {Modulus -> Automatic}
SyntaxInformation[AlgebraicSequenceReduce] = {"ArgumentsPattern" -> {_, _}}
AlgebraicSequenceReduce::ift = "Polynomial function `1` does not satisfy the conditions of implicit function theorem. Use SeriesRoot to identify a series."
AlgebraicSequenceReduce::mat = "Row reduction produced an ill\[Hyphen]formed matrix; resulting polynomial may not be correct."
AlgebraicSequenceReduce::mod = "Modulus must be an integer."
AlgebraicSequenceReduce::prime = "The `1`\[Hyphen]automatic sequence `2` must be presented as a " <> box["p"] <> "\[Hyphen]automatic sequence for prime " <> box["p"] <> "."

SetAttributes[AperyNumber, {Listable, NumericFunction}]
AperyNumber[n_?NumericQ] := HypergeometricPFQ[{-n, -n, n + 1, n + 1}, {1, 1, 1}, 1]
SyntaxInformation[AperyNumber] = {"ArgumentsPattern" -> {_}}

(* These don't check that the automaton is complete, so they can return $Failed. *)
(* TODO Remove these first two down values and rely on AutomaticSequenceNumerationSystemList more, as I'm doing for RegularSequence? *)
AutomaticSequence[automaton_?AutomatonQ, numerationsystem_?NumerationSystemQ][n_Integer] :=
With[{digitlist = DigitList[n, numerationsystem]},
	automaton[digitlist] /; !MatchQ[digitlist, _DigitList]
]
AutomaticSequence[automaton_?AutomatonQ, numerationsystemlist : {__?NumerationSystemQ}][n__Integer] /;
	Length[{n}] == Length[numerationsystemlist] :=
With[{digitlists = MapThread[DigitList, {{n}, numerationsystemlist}]},
	(* This assumes the automaton's input alphabet consists of lists, even if there is only one numeration system. *)
	automaton[Transpose[PadRight[digitlists]]] /; !MemberQ[digitlists, _DigitList]
]
AutomaticSequence[automaton_?AutomatonQ][n__Integer] :=
Module[{numerationsystemlist, automatoninput, digitlists, failed = False},
	numerationsystemlist = AutomaticSequenceNumerationSystemList[AutomaticSequence[automaton]];
	Switch[numerationsystemlist,
		{_} /; Length[{n}] == 1 && !ListQ[(* the first edge label *) automaton[[1, 1, 2]]],
			automatoninput = DigitList[n, First[numerationsystemlist]];
			If[MatchQ[automatoninput, _DigitList],
				failed = True
			],
		_List?(Length[#] == Length[{n}] &),
			digitlists = MapThread[DigitList, {{n}, numerationsystemlist}];
			If[MemberQ[digitlists, _DigitList],
				failed = True,
				automatoninput = Transpose[PadRight[digitlists]]
			],
		_,
			failed = True
	];
	automaton[automatoninput] /; !failed
]
SyntaxInformation[AutomaticSequence] = {"ArgumentsPattern" -> {_, _.}}

AutomaticSequenceAutomaton[AutomaticSequence[automaton_, ___][__]] :=
	automaton
AutomaticSequenceAutomaton[AutomaticSequence[automaton_, ___]] :=
	automaton
SyntaxInformation[AutomaticSequenceAutomaton] = {"ArgumentsPattern" -> {_}}


(*** AutomaticSequenceReduce code ***)

(* Method extracted from Theorem 12.2.5 of Allouche & Shallit, Automatic Sequences: Theory, Applications, Generalizations. *)
AlgebraicSequenceAutomaton[
	(* We don't need to check SeriesRootAlgebraicSequenceObjectQ since this is already tested in AutomaticSequenceReduce. *)
	AlgebraicSequence[
(* xxx allow general series center x0? *)
		SeriesRoot[{polynomialfunction_Function, root_SeriesData}, seriesrootoptions : OptionsPattern[]],
		Modulus -> modulus_?PrimeQ
	],
	options : OptionsPattern[]
] :=
Module[
	{
		polynomial, seriesvariables, variables, y, z,
		yannihilator, y1coefficient, yseriesdimensions, yseries, z1expressedinhigherpowers, minexponents, zexponentexponent, zseries,
		edges, statecount, state, statehashassociation, stateindex, output, automaton, newstate, newstatehash, newstateindex, starttime,
		checkstatesameness, memorystorage, directory, failed
	},
	failed = Catch[
		checkstatesameness = !TrueQ[OptionValue[HashStateNames]];
		polynomial = polynomialfunction[y];
		seriesvariables = SeriesVariables[root];
		variables = Append[seriesvariables, z];
		If[TrueQ[OptionValue[Monitor]],
			PrintTemporary["Computing Ore polynomial"]
		];
		yannihilator = Expand[OrePolynomial[polynomial, Append[seriesvariables, y], modulus, Modulus -> modulus]];
(*
Print["yannihilator:", Tab, Collect[yannihilator, y]];
*)
		If[TrueQ[OptionValue[Monitor]],
			PrintTemporary["Manipulating Ore polynomial"]
		];
		y1coefficient = Coefficient[yannihilator, y, 1];
(*
Print["y1coefficient:", Tab, y1coefficient];
*)
		(* Solve for  z^1 . *)
		z1expressedinhigherpowers = FromCoefficientRules[
			Replace[
				CoefficientRules[yannihilator, y],
				{
					({1} -> _) -> Sequence[],
					({exponent_} -> coefficient_) :> ({exponent} -> Expand[-coefficient y1coefficient^(exponent - 2), Modulus -> modulus])
				},
				{1}
			],
			z
		];
(*
Print["z1expressedinhigherpowers:", Tab, z1expressedinhigherpowers];
*)
		(* Compute enough terms of the power series to compute the constant term of each state series after substituting  z -> yseries/y1coefficient . *)
		If[TrueQ[OptionValue[Monitor]],
			PrintTemporary["Computing initial terms of the series"]
		];
		zexponentexponent = Log[modulus, Exponent[z1expressedinhigherpowers, z]];
		(* These are the minimum exponents of the coefficients in  z1expressedinhigherpowers . *)
		minexponents = Exponent[#, seriesvariables, Min] & /@
			Replace[
				List /@ (modulus^Range[zexponentexponent]),
				Append[
					CoefficientRules[z1expressedinhigherpowers, z],
					_ -> 0
				],
				{1}
			];
		(* Simulate applications of the Cartier operator to compute lower bounds on the minimum exponents of the coefficients in polynomials representing states. *)
(*
		(* specific to one variable *)
		minexponents = MapThread[
			Min,
			FixedPointList[
				Function[exponents,
					Floor[1/modulus MapThread[
						Min,
						{
							First[exponents] + (* specific to one variable *)First /@ minexponents,
							Append[Rest[exponents], Infinity]
						}
					]]
				],
				(* These are the minimum exponents of the coefficients in the initial state. *)
				PadRight[{Exponent[y1coefficient, First[seriesvariables], Min]}, zexponentexponent, Infinity]
			]
		];
		yseriesaccuracyminus1 = Plus[
			(* This is "zseriesdimensions - 1" -- the maximum exponent we need to compute  zseries  up to. *)
			Max @@ ((modulus^Range[0, zexponentexponent - 1] - 1) Exponent[y1coefficient, (* specific to one variable *)First[seriesvariables], Min] - minexponents),
			Exponent[y1coefficient, (* specific to one variable *)First[seriesvariables], Min]
		];
*)
		minexponents = Transpose[MapThread[
			Min,
			(* FixedPointList (instead of NestWhileList) would work here for most inputs, but for some the exponents alternate; for example
				AutomaticSequenceReduce[Mod[AlgebraicSequence[SeriesRoot[{Function[y, (x^3 + 1) y^3 + x^3], x + x^4 + SeriesData[x, 0, {}, 1, 6, 1]}]][n], 2], n]
			*)
			NestWhileList[
				Function[exponents,
					Floor[1/modulus MapThread[
						Min,
						{
							First[exponents] + # & /@ minexponents,
							Append[Rest[exponents], ConstantArray[Infinity, Length[seriesvariables]]]
						},
						2
					]]
				],
				(* These are the minimum exponents of the coefficients in the initial state. *)
				PadRight[{Exponent[y1coefficient, seriesvariables, Min]}, zexponentexponent, {ConstantArray[Infinity, Length[seriesvariables]]}],
				UnsameQ,
				All
			],
			2
		]];
(*
Print[minexponents];
*)
(* States are polynomials in z.  When we substitute  z -> yseries/y1coefficient  we need to be able to compute the constant term.
   The mindegree of yseries/y1coefficient could be as low as  -Exponent[y1coefficient, x, Min] .
   Want:  MinKnownExponent[a_0 z^(p^0) + a_2 z^(p^1) + ... + a_r z^(p^r), x] >= 0
          MinKnownExponent[z^(p^i), x] >= 0	for each i
          MinKnownExponent[(yseries/y1coefficient)^(p^i), x] >= 0	for each i
   To get the constant term when we raise  yseries/y1coefficient  to the power p^i, we need to know  yseries/y1coefficient
   up to and including  x^((p^i - 1) Exponent[y1coefficient, x, Min]) . *)
		yseriesdimensions = 1 + MapThread[
			Function[{y1coefficientminexponent, minexponentlist},
				Plus[
					(* This is "zseriesdimensions - 1" -- the exponent we need to compute  zseries  up to in this variable. *)
					Max @@ ((modulus^Range[0, zexponentexponent - 1] - 1) y1coefficientminexponent - minexponentlist),
					y1coefficientminexponent
				]
			],
			{
				Exponent[y1coefficient, seriesvariables, Min],
				minexponents
			}
		];
(*
Print["yseriesdimensions:", Tab, yseriesdimensions];
*)
(* testprint *)
If[First[yseriesdimensions] < 0, Print["yseriesdimensions is ", yseriesdimensions, "; need to Max with 0 apparently"]; Quit[]];
(*
(* xxx this seems like a weird condition now.
   actually it won't match _Root below either
   I should just rewrite all of this *)
(* xxx turn Return[$Failed] into Throw[True] *)
		If[MatchQ[root, _SeriesRoot],
			yseries = root[[1, 2]];
(* xxx generalize this for more than 1 variable.  The 5th part is the exponent of O[x] (for the outer variable). *)
			If[SeriesAccuracy[yseries] + 1 (* xxx right? *) < yseriesaccuracyminus1 + 1,
				Message[ChristolAutomaton::prec, yseries, yseriesaccuracyminus1 + 1]; Return[$Failed]
			]
			,
			If[Length[seriesvariables] == 1,
				Switch[root,
					_Root,
						yseries = Algebraics`Private`RootSeries[root, {First[seriesvariables], 0, yseriesaccuracyminus1 + 1}];
						If[yseries === $Failed,
							Message[ChristolAutomaton::noroot, polynomialfunction]; Return[$Failed]
						],
					None,
						(* TODO Ideally we might pass a Modulus option to SeriesSolve here.  XXX Now SeriesSolve supports it. *)
						yseries = SeriesSolve[polynomial == 0 /. y -> y @@ seriesvariables, y @@ seriesvariables, {First[seriesvariables], 0, yseriesaccuracyminus1 + 1}];
						(* Since we haven't computed many terms of the series, it may be possible that the following test passes even though there isn't a unique root. *)
(* xxx should really make this a rigorous test *)
						If[Length[yseries] != 1,
							Message[ChristolAutomaton::noroot1, polynomialfunction]; Return[$Failed]
						];
						yseries = y @@ seriesvariables /. First[yseries]
				],
(* XXX TODO real message *)
				Print["for a series in more than 1 variable, supply an approximation as SeriesRoot"]
			]
		];
*)
		If[Length[seriesvariables] == 1,
			(* TODO SeriesRootSeriesList only supports functions of one variable. *)
			yseries = SeriesRootSeriesList[
				{{y, polynomial}, {Normal[root], SeriesAccuracy[root] - 1}},
				{First[seriesvariables], 0, First[yseriesdimensions] - 1},
				MaxDenominator -> 1,
				Modulus -> modulus
			];
			If[Length[DeleteDuplicates[yseries]] != 1,
				Message[AutomaticSequenceReduce::soln, polynomialfunction, root]; Throw[True]
			];
			(* Even if  Length[DeleteDuplicates[yseries]] == 1  this doesn't mean that if we used higher accuracy it wouldn't split into multiple solutions.
			   But the automaton only depends on the terms we've computed, so it's fine. *)
			yseries = First[yseries];
			,
			If[And @@ Thread[SeriesDimensions[root] >= yseriesdimensions],
				yseries = root,
				Message[AutomaticSequenceReduce::srsdim, root, SeriesDimensions[root]]; Throw[True]
			]
		];
(*
Print["yseries:", Tab, yseries];
*)
		If[Or @@ Divisible[Denominator[Flatten[CoefficientList[yseries, seriesvariables]]], modulus],
			Message[AutomaticSequenceReduce::coeff, yseries, modulus]; Throw[True]
		];
(* xxx this will probably cause problems if the constant term of  y1coefficient  is divisible by  modulus ; are we checking for that? *)
		zseries = SeriesMod[yseries/y1coefficient, modulus];
(*
Print["zseries = yseries/y1coefficient:", Tab, zseries];
*)
		memorystorage = Replace[OptionValue[StateStorage],
			{
				"Disk" | {"Disk", ___, "Directory" -> Automatic, ___} :> (
					directory = $TemporaryDirectory;
					False
				),
			 	{"Disk", ___, "Directory" -> dir_, ___} :> (
					directory = dir;
					False
				),
				"Memory" ->
					True,
				_ ->
					False
			}
		];
		statecount = 1;
		(* Substitute  z = y/y1coefficient . *)
		newstate = Expand[y1coefficient z];
		If[memorystorage,
			state[statecount] = newstate,
			Export[FileNameJoin[{directory, ToString[statecount] <> ".m"}], newstate]
		];
		statehashassociation = Association[];
		statehashassociation[Hash[newstate]] = statecount;
		output = Association[];
		output[statecount] = Expand[Normal[newstate /. z -> zseries], Modulus -> modulus] /. Alternatives @@ seriesvariables -> 0;
		stateindex = 1;
		starttime = DateObject[];
		If[TrueQ[OptionValue[Monitor]] && 10 < $VersionNumber < 11,
			Message[Monitor::abort]
		];
		edges = Join @@ Reap[
			If[TrueQ[OptionValue[Monitor]] && !(10 < $VersionNumber < 11), Monitor, List][
				While[stateindex <= statecount,
					Sow[
						MapIndexed[
							Function[{monomialrules, index},
								(* Reap isn't consistent. *)
								newstate = If[monomialrules == {},
									0,
									FromCoefficientRules[First[monomialrules], variables]
								];
								newstatehash = Hash[newstate];
								newstateindex = statehashassociation[newstatehash];
								If[
									And[
										checkstatesameness,
										!MissingQ[newstateindex],
										If[memorystorage,
											state[newstateindex],
											Import[FileNameJoin[{directory, ToString[newstateindex] <> ".m"}]]
										] =!= newstate
									]
									,
									Message[AutomaticSequenceReduce::hash, newstatehash];
									newstateindex = Missing["NotFound"]
								];
								{
									stateindex -> If[MissingQ[newstateindex],
										statecount++;
										If[memorystorage,
											state[statecount] = newstate,
											Export[FileNameJoin[{directory, ToString[statecount] <> ".m"}], newstate]
										];
										statehashassociation[newstatehash] = statecount;
										(* TODO Is replacing  Alternatives @@ seriesvariables -> 0  faster than using Normal followed by ConstantTerm? *)
										(* The modulus is important here because in many cases it turns a Laurent series, for example with a term p/x, into a power series modulo p. *)
										(* TODO Do I need RationalMod if I've already applied SeriesMod?  Not for p==2 but what if p==3 and y1coefficient==2+stuff ? *)
(*
										state[i] = (*RationalMod[*)SeriesMod[state[i] /. z -> zseries, p] /. Alternatives @@ seriesvariables -> 0(*, p]*),
*)
(* testprint *)
If[
	And[
		MatchQ[newstate /. z -> zseries, _SeriesData],
		(newstate /. z -> zseries)[[5]] <= 0
	],
	Print[Style["not enough terms", Red], Tab, newstate /. z -> zseries]
];
										output[statecount] = Expand[Normal[newstate /. z -> zseries], Modulus -> modulus] /. Alternatives @@ seriesvariables -> 0;
										statecount
										,
										newstateindex
									],
									DigitList[index[[1]] - 1, modulus, Length[seriesvariables]]
								}
							],
							Last[Reap[
								(With[{exponentquotientremainders = QuotientRemainder[#[[1]], modulus]},
									Sow[First /@ exponentquotientremainders -> #[[2]], {Last /@ Most[exponentquotientremainders]}];
								] &) /@
									CoefficientRules[
										(* Replace z^1 with z1expressedinhigherpowers. *)
										state[stateindex] + Coefficient[state[stateindex], z, 1] (z1expressedinhigherpowers - z),
										variables,
										Modulus -> modulus
									];,
								Tuples[Range[0, modulus - 1], Length[seriesvariables]]
							]]
						]
					];
					If[!checkstatesameness,
						If[memorystorage,
							Unset[state[stateindex]],
							DeleteFile[FileNameJoin[{directory, ToString[stateindex] <> ".m"}]]
						]
					];
					stateindex++
				],
				Column[{
					Row[{"Processing state ", stateindex, " of ", statecount}],
					ProgressIndicator[(stateindex - 1)/statecount],
					If[stateindex == 1,
						Row[{}],
						Row[{"Processing known states will finish at ", DatePlus[starttime, statecount/(stateindex - 1) DateDifference[starttime, DateObject[]]]}]
					]
				}]
			];
			If[checkstatesameness,
				If[memorystorage,
					(* Unsetting the states one at a time seems to be better than  Clear[state]  for avoiding a time-consuming memory spike when states have been swapped to disk. *)
					Unset[state[#]] & /@ Range[statecount, 1, -1],
					DeleteFile[FileNameJoin[{directory, ToString[#] <> ".m"}] & /@ Range[statecount]]
				]
			];
		][[2, 1]];
		If[TrueQ[OptionValue[FlattenInputAlphabet]] && Length[seriesvariables] == 1,
			edges = MapAt[First, 2] /@ edges
		];
		automaton = Automaton[edges, 1, Normal[output]];
		If[TrueQ[OptionValue[Minimize]],
			If[TrueQ[OptionValue[Monitor]],
				PrintTemporary["Minimizing"]
			];
			automaton = AutomatonMinimize[automaton]
		];
		False
	];
	automaton /; !failed
]
Options[AlgebraicSequenceAutomaton] = {
	FlattenInputAlphabet -> True,
	HashStateNames -> False,
	Minimize -> True,
	Monitor -> False,
	StateStorage -> "Memory"
}

ConstantTermSequenceAutomaton[
	ConstantTermSequence[originalpowerpolynomial_, originalfactorpolynomial_, variables_List],
	modulus_?PrimePowerQ,
	options : OptionsPattern[]
] /;
	And[
		UnsameQ @@ variables,
		SubsetQ[variables, Variables[{originalpowerpolynomial, originalfactorpolynomial}]],
		LaurentPolynomialQ[originalpowerpolynomial, variables],
		LaurentPolynomialQ[originalfactorpolynomial, variables],
(*
(* XXX Wouldn't it be faster in some cases to plug in 0, if the expression is factored? *)
		GCD[ConstantTerm[Expand[Denominator[rationalexpression], Modulus -> modulus], Join @@ variablepartition], modulus] == 1,
*)
		Or[
			MatchQ[OptionValue[ConstantTermSequenceAutomaton, {options}, StateStorage], "Disk" | {"Disk", "Directory" -> Automatic | _?DirectoryQ} | "Memory"],
(* TODO Issue a different message if the directory doesn't pass  DirectoryQ ? *)
			Message[AutomaticSequenceReduce::bdstg, OptionValue[ConstantTermSequenceAutomaton, {options}, StateStorage]]; False
		]
	] :=
Module[
	{
		p, alpha, stabilizedpowerpolynomial, stabilizedpowerpolynomialpowersmatrix, newstatesfunction,
		minexponents, maxexponents, dimensions, annihilatordata, slot,
		currentstate, powerpolynomial, factorpolynomial, newpowerpolynomial, newstates, newstateminexponents, newstatemaxexponents,
		edges, statecount, state, statehashassociation, stateindex, output, automaton, newstatehash, newstateindex, starttime,
		checkstatesameness, usepolynomialsonly, compressstatenames, memorystorage, directory
	},
	{p, alpha} = NumberTheory`PrimePower[modulus];
	checkstatesameness = !TrueQ[OptionValue[HashStateNames]];
(* xxx setting this to True seems to give a speed improvement.  (it prevents newstatesfunction from being defined) *)
usepolynomialsonly = True;
	If[Length[variables] == 1,
		compressstatenames = MatchQ[OptionValue[CompressStateNames], True | Automatic]
		,
		(* LaurentPolynomialPowerAnnihilators is only implemented for univariate polynomials. *)
		compressstatenames = False;
		If[TrueQ[OptionValue[CompressStateNames]],
			Message[AutomaticSequenceReduce::cmprss, "multivariate polynomials"]
		]
	];
	If[TrueQ[OptionValue[Monitor]],
		PrintTemporary["Computing the stabilized polynomial"]
	];
(*
i=0;
Monitor[
*)
	stabilizedpowerpolynomial = FixedPoint[
		(
(*
i++;
*)
			newpowerpolynomial = Expand[#^p, Modulus -> modulus];
			If[And @@ Divisible[Join @@ First /@ LaurentPolynomialCoefficientRules[newpowerpolynomial, variables], p],
				Cartier0WithoutSelect[newpowerpolynomial, variables, p],
				newpowerpolynomial
			]
		) &,
		originalpowerpolynomial,
		alpha - 1
	];
(*
, i];
*)
(*
Print[stabilizedpowerpolynomial];
*)
	{minexponents, maxexponents} = Transpose[Exponent[stabilizedpowerpolynomial, variables, MinMax[{##}] &]];
(*
Print[{minexponents, maxexponents}];
*)
	dimensions = maxexponents - minexponents + 1;
	If[TrueQ[OptionValue[Monitor]],
		PrintTemporary["Binning monomials of powers of the stabilized polynomial"]
	];
	stabilizedpowerpolynomialpowersmatrix =
		Function[poly,
			(* Bin monomials by their (negative) exponents modulo p. *)
			Replace[
				Last[Reap[
					Function[monomial,
						Sow[monomial, {Mod[-Exponent[monomial, variables], p]}];
					] /@ FastMonomialList[poly],
					Tuples[Range[0, p - 1], Length[variables]]
				]],
				{{} -> 0, {monomiallist_} :> Total[monomiallist]},
				{1}
			]
		] /@ NestList[Expand[# stabilizedpowerpolynomial, Modulus -> modulus] &, 1, p - 1];
(*
Print[Dimensions[stabilizedpowerpolynomialpowersmatrix]];
*)
(*
Print[dimensions];
Print[variables];
Print[minexponents];
*)
(* This If might actually be important to keep.  Or maybe replace it with  If[!annihilatorcheck ...  Wait, it's already in that, right?  well we don't have annihilatorcheck anymore *)
If[!usepolynomialsonly,
(* xxx can I do both the binning and multiplying with a single matrix multiplication?  Yeah I should be able to.
   How do I construct it?  Perform the binning and multiplying symbolically and then look at coefficients?
   But then do we even need a matrix multiplication?  I could just construct a replacement rule.
   Or a function: *)
	(* Bin monomials in a symbolic Laurent polynomial by their exponents modulo p, and multiply by each power of  stabilizedpowerpolynomial ,
	   keeping only monomials with exponents that are congruent to 0.
	   This allows us to create a function that we can apply directly to a state (represented as a list of coefficients)
	   to compute its images under the Cartier operators. *)
	newstatesfunction = Function[newstate,
		Flatten[Normal[SparseArray[
			MapAt[# - minexponents + 1 &, 1] /@ GeneralCoefficientRules[
(* xxx we need to Expand here (because FastMonomialList expects it), but does the Modulus really do anything?  I think not. *)
				SymbolicCartier0WithoutSelect[Expand[newstate(*, Modulus -> modulus*)], variables, p],
				variables
			],
			dimensions
		]]]
	] /@
		Dot[
			stabilizedpowerpolynomialpowersmatrix,
			Replace[
				Last[Reap[
					Function[monomial,
						Sow[monomial, {Mod[Exponent[monomial, variables], p]}];
					] /@
(* xxx FastMonomialList kinda undoes the FromCoefficientListWithOffsets; better way?
   maybe construct coefficient rules directly; then I won't need Exponent *)
						FastMonomialList[FromCoefficientListWithOffsets[
							ArrayReshape[
								slot /@ Range[Times @@ dimensions],
								dimensions
							],
							variables,
							minexponents
						]],
					Tuples[Range[0, p - 1], Length[variables]]
				]],
				{{} -> 0, {monomiallist_} :> Total[monomiallist]},
				{1}
			]
		];
	newstatesfunction = If[OptionValue[Compile],
		Compile @@ {
			{slot[#], _Integer} & /@ Range[Times @@ dimensions],
			Mod[newstatesfunction, modulus]
		},
		Function @@ {Mod[newstatesfunction /. slot -> Slot, modulus]}
	]
];
	If[compressstatenames,
(*
Print[Style["COMPUTING annihilatordata", Red]];
*)
		annihilatordata = LaurentPolynomialPowerAnnihilators[stabilizedpowerpolynomial, First[variables], Modulus -> modulus];
		annihilatordata =
			Function[nullvector,
				With[{position = FirstPositionLevel1[nullvector, Except[0]]},
					{

						(* coefficient *)
						nullvector[[position]],

						(* vector data... *)
						(* position of the coefficient in the coefficient list *)
						position,
						nullvector,

						(* polynomial data... *)
						(* exponent list for the coefficient's monomial *)
						If[$VersionNumber >= 11.3,
							IntegerDigits[position - 1, MixedRadix[dimensions], Length[variables]] + minexponents,
							Reverse[DigitList[position - 1, Reverse[dimensions], Length[variables]]] + minexponents
						],
						FromCoefficientListWithOffsets[ArrayReshape[nullvector, dimensions], variables, minexponents]

					}
				]
			] /@ annihilatordata
(* (xxx would also need to put a List around the first entry)
;		polynomialannihilatordata = MapAt[FromCoefficientListWithOffsets[ArrayReshape[#, dimensions], variables, minexponents] &, 3] /@ annihilatordata
*)
(*
; Print[Grid[#[[3]] & /@ annihilatordata /. 0 -> ""]]
; Print[Multicolumn[annihilatordata, p]]
; Print[Length[annihilatordata], " annihilators"]
*)
	];
(*
If[usepolynomialsonly, Print["here"]];
*)
	statecount = 1;
	state[statecount] = "pair" @@ Expand[{originalpowerpolynomial, originalfactorpolynomial}, Modulus -> modulus];
(*
Print[statecount, Tab, state[statecount]];
*)
	output = Association[];
	If[First[state[statecount]] === stabilizedpowerpolynomial,
		(* Represent the initial state by a single Laurent polynomial. *)
(*
Print[Tab, Style["CONVERTING TO LAURENT POLYNOMIAL", Purple]];
*)
		state[statecount] = Last[state[statecount]];
(*
Print[statecount, Tab, state[statecount]];
*)
		If[compressstatenames,
(*
Print[statecount, Tab, "minimizing representation"];
Print[laurentPolynomialMod[state[statecount], variables, annihilatordata, modulus]];
*)
			state[statecount] = LaurentPolynomialMod[state[statecount], variables, annihilatordata, modulus]
(*
; Print[statecount, Tab, state[statecount]]
*)
		];
		output[statecount] = ConstantTerm[state[statecount], variables];
If[!usepolynomialsonly,
		{newstateminexponents, newstatemaxexponents} = Transpose[Exponent[state[statecount], variables, MinMax[{##}] &]];
		If[And @@ Thread[minexponents <= newstateminexponents] && And @@ Thread[newstatemaxexponents <= maxexponents],
			(* Represent the initial state by a (flattened) coefficient list instead of a Laurent polynomial. *)
			state[statecount] = Flatten[Normal[SparseArray[
				MapAt[# - minexponents + 1 &, 1] /@ LaurentPolynomialCoefficientRules[
					state[statecount],
					variables
				],
				dimensions
			]]]
		]
]
		,
		output[statecount] = ConstantTerm[Last[state[statecount]], variables]
	];
(* TODO check that we actually get a speed benefit by testing inequality of hash values; is it only beneficial once we've started paging to disk? *)
	statehashassociation = Association[];
	statehashassociation[Hash[state[statecount]]] = statecount;
	memorystorage = Replace[OptionValue[StateStorage],
		{
			"Disk" | {"Disk", ___, "Directory" -> Automatic, ___} :> (
				directory = $TemporaryDirectory;
				False
			),
		 	{"Disk", ___, "Directory" -> dir_, ___} :> (
				directory = dir;
				False
			),
			"Memory" ->
				True,
			_ ->
				False
		}
	];
	If[!memorystorage,
		Export[FileNameJoin[{directory, ToString[statecount] <> ".m"}], state[statecount]];
		Unset[state[statecount]]
	];
	stateindex = 1;
	starttime = DateObject[];
	If[TrueQ[OptionValue[Monitor]] && 10 < $VersionNumber < 11,
		Message[Monitor::abort]
	];
	edges = Join @@ Reap[
		If[TrueQ[OptionValue[Monitor]] && !(10 < $VersionNumber < 11), Monitor, List][
			While[stateindex <= statecount,
				currentstate = If[memorystorage,
					state[stateindex],
					Import[FileNameJoin[{directory, ToString[stateindex] <> ".m"}]]
				];
				Sow[
					MapIndexed[
						Function[{newstate, index},
							newstatehash = Hash[newstate];
							newstateindex = statehashassociation[newstatehash];
							If[
								And[
									checkstatesameness,
									!MissingQ[newstateindex],
									If[memorystorage,
										state[newstateindex],
										Import[FileNameJoin[{directory, ToString[newstateindex] <> ".m"}]]
									] =!= newstate
								]
								,
								Message[AutomaticSequenceReduce::hash, newstatehash];
								newstateindex = Missing["NotFound"]
							];
							{
								stateindex -> If[MissingQ[newstateindex],
									statecount++;
									If[memorystorage,
(*
Print[statecount, Tab, newstate];
*)
										state[statecount] = newstate,
										Export[FileNameJoin[{directory, ToString[statecount] <> ".m"}], newstate]
									];
									statehashassociation[newstatehash] = statecount;
									output[statecount] = Switch[newstate,
										_List, Extract[newstate, -minexponents + 1],
(* xxx does this assume something about  First[newstate] ?  like that its constant term is 1? *)
										"pair"[_, _], ConstantTerm[Last[newstate], variables],
										_, ConstantTerm[newstate, variables]
									];
									statecount
									,
									newstateindex
								],
								index[[1]] - 1
							}
						],
						Switch[currentstate,

							_List,
							(* The current state is represented by a (flattened) coefficient list. *)
(*
Print[Tab, Style["COEFFICIENT LIST", Purple]];
Print[currentstate];
Print["hello hello hello"];
Pause[1];
Quit[];
*)
							newstates = newstatesfunction @@ currentstate;
							If[compressstatenames,
(* XXX TODO Is it faster to apply Mod after VectorReduceMod rather than inside the Fold? *)
								newstates = (*EchoFunction["list", Function[asdf, # -> asdf]]@*)VectorReduceMod[#, annihilatordata, modulus] & /@ newstates
							];
							newstates
							,

							"pair"[_, _],
(*
Print[Tab, Style["PAIR", Purple]];
*)
(*
Print[stateindex, Tab, "list"];
*)
							(* The current state is represented by a pair of Laurent polynomials; the power polynomial hasn't stabilized yet. *)
							{powerpolynomial, factorpolynomial} = List @@ currentstate;
							newpowerpolynomial = Expand[powerpolynomial^p, Modulus -> modulus];
							newstates = Expand[powerpolynomial^Range[0, p - 1] factorpolynomial, Modulus -> modulus];
							If[And @@ Divisible[Join @@ First /@ LaurentPolynomialCoefficientRules[newpowerpolynomial, variables], p],
(* xxx for Motkin numbers, this seems to occur precisely for primes (and never prime powers), and only occurs once.  Why is that?  Can we use it? *)
								newpowerpolynomial = Cartier0WithoutSelect[newpowerpolynomial, variables, p];
								newstates = Cartier0[#, variables, p] & /@ newstates
							];
							If[newpowerpolynomial === stabilizedpowerpolynomial,
								(* The power polynomial has now stabilized for the new state, so we can use the annihilators. *)
								If[compressstatenames,
									newstates = (*EchoFunction["pair", Function[asdf, # -> asdf]]@*)LaurentPolynomialMod[#, variables, annihilatordata, modulus] & /@ newstates
								];
If[!usepolynomialsonly,
								newstates = Function[newstate,
									{newstateminexponents, newstatemaxexponents} = Transpose[Exponent[newstate, variables, MinMax[{##}] &]];
									If[And @@ Thread[minexponents <= newstateminexponents] && And @@ Thread[newstatemaxexponents <= maxexponents],
										(* Represent the new state by a (flattened) coefficient list instead of a Laurent polynomial. *)
										Flatten[Normal[SparseArray[
											MapAt[# - minexponents + 1 &, 1] /@ LaurentPolynomialCoefficientRules[
												newstate,
												variables
											],
											dimensions
										]]],
										newstate
									]
								] /@ newstates
]
								,
								newstates = "pair"[newpowerpolynomial, #] & /@ newstates
							];
							newstates
							,

							_,
							(* The current state is represented by a Laurent polynomial. *)
(* This can happen, right?  The power polynomial can stabilize without the factor polynomial being small enough yet?
   Yes, it happens for Motzkin numbers modulo 8. *)
(*
Print[Tab, Style["LAURENT POLYNOMIAL", Purple], Tab, stateindex, Tab, currentstate];
*)
(* testprint *)
If[!FreeQ[currentstate, Quotient], Print[Quotient, Tab, currentstate]; Pause[1]; Quit[]];
(*
Print[stateindex, Tab, "polynomial"];
*)
							(* Bin monomials by their exponents modulo p. *)
(*
tempstate = currentstate;
*)
							currentstate = Replace[
								Last[Reap[
									Function[monomial,
										Sow[monomial, {Mod[Exponent[monomial, variables], p]}];
									] /@ FastMonomialList[currentstate],
									Tuples[Range[0, p - 1], Length[variables]]
								]],
								{{} -> 0, {monomiallist_} :> Total[monomiallist]},
								{1}
							];
(*
If[usepolynomialsonly, Print["newstate", Tab, newstate]];
*)
							(* Multiply the current state by each power of  stabilizedpowerpolynomial ,
							   keeping only monomials with exponents that are congruent to 0. *)
							newstates = If[compressstatenames,
(*
Print[laurentPolynomialMod[cartier0WithoutSelect[#, variables, p], variables, polynomialannihilatordata, modulus]];
*)
								LaurentPolynomialMod[(*EchoFunction["polynomial", Function[asdf, asdf -> LaurentPolynomialMod[asdf, variables, annihilatordata, modulus]]]@*)Cartier0WithoutSelect[#, variables, p], variables, annihilatordata, modulus] & /@
									Expand[stabilizedpowerpolynomialpowersmatrix.currentstate, Modulus -> modulus],
								Cartier0WithoutSelect[#, variables, p] & /@
									Expand[stabilizedpowerpolynomialpowersmatrix.currentstate, Modulus -> modulus]
							];
(*
{newstateminexponents, newstatemaxexponents} = Transpose[Exponent[tempstate, variables, MinMax[{##}] &]];
If[
	And[
		And @@ Thread[minexponents <= newstateminexponents],
		And @@ Thread[newstatemaxexponents <= maxexponents],
		UnsameQ[
			Function[newstate,
				Flatten[Normal[SparseArray[
					MapAt[# - minexponents + 1 &, 1] /@ LaurentPolynomialCoefficientRules[newstate, variables],
					dimensions
				]]]
			] /@ newstates,
			(If[compressstatenames, VectorReduceMod[#, annihilatordata, modulus], #] &) /@
				newstatesfunction @@ Flatten[Normal[SparseArray[
					MapAt[# - minexponents + 1 &, 1] /@ LaurentPolynomialCoefficientRules[tempstate, variables],
					dimensions
				]]]
		]
	],
	Print["current state:", Tab, tempstate];
	Print[currentstate];
	Print[currentstate[[10]]];
	Print[newstates];
	Print[newstates[[10]]];
(*
	Print[
		Function[newstate,
			Flatten[Normal[SparseArray[
				MapAt[# - minexponents + 1 &, 1] /@ LaurentPolynomialCoefficientRules[newstate, variables],
				dimensions
			]]]
		] /@ newstates
	];
	Print[
		newstatesfunction @@ Flatten[Normal[SparseArray[
			MapAt[# - minexponents + 1 &, 1] /@ LaurentPolynomialCoefficientRules[tempstate, variables],
			dimensions
		]]]
	];
*)
	Print[
		"should be:", Tab,
		Flatten[Normal[SparseArray[
			MapAt[# - minexponents + 1 &, 1] /@ LaurentPolynomialCoefficientRules[newstates[[10]], variables],
			dimensions
		]]]
	];
	Print[
		"actual:", Tab,
		(
			newstatesfunction @@ Flatten[Normal[SparseArray[
				MapAt[# - minexponents + 1 &, 1] /@ LaurentPolynomialCoefficientRules[tempstate, variables],
				dimensions
			]]]
		)[[10]]
	];
	Pause[1];
	Quit[]
];
*)
If[!usepolynomialsonly,
							newstates = Function[newstate,
								{newstateminexponents, newstatemaxexponents} = Transpose[Exponent[newstate, variables, MinMax[{##}] &]];
								If[And @@ Thread[minexponents <= newstateminexponents] && And @@ Thread[newstatemaxexponents <= maxexponents],
									(* Represent the new state by a (flattened) coefficient list instead of a Laurent polynomial. *)
									Flatten[Normal[SparseArray[
										MapAt[# - minexponents + 1 &, 1] /@ LaurentPolynomialCoefficientRules[
											newstate,
											variables
										],
										dimensions
									]]],
									newstate
								]
							] /@ newstates;
];
							newstates

						]
					]
				];
				If[!checkstatesameness,
					If[memorystorage,
						Unset[state[stateindex]],
						DeleteFile[FileNameJoin[{directory, ToString[stateindex] <> ".m"}]]
					]
				];
				stateindex++
			],
			Column[{
				Row[{"Processing state ", stateindex, " of ", statecount}],
				ProgressIndicator[(stateindex - 1)/statecount],
				If[stateindex == 1,
					Row[{}],
					Row[{"Processing known states will finish at ", DatePlus[starttime, statecount/(stateindex - 1) DateDifference[starttime, DateObject[]]]}]
				]
(*
, Union[Values[output]]
*)
			}]
		];
(*
If[compressstatenames,
(*
(* min and max degree of states whose power polynomial is the eventual stabilized polynomial *)
Print[MapAcross[{Min, Max}, Transpose[Table[If[!ListQ[state[n]], Exponent[state[n], First[variables], MinMax[{##}] &], Nothing], {n, statecount}]]]];
Print[Table[If[!ListQ[state[n]], Exponent[state[n], variables, MinMax[{##}] &], List], {n, statecount}]];
Print[Multicolumn[Table[state[n], {n, statecount}], 2 p]];
Print[Table[state[n], {n, statecount}]];
*)
Print[Multicolumn[annihilatordata, p]];
Print[Length[annihilatordata], " annihilators"];
(* annihilators that we could also mod out by: *)
Print[Union @@ (Expand[Subtract @@@ Subsets[#, {2}], Modulus -> modulus] &) /@
  DeleteCases[
   GatherBy[
    DeleteCases[Table[state[n], {n, statecount}], _List],
    Table[ConstantTerm[
       Expand[# stabilizedpowerpolynomial^n,
        Modulus -> modulus], variables], {n, 0, 20}] &], {_}]
];
Null
];
*)
(*
Print[Table[state[n], {n, statecount}]];
*)
		If[checkstatesameness,
			If[memorystorage,
				(* Unsetting the states one at a time seems to be better than  Clear[state]  for avoiding a time-consuming memory spike when states have been swapped to disk. *)
				Unset[state[#]] & /@ Range[statecount, 1, -1],
				DeleteFile[FileNameJoin[{directory, ToString[#] <> ".m"}] & /@ Range[statecount]]
			]
		];
	][[2, 1]];
	automaton = Automaton[edges, 1, Normal[output]];
	If[TrueQ[OptionValue[Minimize]],
		If[TrueQ[OptionValue[Monitor]],
			PrintTemporary["Minimizing"]
		];
		automaton = AutomatonMinimize[automaton]
	];
	automaton
]
Options[ConstantTermSequenceAutomaton] = {
	Compile -> True,
	CompressStateNames -> Automatic,
	HashStateNames -> False,
	Minimize -> True,
	Monitor -> False,
	StateStorage -> "Memory"
}

(* not in use; doesn't go here *)
ConstantTermSequenceTermMod[powerpolynomial_, factorpolynomial_, n_, modulus_?PrimePowerQ, variables_List] /;
	And[
		UnsameQ @@ variables,
		SubsetQ[variables, Variables[{powerpolynomial, factorpolynomial}]],
		LaurentPolynomialQ[factorpolynomial, variables],
		LaurentPolynomialQ[factorpolynomial, variables]
	] :=
Module[
	{p, ndigits, newpowerpolynomial, newstate, penultimatestate},
	p = First[NumberTheory`PrimePower[modulus]];
	ndigits = DigitList[n, p];
	penultimatestate = Fold[
		Function[
			{currentstate, digit}
			,
Print[digit];
Print[Tab, "newpowerpolynomial"];
(* xxx in some cases we could save work by not recomputing this if the polynomial has stabilized, but this won't happen generically until alpha steps or whatever *)
			newpowerpolynomial = Expand[currentstate[[1]]^p, Modulus -> modulus];
Print[Tab, Hash[newpowerpolynomial]];
Print[Tab, "newstate"];
			newstate = Expand[currentstate[[1]]^digit currentstate[[2]], Modulus -> modulus];
Print[Tab, "LaurentPolynomialCoefficientRules"];
			If[And @@ Divisible[Join @@ First /@ LaurentPolynomialCoefficientRules[newpowerpolynomial, variables], p],
(* xxx for Motkin numbers, this seems to occur precisely for primes (and never prime powers), and only occurs once.  Why is that?  Can we use it? *)
Print[Tab, "Cartier0WithoutSelect"];
				newpowerpolynomial = Cartier0WithoutSelect[newpowerpolynomial, variables, p];
Print[Tab, "Cartier0"];
				newstate = Cartier0[newstate, variables, p]
			];
			{newpowerpolynomial, newstate}
		],
		Expand[{powerpolynomial, factorpolynomial}, Modulus -> modulus],
(* xxx if  n==0  this is going to complain *)
		Most[ndigits]
	];
Print[Last[ndigits]];
(* xxx does this assume something about  First[finalstate] ?  like that its constant term is 1? *)
	ConstantTerm[
		Expand[penultimatestate[[1]]^Last[ndigits] penultimatestate[[2]], Modulus -> modulus],
		variables
	]
]

DiagonalSequenceAutomaton[
	DiagonalSequence[rationalexpression_, variablepartition : {__List}, sequenceoptions : OptionsPattern[]],
	modulus_?PrimePowerQ,
	options : OptionsPattern[]
] /;
	And[
		!MemberQ[variablepartition, {}],
		UnsameQ @@ Join @@ variablepartition,
		SubsetQ[Join @@ variablepartition, Variables[rationalexpression]],
		PolynomialQ[Numerator[rationalexpression], Join @@ variablepartition],
		PolynomialQ[Denominator[rationalexpression], Join @@ variablepartition],
		Or[
(* XXX Wouldn't it be faster in some cases to plug in 0, if the expression is factored? *)
			GCD[ConstantTerm[Expand[Denominator[rationalexpression], Modulus -> modulus], Join @@ variablepartition], modulus] == 1,
			Message[AutomaticSequenceReduce::denom, rationalexpression, modulus]; False
		],
		Or[
			MemberQ[{Automatic, "High", "Low"}, OptionValue[DiagonalSequenceAutomaton, {options}, "Degree"]],
			Message[AutomaticSequenceReduce::bddeg, OptionValue[DiagonalSequenceAutomaton, {options}, "Degree"]]; False
		],
(* for backward compatibility *)
		Or[
			MemberQ[{"HighDegree", "LowDegree"}, OptionValue[DiagonalSequenceAutomaton, {options}, Method]],
			Message[DiagonalSequenceAutomaton::bdmtd, OptionValue[DiagonalSequenceAutomaton, {options}, Method]]; False
		],
		Or[
			MatchQ[OptionValue[DiagonalSequenceAutomaton, {options}, StateStorage], "Disk" | {"Disk", "Directory" -> Automatic | _?DirectoryQ} | "Memory"],
(* TODO Issue a different message if the directory doesn't pass  DirectoryQ ? *)
			Message[AutomaticSequenceReduce::bdstg, OptionValue[DiagonalSequenceAutomaton, {options}, StateStorage]]; False
		],
		Or[
			MemberQ[{0, modulus}, OptionValue[DiagonalSequence, {sequenceoptions}, Modulus]],
(* TODO message if we receive conflicting moduli?  Also, if they are compatible, it should work. *)
			False
		]
	] :=
Module[
	{
		p, variables, variablepattern, variablerepresentatives,
		denominator, denominatorconstantinverse, denominatorfactorlist, denominatorconstantfactor, denominatorexponent, position, denominatorconstantfactorroot, factor,
		edges, statecount, state, statehashassociation, stateindex, output, automaton, newstate, newstatehash, newstateindex, starttime,
		degree, checkstatesameness, memorystorage, directory
	},
	p = First[NumberTheory`PrimePower[modulus]];
	variables = Join @@ variablepartition;
	variablepattern = Alternatives @@ variables;
	variablerepresentatives = Reverse[First /@ variablepartition];
	degree = Replace[
		OptionValue["Degree"],
		Automatic -> Replace[OptionValue[Method], {"HighDegree" -> "High", "LowDegree" -> "Low"}]
	];
	checkstatesameness = !TrueQ[OptionValue[HashStateNames]];
	denominator = Denominator[rationalexpression];
	(* Make the constant term 1, but don't expand because  Expand[denominator^exponent, Modulus -> modulus]
	   is faster when  denominator  is factored. *)
	denominatorconstantinverse = PowerMod[denominator /. variablepattern -> 0, -1, modulus];
	denominator = denominatorconstantinverse denominator;
	(* If the denominator is a polynomial raised to a power, we may not need to raise it all the way to  modulus/p - 1 . *)
	denominatorfactorlist = FastFactorList[denominator];
	denominatorconstantfactor = FirstCase[
		denominatorfactorlist,
(* XXX What if the constant factor is a Rational? *)
		{constant_Integer, 1} :> constant,
		1
	];
	denominatorfactorlist = DeleteCases[denominatorfactorlist, {denominatorconstantfactor, 1}];
	denominatorexponent = Min[
		If[degree === "High", modulus, modulus/p],
		p^Min[IntegerExponent[Last /@ denominatorfactorlist, p]]
	];
	(* Absorb the constant term into one of the other factors. *)
	If[Mod[denominatorconstantfactor, modulus] != 1,
		Quiet[
			position = FirstPositionLevel1[
				denominatorfactorlist,
				{_, exponent_} /; IntegerQ[denominatorconstantfactorroot = PowerMod[denominatorconstantfactor, 1/exponent, modulus]],
				None
			],
			PowerMod::root
		];
		If[position =!= None,
			denominatorfactorlist = MapAt[
				denominatorconstantfactorroot # &,
				denominatorfactorlist,
				{position, 1}
			]
			,
			(* It's possible this never actually occurs. *)
(* testprint *)
Print["didn't manage to absorb the constant factor"];
			denominatorfactorlist = {{denominator, 1}};
			denominatorexponent = 1
		]
	];
	denominator = Times @@ (Power[#1, #2/denominatorexponent] &) @@@ denominatorfactorlist;
	If[TrueQ[OptionValue[Monitor]],
		PrintTemporary[Row[{"Computing ", "denominator"^(modulus - modulus/p)}]]
	];
	factor = Expand[denominator^(modulus - modulus/p), Modulus -> modulus];
	If[TrueQ[OptionValue[Monitor]],
		PrintTemporary[Row[{"Binning monomials of ", "denominator"^(modulus - modulus/p)}]]
	];
	factor = Replace[
		(* Bin monomials by the (negative) differences of their exponents modulo p (according to the diagonal we're interested in). *)
		Last[Reap[
			Function[monomial,
				Sow[
					monomial,
					{Mod[Join @@ (Exponent[monomial, Rest[#]] - Exponent[monomial, First[#]] &) /@ variablepartition, p]}
				];
			] /@ FastMonomialList[factor];,
			Tuples[Range[0, p - 1], Length[variables] - Length[variablerepresentatives]]
		]],
		{{} -> 0, {list_} :> Total[list]},
		{1}
	];
	statecount = 1;
	If[degree === "High",
		If[denominatorexponent == modulus,
			newstate = Expand[denominatorconstantinverse Numerator[rationalexpression], Modulus -> modulus]
			,
			(* We can use the binned monomials of  factor . *)
			If[TrueQ[OptionValue[Monitor]],
				If[modulus/p != denominatorexponent,
					PrintTemporary[Row[{"Computing ", Inactive[Times]["numerator", "denominator"^(modulus/p - denominatorexponent)], " for the initial state"}]],
					PrintTemporary[Row[{"Expanding ", "numerator", " for the initial state"}]]
				]
			];
			newstate = Expand[denominatorconstantinverse Numerator[rationalexpression] denominator^(modulus/p - denominatorexponent), Modulus -> modulus];
			If[TrueQ[OptionValue[Monitor]],
				PrintTemporary[Row[{
					"Binning monomials of ", Inactive[Times]["numerator", "denominator"^(modulus/p - denominatorexponent)],
					" and multiplying by binned monomials of ", "denominator"^(modulus - modulus/p)
				}]]
			];
			(* Multiply by  factor , keeping only monomials with exponents that are congruent to each other (according to the diagonal we're interested in). *)
			newstate = CongruentMonomialTimes[FastMonomialList[newstate], factor, p, variablepartition, Modulus -> modulus]
		]
		,
		If[TrueQ[OptionValue[Monitor]] && modulus/p != denominatorexponent,
			If[modulus/p != denominatorexponent,
				PrintTemporary[Row[{"Computing ", Inactive[Times]["numerator", "denominator"^(modulus/p - denominatorexponent)], " for the initial state"}]],
				PrintTemporary[Row[{"Expanding ", "numerator", " for the initial state"}]]
			]
		];
		newstate = Expand[denominatorconstantinverse Numerator[rationalexpression] denominator^(modulus/p - denominatorexponent), Modulus -> modulus]
	];
	memorystorage = Replace[OptionValue[StateStorage],
		{
			"Disk" | {"Disk", ___, "Directory" -> Automatic, ___} :> (
				directory = $TemporaryDirectory;
				False
			),
		 	{"Disk", ___, "Directory" -> dir_, ___} :> (
				directory = dir;
				False
			),
			"Memory" ->
				True,
			_ ->
				False
		}
	];
	If[memorystorage,
		state[statecount] = newstate,
		Export[FileNameJoin[{directory, ToString[statecount] <> ".m"}], newstate]
	];
	statehashassociation = Association[];
	statehashassociation[Hash[newstate]] = statecount;
	output = Association[];
	output[statecount] = ConstantTerm[newstate, variables];
	stateindex = 1;
(*
unprocessedstatecounts = {};
*)
	starttime = DateObject[];
	If[TrueQ[OptionValue[Monitor]] && 10 < $VersionNumber < 11,
		Message[Monitor::abort]
	];
	(* For automata that don't fit in memory, Reap (not Join) takes a long time to assemble the edge list. *)
	edges = Join @@ Reap[
		If[TrueQ[OptionValue[Monitor]] && !(10 < $VersionNumber < 11), Monitor, List][
			While[stateindex <= statecount,
(*
AppendTo[unprocessedstatecounts, statecount - stateindex];
*)
				Sow[
					MapIndexed[
						Function[{monomiallist, index},
							(* Reap isn't consistent. *)
							newstate = If[monomiallist == {},
								0,
								If[degree === "High",
									(* Multiply the image of the current state under the current Cartier operator by  factor ,
									   keeping only monomials with exponents that are congruent to each other (according to the diagonal we're interested in). *)
									CongruentMonomialTimes[First[monomiallist], factor, p, variablepartition, Modulus -> modulus],
									Total[First[monomiallist]]
								]
							];
(* TODO Do associations do their own hashing, so that manual hashing is actually less efficient? *)
							newstatehash = Hash[newstate];
							newstateindex = statehashassociation[newstatehash];
							If[
								And[
									checkstatesameness,
									!MissingQ[newstateindex],
									If[memorystorage,
										state[newstateindex],
										Import[FileNameJoin[{directory, ToString[newstateindex] <> ".m"}]]
									] =!= newstate
								]
								,
								Message[AutomaticSequenceReduce::hash, newstatehash];
								newstateindex = Missing["NotFound"]
							];
							{
								stateindex -> If[MissingQ[newstateindex],
									statecount++;
									If[memorystorage,
										state[statecount] = newstate,
										Export[FileNameJoin[{directory, ToString[statecount] <> ".m"}], newstate]
									];
									statehashassociation[newstatehash] = statecount;
									output[statecount] = ConstantTerm[newstate, variables];
									statecount
									,
									newstateindex
								],
								DigitList[index[[1]] - 1, p, Length[variablerepresentatives]]
							}
						],
						(* Bin monomials by their exponents modulo p (using the fact that we're interested in a certain diagonal), and quotient the exponents by p.
						   This applies all relevant Cartier operators at once. *)
						Last[Reap[
							Function[monomial,
								Sow[
									monomial /. (var : variablepattern)^exponent_. :> var^Quotient[exponent, p],
									{Mod[Exponent[monomial, variablerepresentatives], p]}
								];
							] /@
								FastMonomialList[
									If[degree === "High",
										If[memorystorage,
											state[stateindex],
											Import[FileNameJoin[{directory, ToString[stateindex] <> ".m"}]]
										],
										(* Multiply the current state by  factor ,
										   keeping only monomials with exponents that are congruent to each other (according to the diagonal we're interested in). *)
										Replace[
											If[memorystorage,
												state[stateindex],
												Import[FileNameJoin[{directory, ToString[stateindex] <> ".m"}]]
											],
											s : Except[0] :> CongruentMonomialTimes[FastMonomialList[s], factor, p, variablepartition, Modulus -> modulus]
										]
									]
								];
							,
							Tuples[Range[0, p - 1], Length[variablerepresentatives]]
						]]
					]
				];
				If[!checkstatesameness,
					If[memorystorage,
						Unset[state[stateindex]],
						DeleteFile[FileNameJoin[{directory, ToString[stateindex] <> ".m"}]]
					]
				];
				stateindex++
			],
(*
]; Echo[statecount],
*)
			Column[{
				Row[{"Processing state ", stateindex, " of ", statecount}],
				ProgressIndicator[(stateindex - 1)/statecount],
(*
ListPlot[unprocessedstatecounts, ImageSize -> 350],
*)
				If[stateindex == 1,
					Row[{}],
					Row[{"Processing known states will finish at ", DatePlus[starttime, statecount/(stateindex - 1) DateDifference[starttime, DateObject[]]]}]
				]
			}]
		];
(* don't keep this *)
If[TrueQ[OptionValue[Monitor]],
	PrintTemporary["done with Monitor"]
];
		If[checkstatesameness,
(* keep this? *)
If[TrueQ[OptionValue[Monitor]],
		PrintTemporary["Clearing states"]
];
(*
Print[state /@ Range[statecount]];
*)
			If[memorystorage,
				(* Unsetting the states one at a time seems to be better than  Clear[state]  for avoiding a time-consuming memory spike when states have been swapped to disk. *)
				Unset[state[#]] & /@ Range[statecount, 1, -1],
				DeleteFile[FileNameJoin[{directory, ToString[#] <> ".m"}] & /@ Range[statecount]]
			]
		];
(* don't keep this *)
If[TrueQ[OptionValue[Monitor]],
	PrintTemporary["Reaping"]
]
	][[2, 1]];
(* don't keep this *)
If[TrueQ[OptionValue[Monitor]],
	PrintTemporary["done Reaping"]
];
(*
Echo[ByteCount[reap], "reap ByteCount"];
Echo[AbsoluteTiming[MaxMemoryUsed[Flatten[reap, 1]]], Flatten];
Echo[AbsoluteTiming[MaxMemoryUsed[Catenate[reap]]], Catenate];
Echo[AbsoluteTiming[MaxMemoryUsed[Join @@ reap]], Join];
*)
(*
Echo[unprocessedstatecounts];
Echo[ListPlot[unprocessedstatecounts]];
Clear[unprocessedstatecounts];
*)
	If[TrueQ[OptionValue[FlattenInputAlphabet]] && Length[variablepartition] == 1,
(* keep this? *)
If[TrueQ[OptionValue[Monitor]],
	PrintTemporary["Flattening edges"]
];
		edges = MapAt[First, 2] /@ edges
	];
(* keep this? *)
If[TrueQ[OptionValue[Monitor]],
	PrintTemporary["Constructing automaton"]
];
	automaton = Automaton[edges, 1, Normal[output]];
	If[TrueQ[OptionValue[Minimize]],
		If[TrueQ[OptionValue[Monitor]],
			PrintTemporary["Minimizing"]
		];
		automaton = AutomatonMinimize[automaton]
	];
(* don't keep this *)
If[TrueQ[OptionValue[Monitor]],
	PrintTemporary["Returning"]
];
	automaton
]
Options[DiagonalSequenceAutomaton] = {
	"Degree" -> Automatic,
	FlattenInputAlphabet -> True,
	HashStateNames -> False,
	Method -> "LowDegree",
	Minimize -> True,
	Monitor -> False,
	StateStorage -> "Memory"
}
SyntaxInformation[DiagonalSequenceAutomaton] = {"ArgumentsPattern" -> {_, _, OptionsPattern[]}}
DiagonalSequenceAutomaton::bdmtd = "Value of option Method -> `1` must be \"HighDegree\" or \"LowDegree\"."

AutomaticSequenceReduce[
	expression : (BaumSweet | RudinShapiro | ThueMorse)[n_],
	{n_?PlausibleVariableQ},
(*
	numerationsystem : _Integer?Positive(* more general numeration system? at least check that it's an integer >= 2? *) : 2,
*)
	OptionsPattern[]
] :=
(* XXX This ignores any Method option. Is that the right thing to do?
   Maybe it should issue a message. But not if we're AutomaticSequenceReduce[]ing something like BaumSweet[n] + Mod[CatalanNumber[n],4] *)
(* This evaluates even if none of the cases are matched, unlike other *Reduce symbols. *)
	Replace[
		expression,
		{
			BaumSweet[x_] (*/; numerationsystem === 2*) :>
				AutomaticSequence[$BaumSweetAutomaton][x],
			RudinShapiro[x_] (*/; numerationsystem === 2*) :>
				AutomaticSequence[$RudinShapiroAutomaton][x],
			ThueMorse[x_] (*/; numerationsystem === 2*) :>
				AutomaticSequence[$ThueMorseAutomaton][x]
		}
	]
AutomaticSequenceReduce[
	Mod[
		originalsequence_[nsequence__],
		modulus_?PrimePowerQ
		(*, XXX optional argument *)
	],
	{nsequence__?PlausibleVariableQ},
	(* XXX optional numeration system, *)
	options : OptionsPattern[]
] /;
	Or[
		MatchQ[
			OptionValue[AutomaticSequenceReduce, {options}, Method],
			Automatic | "ConstantTerm" | "Diagonal" | {"Diagonal", "Degree" -> "High" | "Low"} | "OrePolynomial"
		],
		Message[AutomaticSequenceReduce::bdmtd, OptionValue[AutomaticSequenceReduce, {options}, Method]]; False
	] :=
Module[{method, sequence, polynomialfunction, automaton, seriesvariables, y, failed},

(* TODO incorporate: where do the derivative conditions go, and where do we use the modulus?
	failed = Catch[
		If[method =!= "OrePolynomial",
			If[
				And[
					Divisible[Coefficient[polynomial /. x -> 0, y, 0], modulus],
					GCD[Coefficient[polynomial /. x -> 0, y, 1], modulus] == 1
				],
				(* The diagonal method applies. *)
				If[method === Automatic,
					method = "LowDegree"
				],
				(* The diagonal method does not apply. *)
				If[method === Automatic,
					If[PrimeQ[modulus],
						method = "OrePolynomial",
						Message[ChristolAutomaton::mod, polynomial]; Throw[True]
					],
					Message[ChristolAutomaton::der, polynomial, method]; Throw[True]
				]
			]
		];
*)

(* TODO If the sequence has a Modulus option, need to reconcile it with the modulus. *)

	failed = Catch[
		method = Switch[OptionValue[Method],
			"OrePolynomial" /; !PrimeQ[modulus],
				Message[AutomaticSequenceReduce::oremod]; Throw[True],
			Alternatives[
				Automatic /;
					And[
						!FreeQ[originalsequence, _AlgebraicSequence],
						FreeQ[originalsequence, _ConstantTermSequence | _DiagonalSequence],
						PrimeQ[modulus]
					],
				"OrePolynomial"
			],
				"OrePolynomial",
			Alternatives[
				Automatic /; FreeQ[originalsequence, _AlgebraicSequence | _DiagonalSequence],
				"ConstantTerm"
			],
				"ConstantTerm",
			_,
				"Diagonal"
		];
		sequence = Replace[
			originalsequence,
			algebraicsequence_AlgebraicSequence /; !MemberQ[algebraicsequence, Modulus -> _] :>
				Append[algebraicsequence, Modulus -> modulus]
		][nsequence];
		Switch[method,
			"ConstantTerm" /; Length[{nsequence}] == 1,
				(* TODO Support multivariate sequences. *)
				sequence = ConstantTermSequenceReduce[sequence, nsequence];
				If[!MatchQ[sequence, _ConstantTermSequence[nsequence]],
					Message[AutomaticSequenceReduce::method, originalsequence[nsequence], method]; Throw[True]
				];
				sequence = Replace[
					(* Drop the argument. *)
					Head[sequence],
					{
						ConstantTermSequence[powerpolynomial_, varspec_] :>
							ConstantTermSequence[
								powerpolynomial,
								1,
								If[ListQ[varspec], varspec, {varspec}]
							],
						ConstantTermSequence[powerpolynomial_, factorpolynomial_, varspec_] :>
							ConstantTermSequence[
								powerpolynomial,
								factorpolynomial,
								If[ListQ[varspec], varspec, {varspec}]
							]
					}
				];
				automaton = ConstantTermSequenceAutomaton[
					sequence,
					modulus,
					Sequence @@ Replace[
						{options},
						{
							(FlattenInputAlphabet -> _) ->
								Nothing,
							(Method -> method) ->
								Nothing
						},
						{1}
					]
				],
			"Diagonal" /; Length[{nsequence}] == 1,
				(* This only works for one-dimensional sequences.  For multidimensional sequences we'd need to construct a different rational expression and take a multidimensional diagonal. *)
(* TODO allow multidimensional sequences through to DiagonalSequenceAutomaton *)
				sequence = DiagonalSequenceReduce[sequence, nsequence];
				If[!MatchQ[sequence, _DiagonalSequence[nsequence]],
					Message[AutomaticSequenceReduce::method, originalsequence[nsequence], method]; Throw[True]
				];
				(* Factoring the denominator speeds up  Expand[denominator^(modulus - modulus/p), Modulus -> modulus]  in DiagonalSequenceAutomaton. *)
				If[!MatchQ[originalsequence, _DiagonalSequence],
					sequence = MapAt[Numerator[#]/Factor[Denominator[#]] &, sequence, {0, 1}]
				];
				sequence = Replace[
					(* Drop the argument. *)
					Head[sequence],
					{
						DiagonalSequence[rationalexpression_, variables : Except[{__List}, {Except[_List] ..}], sequenceoptions : OptionsPattern[]] :>
							DiagonalSequence[rationalexpression, {variables}, sequenceoptions],
						DiagonalSequence[rationalexpression_, variable : Except[_List], sequenceoptions : OptionsPattern[]] :>
							DiagonalSequence[rationalexpression, {{variable}}, sequenceoptions]
					}
				];
				automaton = DiagonalSequenceAutomaton[
					MapAt[FragileTogether, sequence, 1],
					modulus,
					Sequence @@ Replace[
						{options},
						{
							(CompressStateNames -> compressstatenames_) :>
								(If[TrueQ[compressstatenames], Message[AutomaticSequenceReduce::cmprss, "method Diagonal"]]; Nothing),
							(Method -> method) ->
								Nothing,
							(Method -> {"Diagonal", "Degree" -> degree_}) :>
								("Degree" -> degree)
						},
						{1}
					]
				],
			"OrePolynomial",
				sequence = AlgebraicSequenceReduce[sequence, {nsequence}];
				If[!MatchQ[sequence, AlgebraicSequence[_SeriesRoot, OptionsPattern[]][nsequence]],
					Message[AutomaticSequenceReduce::method, originalsequence[nsequence], method]; Throw[True]
				];
				Replace[
					(* Drop the argument. *)
					Head[sequence],
					{
						AlgebraicSequence[
							seriesroot : SeriesRoot[{f_Function, root_}, OptionsPattern[]],
							sequenceoptions : OptionsPattern[]
						]?SeriesRootAlgebraicSequenceObjectQ :>
							(
								seriesvariables = SeriesVariables[root];
								polynomialfunction = f;
								sequence = AlgebraicSequence[seriesroot, Sequence @@ DeleteDuplicates[{sequenceoptions, Modulus -> modulus}]]
							),
						_ :>
							(Message[AutomaticSequenceReduce::method, originalsequence[nsequence], method]; Throw[True])
					}
				];
				If[!PolynomialQ[polynomialfunction[y], Append[seriesvariables, y]],
					Message[AutomaticSequenceReduce::method, originalsequence[nsequence], method]; Throw[True]
				];
				If[!MatchQ[CoefficientRules[polynomialfunction[y], Append[seriesvariables, y]], {(_ -> _Integer) ..}],
(* xxx if there are rational coefficients, try to fix this by multiplying by a common denominator?  does this occur? *)
					Message[AutomaticSequenceReduce::coeffs, polynomialfunction]; Throw[True]
				];
				Switch[CoefficientRules[polynomialfunction[y], y, Modulus -> modulus],
					{0 -> _},
						Message[AutomaticSequenceReduce::polymod, polynomialfunction, modulus]; Throw[True],
					{_},
(* We're working with the zero sequence, which should in theory be okay but causes problems in AlgebraicSequenceAutomaton because  z1expressedinhigherpowers  is 0. *)
(* Example:  x^2 y^2 + 2 (2 x^2 + x - 1) y + 2 (x^2 + x)  modulo 2. *)
						Message[AutomaticSequenceReduce::polymod, polynomialfunction, modulus]; Throw[True],
					_,
						Null
				];
				automaton = AlgebraicSequenceAutomaton[
					sequence,
					Sequence @@ Replace[
						{options},
(* xxx don't I want this?
							(CompressStateNames -> compressstatenames_) :>
								(If[TrueQ[compressstatenames], Message[AutomaticSequenceReduce::cmprss, "method OrePolynomial"]]; Nothing),
*)
						(Method -> method) -> Nothing,
						{1}
					]
				];
				If[MatchQ[automaton, _AlgebraicSequenceAutomaton],
					Throw[True]
				]
		];
		False
	];
	AutomaticSequence[automaton(*, XXX*)][nsequence] /; !failed && MatchQ[automaton, _Automaton]
]
AutomaticSequenceReduce[
	(originalsequence : AlgebraicSequence[SeriesRoot[_, Modulus -> modulus_?PrimePowerQ]])[nsequence__],
	{nsequence__?PlausibleVariableQ},
	(* XXX optional numeration system, *)
	options : OptionsPattern[]
] :=
With[
	{sequence = AutomaticSequenceReduce[
		Mod[originalsequence[nsequence], modulus],
		{nsequence},
		options
	]},
	sequence /; !MatchQ[sequence, _AutomaticSequenceReduce]
]
AutomaticSequenceReduce[
	(sequence_AutomaticSequence)[n_],
	{n_?PlausibleVariableQ},
(*
	numerationsystem : _Integer?Positive(* more general numeration system? at least check that it's an integer >= 2? *) : (* xxx not the right default *) 2,
*)
	OptionsPattern[]
] :=
(* XXX This ignores any Method option. Is that the right thing to do? *)
(* xxx TODO this check isn't very general; what if  sequence  is multi-dimensional? *)
	sequence[n] (*/; {numerationsystem} === AutomaticSequenceNumerationSystemList[sequence]*)
AutomaticSequenceReduce[
	expression_,
	n_?PlausibleVariableQ,
	(* XXX optional numeration system, *)
	options : OptionsPattern[]
] :=
With[{sequence = AutomaticSequenceReduce[expression, {n}, options]},
	sequence /; !MatchQ[sequence, _AutomaticSequenceReduce]
]
Options[AutomaticSequenceReduce] = {
	(* xxx better option name? should it be a suboption of the Method since it doesn't apply to the diagonal method? *)
	Compile -> True,
	CompressStateNames -> Automatic,
	FlattenInputAlphabet -> True,
	HashStateNames -> False,
	Method -> Automatic,
	(* xxx better option name? *)
	Minimize -> True,
	Monitor -> False,
	StateStorage -> "Memory"
}
SyntaxInformation[AutomaticSequenceReduce] = {"ArgumentsPattern" -> {_, _, (*_.,*) OptionsPattern[]}}
AutomaticSequenceReduce::bddeg = "Value of option \"Degree\" -> `1` must be Automatic, \"High\", or \"Low\"."
AutomaticSequenceReduce::bdmtd = "Value of option Method -> `1` must be Automatic, \"ConstantTerm\", \"Diagonal\", or \"OrePolynomial\"."
AutomaticSequenceReduce::bdstg = "Value of option StateStorage -> `1` must be \"Disk\" or \"Memory\"."
AutomaticSequenceReduce::cmprss = "State compression is not supported for `1`; using uncompressed states."
AutomaticSequenceReduce::coeff = "Coefficients of the power series `1` are not `2`\[Hyphen]adic integers."
AutomaticSequenceReduce::coeffs = "Polynomial function `1` must have integer coefficients."
AutomaticSequenceReduce::denom = "Constant term in the denominator of `1` must be invertible modulo `2`."
AutomaticSequenceReduce::hash = "Hash value `1` occurs for two distinct states; resulting automaton may not be correct."
AutomaticSequenceReduce::method = "Unable to convert `1` to use Method `2`."
AutomaticSequenceReduce::oremod = "Method \"OrePolynomial\" requires a prime modulus."
AutomaticSequenceReduce::polymod = "Polynomial function `1` reduces to a monomial modulo `2`."
(* Should this message also indicate that there may be no roots? *)
AutomaticSequenceReduce::soln = "Polynomial function `1` has multiple roots near `2`. Specify more terms."
AutomaticSequenceReduce::srsdim = "Root `1` is needed up to dimensions `2`. Specify more terms."

(*** end AutomaticSequenceReduce code ***)


(automaton : Automaton[edges_, initialstate_, ___]?AutomatonQ)[input_List] :=
With[
	{
		transitionrules = Append[
			Replace[
				edges,
				{instate_ -> outstate_, label_} :> ({instate, label} -> outstate),
				{1}
			],
			_ -> $Failed
		]
	},
	Replace[
		Fold[
			Replace[{##}, transitionrules] &,
			initialstate,
			input
		],
		AutomatonOutputRules[automaton]
	]
]
(* Any options that are added here need to also be added to $AutomatonOutputRulesPattern. *)
Options[Automaton] = {InputAlphabet -> Automatic}
SyntaxInformation[Automaton] = {"ArgumentsPattern" -> {_, _, _., OptionsPattern[]}}

AutomatonAdjacencyMatrix[automaton_?AutomatonQ] :=
	AdjacencyMatrix[VertexDelete[
		AutomatonGraph[automaton, GatherEdges -> False],
		Null
	]]
SyntaxInformation[AutomatonAdjacencyMatrix] = {"ArgumentsPattern" -> {_}}

(* TODO TransitionSequence[] is supported, but nonempty TransitionSequence[ ]s aren't *)
AutomatonDeterminize[
	originalautomaton : Automaton[originaledges_, originalinitialstate_, ___]?AutomatonQ,
	outputfunction : Except[_Rule] : Identity,
	OptionsPattern[]
] :=
Module[
	{
		inputalphabet, initialstate, epsilontransitiongraph,
		statelist, statecount, stateindex, edges, currentstate, newstate, originaloutputrules, determinizedautomaton
	},
	inputalphabet = AutomatonInputAlphabet[originalautomaton];
(* TODO Don't I need to check  !MatchQ[inputalphabet, _AutomatonInputAlphabet] ? *)
	epsilontransitiongraph = Graph[
		AutomatonStateList[originalautomaton],
		Cases[originaledges, {rule_Rule, TransitionSequence[]} :> rule]
	];
	initialstate = If[AutomatonInitialStateMode[originalautomaton, AutomatonDeterminize] == "StateList",
		originalinitialstate,
		{originalinitialstate}
	];
	statelist = {initialstate};
	statecount = 1;
	stateindex = 1;
(* xxx support Monitor, HashState, and StateStorage? *)
	edges = Join @@ Reap[
		While[stateindex <= statecount,
			currentstate = statelist[[stateindex]];
			Sow[
				Function[letter,
					newstate = Union @@ Function[originalstate, Cases[originaledges, {originalstate -> s_, label_ /; MatchQ[letter, label]} :> s]] /@ currentstate;
(*
Print["newstate:", Tab, newstate];
*)
					(* Add to  newstate  the states in the original automaton that are reachable by epsilon transitions from the states we just put into  newstate . *)
					newstate = Union[
						newstate,
						VertexOutComponent[epsilontransitiongraph, newstate]
					];
(*
Print["newstate:", Tab, Tab, newstate];
*)
(* TODO Should I do the whole hashing states business?  Store the states as down values rather than in a list?  Allow them to be written to disk, etc.?  Monitor a progress bar? *)
					If[!MemberQ[statelist, newstate],
						statecount++;
						AppendTo[statelist, newstate]
					];
					{currentstate -> newstate, letter}
				] /@ inputalphabet
			];
			stateindex++
		]
	][[2, 1]];
	originaloutputrules = AutomatonOutputRules[originalautomaton];
	determinizedautomaton = Automaton[
		edges,
		initialstate,
		Function[s, s -> outputfunction[Replace[s, originaloutputrules, {1}]]] /@ statelist,
		InputAlphabet -> inputalphabet
	];
(*
Print[determinizedautomaton];
*)
	If[TrueQ[OptionValue[Minimize]],
		determinizedautomaton = AutomatonMinimize[determinizedautomaton, IndexedStateNames -> OptionValue[IndexedStateNames]],
		If[TrueQ[OptionValue[IndexedStateNames]],
			determinizedautomaton = IndexAutomaton[determinizedautomaton]
		]
	];
	determinizedautomaton
]
Options[AutomatonDeterminize] = {IndexedStateNames -> True, Minimize -> True}
SyntaxInformation[AutomatonDeterminize] = {"ArgumentsPattern" -> {_, _., OptionsPattern[]}}
AutomatonDeterminize::initamb = "Initial state specification `1` is both a state and a list of states.  Interpreting as a list of states."

AutomatonGraph[
	automaton : Automaton[edges_ /; !MemberQ[edges, {_[___, Null, ___], _}], initialstate_, ___]?AutomatonQ,
	options : OptionsPattern[]
] :=
With[{outputrules = AutomatonOutputRules[automaton]},
	Graph[
		Prepend[
			Function[{edge, labels},
				Labeled[
					If[outputrules === {},
						edge,
						Interpretation[Replace[#, outputrules], #] & /@ edge
					],
					If[Length[labels] == 1, First[labels], Row[Riffle[labels, ","]]]
				]
			] @@@ If[OptionValue[GatherEdges],
				KeyValueMap[{#1, #2} &, GroupBy[edges, First -> Last]],
				MapAt[List, 2] /@ edges
			],
			(* AutomatonAdjacencyMatrix assumes the initial state is  Null . *)
			Null -> If[outputrules === {},
				initialstate,
				Interpretation[Replace[initialstate, outputrules], initialstate]
			]
		],
		Sequence @@ DeleteCases[{options}, GatherEdges -> _],
(*
		GraphStyle -> "DiagramBlue",
*)
		EdgeShapeFunction -> {{"CorporateShortCarvedArrow", "ArrowSize" -> .04, "ArrowPositions" -> 1}},
		EdgeStyle -> Directive[Gray, Opacity[1]],
		(* It's a bug that this is necessary to get edge arrows placed correctly. *)
		PerformanceGoal -> "Quality",
		(* TODO I can probably use  outputrules  here instead of hackily using Interpretation to get the vertex label. *)
		(* The vertex labels look a little low when graphs are converted to graphics and then exported as pdf; maybe I should raise them.  What if the Graph is directly exported as pdf?
		   But labels actually look a little too high in the front end. *)
		VertexLabels -> {vertex_ :> Placed[vertex, {1/2, 1/2}]},
(* I guess this is not necessary.
		VertexLabelStyle -> {Null -> Sequence[]},
*)
		VertexShapeFunction -> {_ -> "Circle", Null -> None},
		VertexSize -> .2,
		VertexStyle -> Hue[.6, .3, .8]
	]
]
(* Ideally these default option values would reflect the values actually used by AutomatonGraph. *)
Options[AutomatonGraph] = Sort[Append[Options[Graph], GatherEdges -> True]]
SyntaxInformation[AutomatonGraph] = {"ArgumentsPattern" -> {_, OptionsPattern[]}}

AutomatonInputAlphabet[Automaton[___, InputAlphabet -> alphabet_List, ___]?AutomatonQ] :=
	alphabet
AutomatonInputAlphabet[Automaton[edges : {{_, _?AutomatonInputSymbolQ | TransitionSequence[]} ..}, __]?AutomatonQ] :=
	DeleteCases[DeleteDuplicates[Last /@ edges], TransitionSequence[]]
AutomatonInputAlphabet[Automaton[arguments___, InputAlphabet -> Automatic, options___]] :=
	AutomatonInputAlphabet[Automaton[arguments, options]]
SyntaxInformation[AutomatonInputAlphabet] = {"ArgumentsPattern" -> {_}}

(* old method.  I thought it was going to be much slower, but it's actually faster? *)
AutomatonMinimize[
	automaton : Automaton[_, initialstate_, ___]?AutomatonQ,
	OptionsPattern[]
] /; True :=
(* This is an implementation of Moore's algorithm.  Hopcroft's algorithm should be faster in some cases. *)
Module[
	{
		inputalphabet, outputrules, originalstatelist, originaledges, imagelist, statelist,
		edges, statecount, state, statehash, stateindex, output,
		remainingstateindices, newstates, stateassignmentrules, letter, failed, i
	},
	failed = Catch[
(*
Print[Tab, "compute inputalphabet"];
*)
		inputalphabet = AutomatonInputAlphabet[automaton];
		If[MatchQ[inputalphabet, _AutomatonInputAlphabet],
			Message[AutomatonMinimize::input]; Throw[True]
		];
(*
Print[Tab, "compute outputrules"];
*)
		outputrules = Dispatch[AutomatonOutputRules[automaton]];
		(* Remove unreachable states. *)
(*
Print[Tab, "remove unreachable states"];
*)
		originalstatelist = AutomatonReachableStateList[automaton, inputalphabet];
(*
Print[Tab, Export["outputrules.m", outputrules]];
Print[Tab, Export["originalstatelist.m", originalstatelist]];
*)
(*
Print[Tab, "state count: ", Length[originalstatelist]];
Print[Tab, "extract edges"];
*)
		originaledges = Cases[First[automaton], {Alternatives @@ originalstatelist -> _, _}];
		(* Compute the image of each state under its out-edges. *)
(*
Print[Tab, Export["edges2.m", originaledges]];
Print[Tab, Export["inputalphabet.m", inputalphabet]];
*)
(*
Print[Tab, "map over originalstatelist"];
*)
(* XXX Not sure this is worth splitting into cases as is. *)
		If[MatchQ[originaledges, {{_, _?AutomatonInputSymbolQ} ..}],
(*
Print["No edge labels contain patterns."];
*)
			(* No edge labels contain patterns. *)
(* too slow
			Function[state,
				(* Would this be faster to use later as a Dispatch table instead? *)
				imagelist[state] = Table[
					FirstCase[
						originaledges,
						{state -> s_, letter} :> s,
						Message[AutomatonMinimize::undef, letter, state]; Throw[True]
					],
					{letter, inputalphabet}
				];
			] /@ originalstatelist
*)
			Function[stateedges,
				(* Would this be faster to use later as a Dispatch table instead? *)
				imagelist[stateedges[[1, 1, 1]]] = Table[
					FirstCase[
						stateedges,
						{_ -> s_, letter} :> s,
						Message[AutomatonMinimize::undef, letter, stateedges[[1, 1, 1]]]; Throw[True]
					],
					{letter, inputalphabet}
				];
			] /@ GatherBy[originaledges, #[[1, 1]] &]
			,
(*
Print["Some edge labels contain patterns."];
*)
			(* Some edge labels contain patterns. *)
(* XXX TODO rewrite as above *)
			Function[originalstate,
				(* Would this be faster to use later as a Dispatch table instead? *)
				imagelist[originalstate] = Table[
					FirstCase[
						originaledges,
						{originalstate -> s_, label_ /; MatchQ[letter, label]} :> s,
						Message[AutomatonMinimize::undef, letter, originalstate]; Throw[True]
					],
					{letter, inputalphabet}
				];
			] /@ originalstatelist
		];
(*
Print[Tab, Column[imagelist /@ Take[originalstatelist, 10]]];
*)
		(* Combine equivalent states.  XXX well really what's happening is that we split a class of states when they are inequivalent *)
(* up to here, both variants are identical *)
(* old method.  I thought it was going to be much slower, but it's actually faster? *)
(*
PrintTemporary[Tab, FixedPoint];
tempcount=0;
Monitor[
*)
		statelist = FixedPoint[
			Function[stateclasslist,
(*
tempcount++;
templist = Echo[
*)
				Join @@ Function[stateclass,
					(* If the state class breaks up into multiple pieces, then it might be better to go to the next FixedPoint iteration rather than complete the current one,
					   since the other classes need to be computed with the new information.  Currently we don't do this. *)
					GatherBy[
						stateclass,
						Function[originalstate,
(* xxx Instead of Position this could also be Cases.  Is that better/faster?
   Create a PositionIndex association for speed? *)
							Position[stateclasslist, {___, #, ___}, {1}, 1] & /@ imagelist[originalstate]
						]
					]
				] /@ stateclasslist
(*
]
*)
			],
(*
Echo@
*)
			GatherBy[
				originalstatelist,
				Replace[#, outputrules] &
			]
		];
(*
, {tempcount, Length[templist]}
];
*)
		stateassignmentrules = Function[newstate,
			Alternatives @@ newstate -> newstate
		] /@ statelist;
		False
	];
	If[TrueQ[OptionValue[IndexedStateNames]], IndexAutomaton, Identity][
		Automaton[
			Join @@ Function[newstate,
				Transpose[{
					newstate -> # & /@ Replace[imagelist[First[newstate]], stateassignmentrules, {1}],
					inputalphabet
				}]
			] /@ statelist,
			Replace[initialstate, stateassignmentrules],
			Function[s, s -> Replace[First[s], outputrules]] /@ statelist,
			(* TODO Should we omit this if the input automaton didn't have an explicit InputAlphabet?
			   xxx Well, it should be smart about it. *)
			InputAlphabet -> inputalphabet
		]
	] /; !failed
]
(* newer, slower *)
AutomatonMinimize[
	automaton : Automaton[_, initialstate_, ___]?AutomatonQ,
	OptionsPattern[]
] /; False :=
(* This is an implementation of Moore's algorithm.  Hopcroft's algorithm should be faster in some cases. *)
Module[
	{
		inputalphabet, outputrules, originalstatelist, originaledges, imagelist, statelist,
		edges, statecount, state, statehash, stateindex, output,
		remainingstateindices, newstates, stateassignmentrules, letter, failed, i
	},
	failed = Catch[
(*
Print[Tab, "compute inputalphabet"];
*)
		inputalphabet = AutomatonInputAlphabet[automaton];
		If[MatchQ[inputalphabet, _AutomatonInputAlphabet],
			Message[AutomatonMinimize::input]; Throw[True]
		];
(*
Print[Tab, "compute outputrules"];
*)
		outputrules = Dispatch[AutomatonOutputRules[automaton]];
		(* Remove unreachable states. *)
(*
Print[Tab, "remove unreachable states"];
*)
		originalstatelist = AutomatonReachableStateList[automaton, inputalphabet];
(*
Print[Tab, Export["outputrules.m", outputrules]];
Print[Tab, Export["originalstatelist.m", originalstatelist]];
*)
(*
Print[Tab, "state count: ", Length[originalstatelist]];
Print[Tab, "extract edges"];
*)
		originaledges = Cases[First[automaton], {Alternatives @@ originalstatelist -> _, _}];
		(* Compute the image of each state under its out-edges. *)
(*
Print[Tab, Export["edges2.m", originaledges]];
Print[Tab, Export["inputalphabet.m", inputalphabet]];
*)
(*
Print[Tab, "map over originalstatelist"];
*)
(* XXX Not sure this is worth splitting into cases as is. *)
		If[MatchQ[originaledges, {{_, _?AutomatonInputSymbolQ} ..}],
(*
Print["No edge labels contain patterns."];
*)
			(* No edge labels contain patterns. *)
(* too slow
			Function[state,
				(* Would this be faster to use later as a Dispatch table instead? *)
				imagelist[state] = Table[
					FirstCase[
						originaledges,
						{state -> s_, letter} :> s,
						Message[AutomatonMinimize::undef, letter, state]; Throw[True]
					],
					{letter, inputalphabet}
				];
			] /@ originalstatelist
*)
			Function[stateedges,
				(* Would this be faster to use later as a Dispatch table instead? *)
				imagelist[stateedges[[1, 1, 1]]] = Table[
					FirstCase[
						stateedges,
						{_ -> s_, letter} :> s,
						Message[AutomatonMinimize::undef, letter, stateedges[[1, 1, 1]]]; Throw[True]
					],
					{letter, inputalphabet}
				];
			] /@ GatherBy[originaledges, #[[1, 1]] &]
			,
(*
Print["Some edge labels contain patterns."];
*)
			(* Some edge labels contain patterns. *)
(* XXX TODO rewrite as above *)
			Function[originalstate,
				(* Would this be faster to use later as a Dispatch table instead? *)
				imagelist[originalstate] = Table[
					FirstCase[
						originaledges,
						{originalstate -> s_, label_ /; MatchQ[letter, label]} :> s,
						Message[AutomatonMinimize::undef, letter, originalstate]; Throw[True]
					],
					{letter, inputalphabet}
				];
			] /@ originalstatelist
		];
(*
Print[Tab, Column[imagelist /@ Take[originalstatelist, 10]]];
*)
		(* Combine equivalent states.  XXX well really what's happening is that we split a class of states when they are inequivalent *)
(* up to here, both variants are identical *)
(* newer, slower *)
(* When a class splits into multiple new classes, we only need to update the classes containing states with out-edges pointing to states in the newly split classes. *)
		statelist = GatherBy[
			originalstatelist,
			Replace[#, outputrules] &
		];
(* alternative, but less parallel to code below
		MapIndexed[
			(state[#2[[1]]] = #1) &,
			statelist
		];
		statecount = Length[statelist];
*)
		statecount = 0;
		(state[++statecount] = #) & /@ statelist;
(* xxx or I could do this if it's faster:
		state /@ Range[Length[statelist]] = statelist;
*)
		remainingstateindices = Range[statecount];
		Monitor[
			While[remainingstateindices != {},
				stateindex = First[remainingstateindices];
				remainingstateindices = (*Echo@*)Rest[remainingstateindices];
				newstates = GatherBy[
					state[stateindex],
					Function[originalstate,
(* xxx is this what's slowing it down?
   Maintain a PositionIndex association for speed, instead of this? *)
						Function[s,
							SelectFirst[Range[statecount], MemberQ[state[#], s] &]
(* xxx or something like this?
							FirstPositionLevel1[state /@ Range[statecount], s]
*)
						] /@ imagelist[originalstate]
					]
				];
				If[Length[newstates] > 1,
					state[stateindex] = First[newstates];
					(state[++statecount] = #) & /@ Rest[newstates];
(* xxx or I could do this if it's faster:
					state /@ Range[xxx, xxx] = Rest[newstates];
*)
					remainingstateindices = DeleteDuplicates[Join[
						remainingstateindices,
						{stateindex},
						Range[statecount - Length[newstates] + 2, statecount]
(* xxx don't I need to add states that need to be re-updated? *)
					]]
				]
			],
			Column[{
				{Length[remainingstateindices], statecount, statecount - Length[remainingstateindices]},
				remainingstateindices
			}]
		];
		stateassignmentrules = Table[
			Alternatives @@ state[i] -> state[i],
			{i, 1, statecount}
		];
		False
	];
	If[TrueQ[OptionValue[IndexedStateNames]], IndexAutomaton, Identity][
		Automaton[
Monitor[
			Join @@ Table[
				Transpose[{
					state[i] -> # & /@ Replace[imagelist[First[state[i]]], stateassignmentrules, {1}],
					inputalphabet
				}],
				{i, 1, statecount}
			],
i],
			Replace[initialstate, stateassignmentrules],
Monitor[
			Table[
				state[i] -> Replace[First[state[i]], outputrules],
				{i, 1, statecount}
			],
i],
			(* TODO Should we omit this if the input automaton didn't have an explicit InputAlphabet?
			   xxx Well, it should be smart about it. *)
			InputAlphabet -> inputalphabet
		]
	] /; !failed
]
Options[AutomatonMinimize] = {IndexedStateNames -> True}
SyntaxInformation[AutomatonMinimize] = {"ArgumentsPattern" -> {_, OptionsPattern[]}}
AutomatonMinimize::input = "Unable to determine the input alphabet."
AutomatonMinimize::undef = "Automaton is undefined when reading `1` from state `2`."

AutomatonOutputAlphabet[automaton : Automaton[edges_, initialstate_, ___]?AutomatonQ] :=
With[{inputalphabet = AutomatonInputAlphabet[automaton]},
	DeleteDuplicates[Replace[
		Join[
			AutomatonReachableStateList[automaton, inputalphabet],
			If[DeterministicAutomatonQ[automaton],
				{},
				{$Failed}
			]
		],
		AutomatonOutputRules[automaton],
		{1}
	]] /; !MatchQ[inputalphabet, _AutomatonInputAlphabet] || Message[AutomatonOutputAlphabet::input]
]
SyntaxInformation[AutomatonOutputAlphabet] = {"ArgumentsPattern" -> {_}}
AutomatonOutputAlphabet::input = "Unable to determine the input alphabet."

(* Options are allowed to be in lists, so  OptionsPattern[]  is matched by lists. *)
AutomatonOutputRules[Automaton[_, _, outputrules : $AutomatonOutputRulesPattern, ___]?AutomatonQ] :=
	outputrules
AutomatonOutputRules[Automaton[_, __]?AutomatonQ] :=
	{}
SyntaxInformation[AutomatonOutputRules] = {"ArgumentsPattern" -> {_}}


(*** AutomatonProduct code ***)

(*
If I expose it or use it outside the current context where edge labels are simple list patterns, the first down value should check that the lists don't have Repeated etc. (as for AutomatonInputAlphabetLength in the notebook); right now it assumes that it can compare the elements pairwise.
That also means that an edge pattern {i_,i_} is bad, even though this is very tempting to use for EqualAutomaton.
*)
SetAttributes[PatternIntersection, Orderless]
PatternIntersection[list1_List, list2_List] /; Length[list1] == Length[list2] :=
	Thread[patternIntersection[list1, list2]] /. patternIntersection -> PatternIntersection
PatternIntersection[pattern_, Verbatim[_]] :=
	pattern
PatternIntersection[pattern_, pattern_] :=
	pattern
PatternIntersection[alternatives1 : HoldPattern[Alternatives][__Integer], alternatives2 : HoldPattern[Alternatives][__Integer]] :=
	Replace[Intersection[alternatives1, alternatives2], HoldPattern[Alternatives][x_] :> x]
PatternIntersection[pattern_, alternatives_Alternatives] /; !MatchQ[pattern, alternatives] :=
	$EmptyPattern
PatternIntersection[pattern1_, pattern2_] /; pattern1 != pattern2 :=
	$EmptyPattern
PatternIntersection[pattern1_, pattern2_] :=
	_?(MatchQ[#, pattern1] && MatchQ[#, pattern2] &)

(* This requires complete automata.  The product automaton simulates two automata simultaneously, so the problem with incomplete automata
   is that if one automaton isn't defined for an input, then this halts the computation of the other automaton on that input as well. *)
(* TODO Is the $EmptyPattern pattern general enough? *)
AutomatonProduct[
	automaton1 : Automaton[edges1_, initialstate1_, ___]?AutomatonQ,
	automaton2 : Automaton[edges2_, initialstate2_, ___]?AutomatonQ,
	outputfunction : Except[_Rule] : Identity,
	OptionsPattern[]
] :=
Module[{inputalphabet1, inputalphabet2, statelist1, statelist2, productautomaton, failed},
	failed = Catch[
(*
If[AutomatonStateCount[automaton1] == 424 && AutomatonStateCount[automaton2] == 470,
	Print[Export["automaton1.m", automaton1]];
	Print[Export["automaton2.m", automaton2]];
	Print[outputfunction];
];
*)
		(* We don't actually use the input alphabets anywhere, so they don't actually need to be the same, but it's not clear what the product is if they're different.
		   Maybe we would use the input alphabet in a more rigorous implementation of PatternIntersection. *)
(*
Print["extracting input alphabets"];
*)
		inputalphabet1 = AutomatonInputAlphabet[automaton1];
		inputalphabet2 = AutomatonInputAlphabet[automaton2];
		If[MatchQ[inputalphabet1, _AutomatonInputAlphabet] || MatchQ[inputalphabet2, _AutomatonInputAlphabet],
			Message[AutomatonProduct::input]; Throw[True]
		];
		If[Sort[inputalphabet1] =!= Sort[inputalphabet2],
			Message[AutomatonProduct::alph]; Throw[True]
		];
		(* We check completeness here instead of earlier so that we issue AutomatonProduct::input above if applicable,
		   instead of having messages generated by CompleteAutomatonQ. *)
(*
Print["checking determinism"];
*)
(* TODO This check is somewhat expensive. *)
		If[!CompleteAutomatonQ[automaton1] || !CompleteAutomatonQ[automaton2],
			Message[AutomatonProduct::com]; Throw[True]
		];
(*
		(* These are inefficient in that they test again whether the automata are complete. *)
XXX No they don't.
*)
(*
Print["extracting state lists"];
*)
		statelist1 = AutomatonStateList[automaton1];
		statelist2 = AutomatonStateList[automaton2];
		productautomaton = Automaton[
(* xxx too memory-intensive for moderate edge counts
			DeleteCases[
				Join @@ Outer[
					{Thread[First /@ {##}, Rule], PatternIntersection @@ Last /@ {##}} &,
					edges1,
					edges2,
					1
				],
				{_, $EmptyPattern | {___, $EmptyPattern, ___}}
			],
*)
			If[MatchQ[edges1, {{_, _?AutomatonInputSymbolQ} ..}] && MatchQ[edges2, {{_, _?AutomatonInputSymbolQ} ..}],
				(* No edge labels contain patterns. *)
(*
Print["No edge labels contain patterns."];
*)
				Join @@ Function[edge1,
					Cases[
						edges2,
						edge2 : {_, Last[edge1]} :>
							{Thread[First /@ {edge1, edge2}, Rule], Last[edge1]}
					]
				] /@ edges1
				,
				(* Some edge labels contain patterns. *)
(*
Print["Some edge labels contain patterns."];
*)
				(* This is essentially Outer on the edge lists, but using Outer is too memory-intensive since we end up deleting so many empty patterns. *)
				Join @@ Function[edge1,
					DeleteCases[
						Function[edge2,
							{Thread[First /@ {edge1, edge2}, Rule], PatternIntersection @@ Last /@ {edge1, edge2}}
						] /@ edges2,
						{_, $EmptyPattern | {___, $EmptyPattern, ___}}
					]
				] /@ edges1
			],
			{initialstate1, initialstate2},
			MapAt[outputfunction, Thread[#, Rule], 2] & /@
				Tuples[{
					Thread[statelist1 -> Replace[statelist1, AutomatonOutputRules[automaton1], {1}]],
					Thread[statelist2 -> Replace[statelist2, AutomatonOutputRules[automaton2], {1}]]
				}],
			InputAlphabet -> inputalphabet1
		];
(*
Print["done computing product"];
*)
		If[TrueQ[OptionValue[Minimize]],
(*
Print["state count: ", AutomatonStateCount[productautomaton]];
Print["minimizing"];
*)
			productautomaton = AutomatonMinimize[productautomaton, IndexedStateNames -> OptionValue[IndexedStateNames]],
(*
Print["done minimizing"];
*)
(* xxx didn't we just compress state names already?  Well this doesn't seem to always fire. *)
			If[TrueQ[OptionValue[IndexedStateNames]],
(*
Print["compressing"];
*)
				productautomaton = IndexAutomaton[productautomaton]
			]
		];
(*
Print["done compressing"];
*)
		False
	];
	productautomaton /; !failed
]
Options[AutomatonProduct] = {IndexedStateNames -> True, Minimize -> True}
SyntaxInformation[AutomatonProduct] = {"ArgumentsPattern" -> {_, _, _., OptionsPattern[]}}
AutomatonProduct::alph = "Input alphabets for the two automata are not the same."
AutomatonProduct::com = "One of the input automata is not complete."
AutomatonProduct::input = "Unable to determine the input alphabet."

(*** end AutomatonProduct code ***)


(*** AutomatonQ code ***)

(* AutomatonInitialStateMode determines whether an automaton has a single initial state or multiple initial states. *)
AutomatonInitialStateMode[
	automaton : Automaton[edges_, initialstatespec_, _, OptionsPattern[]],
	callingfunction_ : None
] :=
	If[ListQ[initialstatespec] && And @@ (MemberQ[edges, {_[___, #, ___], _}] &) /@ initialstatespec,
		If[callingfunction =!= None && MemberQ[edges, {_[___, initialstatespec, ___], _}],
			(* AutomatonDeterminize is the only function that calls AutomatonInitialStateMode with a second argument. *)
			Message[AutomatonDeterminize::initamb, initialstatespec]
		];
		"StateList"
		,
		If[MemberQ[edges, {_[___, initialstatespec, ___], _}],
			"State",
			$Failed
		]
	]

(* This doesn't check that the options are valid options for Automaton, or that the specified InputAlphabet is a list. *)
AutomatonQ[automaton : Automaton[{{Except[$Failed] -> Except[$Failed], _} ...}, _, $AutomatonOutputRulesPattern, OptionsPattern[]]] :=
	AutomatonInitialStateMode[automaton] =!= $Failed
AutomatonQ[Automaton[edges_, initialstate_, automatonoptions : OptionsPattern[]]] :=
	AutomatonQ[Automaton[edges, initialstate, {}, automatonoptions]] /;
		(* This prevents $IterationLimit::itlim for  AutomatonQ[Automaton[{A}, InputAlphabet -> {0}]] . *)
 		!MatchQ[{automatonoptions}, {{}, ___}]
AutomatonQ[_] :=
	False
SyntaxInformation[AutomatonQ] = {"ArgumentsPattern" -> {_}}

(*** end AutomatonQ code ***)


(* Method extracted from Theorem 4.3.3 of Allouche & Shallit, Automatic Sequences: Theory, Applications, Generalizations. *)
(* Probably the output is always minimal.  It would be for the reversal construction: https://en.wikipedia.org/wiki/DFA_minimization#Brzozowski's_algorithm *)
AutomatonReverse[
(* xxx assumes that we don't have multiple initial states *)
	originalautomaton : Automaton[originaledges_, originalinitialstate_, ___]?AutomatonQ,
	OptionsPattern[]
] :=
Module[
	{
		inputalphabet, originalstatelist, originalstatepositionindex, originalinitialstateindex, originaltransitionrules, originaloutputrules, currentstate, letter,
		edges, statecount, state, statehashassociation, stateindex, output, newstate, newstatehash, newstateindex, starttime,
		checkstatesameness, memorystorage, directory
	},
	checkstatesameness = !TrueQ[OptionValue[HashStateNames]];
	inputalphabet = AutomatonInputAlphabet[originalautomaton];
(* TODO Don't I need to check  !MatchQ[inputalphabet, _AutomatonInputAlphabet] ? *)
	originalstatelist = AutomatonStateList[originalautomaton];
(* xxx old
	originalstatepositionindex = Thread[originalstatelist -> Range[Length[originalstatelist]]];
*)
	originalstatepositionindex = First /@ PositionIndex[originalstatelist];
	originalinitialstateindex = originalstatepositionindex[originalinitialstate];
	originaltransitionrules = Append[
		Replace[
			originaledges,
			{instate_ -> outstate_, label_} :> ({instate, label} -> outstate),
			{1}
		],
		_ -> $Failed
	];
	originaloutputrules = AutomatonOutputRules[originalautomaton];
	statecount = 1;
	newstate = Replace[originalstatelist, originaloutputrules, {1}];
	memorystorage = Replace[OptionValue[StateStorage],
		{
			"Disk" | {"Disk", ___, "Directory" -> Automatic, ___} :> (
				directory = $TemporaryDirectory;
				False
			),
		 	{"Disk", ___, "Directory" -> dir_, ___} :> (
				directory = dir;
				False
			),
			"Memory" ->
				True,
			_ ->
				False
		}
	];
	If[memorystorage,
		state[statecount] = newstate,
		Export[FileNameJoin[{directory, ToString[statecount] <> ".m"}], newstate]
	];
	statehashassociation = Association[];
	statehashassociation[Hash[newstate]] = statecount;
	output = Association[];
	output[statecount] = newstate[[originalinitialstateindex]];
	stateindex = 1;
	starttime = DateObject[];
	If[TrueQ[OptionValue[Monitor]] && 10 < $VersionNumber < 11,
		Message[Monitor::abort]
	];
	edges = Join @@ Reap[
		If[TrueQ[OptionValue[Monitor]] && !(10 < $VersionNumber < 11), Monitor, List][
			While[stateindex <= statecount,
				currentstate = If[memorystorage,
					state[stateindex],
					Import[FileNameJoin[{directory, ToString[stateindex] <> ".m"}]]
				];
				Sow[
					Table[
						newstate = currentstate[[
							Lookup[
								originalstatepositionindex,
(* xxx if the original automaton isn't complete, then we'll get $Failed sometimes under transitions; test for completeness? *)
								Function[s, Replace[{s, letter}, originaltransitionrules]] /@ originalstatelist
							]
						]];
						newstatehash = Hash[newstate];
						newstateindex = statehashassociation[newstatehash];
						If[
							And[
								checkstatesameness,
								!MissingQ[newstateindex],
								If[memorystorage,
									state[newstateindex],
									Import[FileNameJoin[{directory, ToString[newstateindex] <> ".m"}]]
								] =!= newstate
							]
							,
(* xxx this isn't really ideal; should be able to recover by checking the full states.  but then we lose speed, since the association needs distinct keys *)
							Message[AutomatonReverse::hash, newstatehash];
							newstateindex = Missing["NotFound"]
						];
						{
							stateindex -> If[MissingQ[newstateindex],
								statecount++;
								If[memorystorage,
									state[statecount] = newstate,
									Export[FileNameJoin[{directory, ToString[statecount] <> ".m"}], newstate]
								];
								statehashassociation[newstatehash] = statecount;
								output[statecount] = newstate[[originalinitialstateindex]];
								statecount
								,
								newstateindex
							],
							letter
						}
						,
						{letter, inputalphabet}
					]
				];
				If[!checkstatesameness,
					If[memorystorage,
						Unset[state[stateindex]],
						DeleteFile[FileNameJoin[{directory, ToString[stateindex] <> ".m"}]]
					]
				];
				stateindex++
			],
			Column[{
				Row[{"Processing state ", stateindex, " of ", statecount}],
				ProgressIndicator[(stateindex - 1)/statecount],
				If[stateindex == 1,
					Row[{}],
					Row[{"Processing known states will finish at ", DatePlus[starttime, statecount/(stateindex - 1) DateDifference[starttime, DateObject[]]]}]
				]
			}]
		];
		If[checkstatesameness,
			If[memorystorage,
				(* Unsetting the states one at a time seems to be better than  Clear[state]  for avoiding a time-consuming memory spike when states have been swapped to disk. *)
				Unset[state[#]] & /@ Range[statecount, 1, -1],
				DeleteFile[FileNameJoin[{directory, ToString[#] <> ".m"}] & /@ Range[statecount]]
			]
		];
	][[2, 1]];
	Automaton[edges, 1, Normal[output]]
]
Options[AutomatonReverse] = {HashStateNames -> False, Monitor -> False, StateStorage -> "Memory"}
SyntaxInformation[AutomatonReverse] = {"ArgumentsPattern" -> {_, OptionsPattern[]}}
AutomatonReverse::hash = "Hash value `1` occurs for two distinct states; resulting automaton may not be correct."

(* This maybe isn't ideal because it runs AutomatonQ twice. *)
AutomatonStateCount[automaton_?AutomatonQ] :=
	Length[AutomatonStateList[automaton]]
SyntaxInformation[AutomatonStateCount] = {"ArgumentsPattern" -> {_}}

AutomatonStateList[automaton_?AutomatonQ] :=
	DeleteDuplicates[Join @@ List @@@ First /@ First[automaton]]
SyntaxInformation[AutomatonStateList] = {"ArgumentsPattern" -> {_}}

SetAttributes[BaumSweet, Listable]
BaumSweet[n_Integer?NonNegative] :=
	Boole[And @@ EvenQ /@ Cases[Split[DigitList[n, 2]], zeroblock : {0, ___} :> Length[zeroblock]]]
SyntaxInformation[BaumSweet] = {"ArgumentsPattern" -> {_}}

Cartier[polynomial_, variables_List, modulus_Integer?Positive, residues : {__Integer}] /;
		And[
			PolynomialQ[polynomial, variables],
			Length[variables] == Length[residues]
		] :=
	FromCoefficientRules[
		MapAt[Quotient[#, modulus] &, 1] /@
		Select[
			(* To support Laurent polynomials, I could use  GeneralCoefficientRules[Expand[polynomial], variables]  here.
			   In that case I might be able to allow {} as the variables list; currently this is prevented by
			   CoefficientRules[x, {}]  evaluating to  {{1} -> 1}  rather than  {{} -> x} . *)
			CoefficientRules[polynomial, variables],
			And @@ Divisible[First[#] - residues, modulus] &
		],
		variables
	]
Cartier[polynomial_, x : Except[_List], modulus_Integer?Positive, residue_Integer] :=
	Cartier[polynomial, {x}, modulus, {residue}]
SyntaxInformation[Cartier] = {"ArgumentsPattern" -> {_, _, _, _}}

CauchyProduct[list1_List, list2_List] /; Length[list1] == Length[list2] :=
	Table[Take[list1, i] . Reverse[Take[list2, i]], {i, Length[list1]}]
SyntaxInformation[CauchyProduct] = {"ArgumentsPattern" -> {_, _}}

(* TODO This doesn't use the output rules of the automaton, if present. *)
(* TODO Support edge patterns? *)
(* Multidimensional version? *)
(* With the Modulus option set, the output is a polynomial which is congruent to  0  when  y^i  is replaced with  f(x^i) .
	Probably the only useful settings for Modulus are  0  and powers of  p . *)
ChristolPolynomial[automaton_?AutomatonQ, {x_, y_}, OptionsPattern[]] :=
Module[{initialstate = automaton[[2]], inputalphabet, p, modulus, kernelrelationships, statecount, rules, lastrow, f, z, failed},
	failed = Catch[
		inputalphabet = AutomatonInputAlphabet[automaton];
		If[
			!And[
				MatchQ[inputalphabet, {__Integer}],
				Sort[inputalphabet] === Range[0, (p = Max[inputalphabet] + 1) - 1]
			],
			Throw[True]
		];
		If[!PrimeQ[p],
			Message[ChristolPolynomial::prime, p]; Throw[True]
		];
		modulus = Replace[OptionValue[Modulus], Automatic -> p];
		If[!IntegerQ[modulus],
			Message[ChristolPolynomial::mod]; Throw[True]
		];
		kernelrelationships = Normal[GroupBy[
			Reverse[First[automaton]],
			#[[1, 1]] &,
			(#[[1, 2]] &) /@ SortBy[#, Last] &
		]];
		(* Check that the automaton is deterministic. *)
		If[Union[Length /@ Last /@ kernelrelationships] =!= {p},
			Throw[True]
		];
		statecount = Length[kernelrelationships];
(* xxx better name than rules? *)
		rules = (RuleDelayed @@ {f[First[#], z_], Total[MapIndexed[z^(#2[[1]] - 1) f[#1, z^p] &, Last[#]]]} &) /@ kernelrelationships;
(* TODO
Check that the output alphabet is {0, ..., p-1}?
If the output alphabet size is greater than p, then we'll need to do row reduction over F_q, and even now for F_p I'm not sure it's correct because it could divide by p at some intermediate step.
Should I RowReduce modulo  modulus ?  This would have an impact on the PolynomialMod later; may not need it.
Should I use NullSpace rather than RowReduce?
*)
		lastrow = Last[RowReduce[ArrayFlatten[{{
			Reverse[
				MapIndexed[
					Table[
						Coefficient[#1, f[state, x^p^First[#2]]],
						{state, First /@ kernelrelationships}
					] /. x -> x^p^(statecount + 1 - First[#2]) &,
					Collect[Rest[NestList[# /. rules &, f[initialstate, x], statecount + 1]], _f]
				]
			],
			-IdentityMatrix[statecount + 1]
		}}]]];
		If[!MatchQ[Take[lastrow, statecount], {0 ..}],
(* TODO Can this happen?  Does the identity matrix necessarily prevent it?
			Print["this can happen"]; *) Message[ChristolPolynomial::mat]
		];
		(* TODO Give Modulus to Cancel?  PolynomialLCM? *)
		(* Cancel any powers of p appearing in numerators and denominators; otherwise the output can end up being the zero polynomial. *)
		lastrow = Cancel[lastrow];
		lastrow = Drop[PolynomialMod[(PolynomialLCM @@ Denominator /@ lastrow) lastrow, modulus], statecount];
		False
	];
	lastrow.Table[y^p^i, {i, 0, statecount}] /; !failed
]
Options[ChristolPolynomial] = {Modulus -> Automatic}
SyntaxInformation[ChristolPolynomial] = {"ArgumentsPattern" -> {_, _, OptionsPattern[]}}
ChristolPolynomial::mat = "Row reduction produced an ill\[Hyphen]formed matrix; resulting polynomial may not be correct."
ChristolPolynomial::mod = "Modulus must be an integer."
ChristolPolynomial::prime = "The `1`\[Hyphen]automatic sequence must be presented as a " <> box["p"] <> "\[Hyphen]automatic sequence for prime " <> box["p"] <> "."

CompleteAutomatonQ[automaton : Automaton[edges_, __]?AutomatonQ] :=
Module[{inputalphabet = AutomatonInputAlphabet[automaton], letter},
	And @@ Function[state,
		And @@ Table[
			Count[edges, {state -> _, label_ /; MatchQ[letter, label]}] >= 1,
			{letter, inputalphabet}
		]
	] /@ AutomatonStateList[automaton] /;
		!MatchQ[inputalphabet, _AutomatonInputAlphabet] || Message[CompleteAutomatonQ::input]
]
CompleteAutomatonQ[_] :=
	False
SyntaxInformation[CompleteAutomatonQ] = {"ArgumentsPattern" -> {_}}
CompleteAutomatonQ::input = "Unable to determine the input alphabet."

ConstantTermSequence[powerpolynomial_, variables_List][n_Integer?NonNegative] :=
	ConstantTermSequence[powerpolynomial, 1, variables][n]
ConstantTermSequence[powerpolynomial_, factorpolynomial_, variables_List][n_Integer?NonNegative] /;
		LaurentPolynomialQ[powerpolynomial, variables] && LaurentPolynomialQ[factorpolynomial, variables] :=
	LaurentPolynomialCoefficient[powerpolynomial^n factorpolynomial, variables, ConstantArray[0, Length[variables]]]
ConstantTermSequence[powerpolynomial_, variable : Except[_List]][n_Integer?NonNegative] :=
	ConstantTermSequence[powerpolynomial, {variable}][n]
ConstantTermSequence[powerpolynomial_, factorpolynomial_, variable : Except[_List]][n_Integer?NonNegative] :=
	ConstantTermSequence[powerpolynomial, factorpolynomial, {variable}][n]
SyntaxInformation[ConstantTermSequence] = {"ArgumentsPattern" -> {_, _, _.}}

ConstantTermSequenceReduce[AperyNumber[n_], n_] /; PlausibleVariableQ[n] :=
	ConstantTermSequence[
		Expand[((1 + \[FormalX]) (1 + \[FormalY]) (1 + \[FormalZ]) (1 + \[FormalY] + \[FormalZ] + \[FormalY] \[FormalZ] + \[FormalX] \[FormalY] \[FormalZ]))/(\[FormalX] \[FormalY] \[FormalZ])],
		{\[FormalX], \[FormalY], \[FormalZ]}
	][n]
ConstantTermSequenceReduce[CatalanNumber[n_], n_] /; PlausibleVariableQ[n] :=
	ConstantTermSequence[
		1/\[FormalX] + 2 + \[FormalX],
		1 - \[FormalX],
		\[FormalX]
	][n]
ConstantTermSequenceReduce[MotzkinNumber[n_], n_] /; PlausibleVariableQ[n] :=
	ConstantTermSequence[
		1/\[FormalX] + 1 + \[FormalX],
		1 - \[FormalX]^2,
		\[FormalX]
	][n]
ConstantTermSequenceReduce[sequence : _ConstantTermSequence[n_], n_] /; PlausibleVariableQ[n] :=
	sequence
(* XXX Fibonacci, LucasL, JacobsthalNumber, Tribonacci, PolygonalNumber, etc.;
   ConstantRecursiveSequence, DifferenceRoot where possible, Furstenberg for algebraic sequences, DiagonalSequence *)
SyntaxInformation[ConstantTermSequenceReduce] = {"ArgumentsPattern" -> {_, _}}

DeterministicAutomatonQ[automaton : Automaton[edges_, __]?AutomatonQ] :=
Module[{inputalphabet = AutomatonInputAlphabet[automaton], letter},
	And @@ Function[state,
		And @@ Table[
			Count[edges, {state -> _, label_ /; MatchQ[letter, label]}] == 1,
			{letter, inputalphabet}
		]
	] /@ AutomatonStateList[automaton] /;
		!MatchQ[inputalphabet, _AutomatonInputAlphabet] || Message[DeterministicAutomatonQ::input]
]
DeterministicAutomatonQ[_] :=
	False
SyntaxInformation[DeterministicAutomatonQ] = {"ArgumentsPattern" -> {_}}
DeterministicAutomatonQ::input = "Unable to determine the input alphabet."

DiagonalSequence[rationalexpression_, variablepartition : {__List}, OptionsPattern[]][nsequence__Integer?NonNegative] /;
		Length[variablepartition] == Length[{nsequence}] :=
With[{modulus = OptionValue[Modulus]},
	If[modulus == 0,
		Identity,
		Expand[#, Modulus -> modulus] &
	][
		SeriesCoefficient @@ Join[
			{rationalexpression},
			Join @@ MapThread[
				Function[{variables, n}, Thread[{variables, 0, n}]],
				{
					variablepartition,
					{nsequence}
				}
			]
		]
	]
]
DiagonalSequence[rationalexpression_, variables : Except[{__List}, {Except[_List] ..}], options : OptionsPattern[]][n_Integer?NonNegative] :=
	DiagonalSequence[rationalexpression, {variables}, options][n]
DiagonalSequence[rationalexpression_, variable : Except[_List], options : OptionsPattern[]][n_Integer?NonNegative] :=
	DiagonalSequence[rationalexpression, {{variable}}, options][n]
Options[DiagonalSequence] = {Modulus -> 0}
SyntaxInformation[DiagonalSequence] = {"ArgumentsPattern" -> {_, _, OptionsPattern[]}}

DiagonalSequenceReduce[AperyNumber[n_], n_] /; PlausibleVariableQ[n] :=
	DiagonalSequence[
		1/((1 - \[FormalW] - \[FormalX]) (1 - \[FormalY] - \[FormalZ]) - \[FormalW] \[FormalX] \[FormalY] \[FormalZ]),
		{\[FormalW], \[FormalX], \[FormalY], \[FormalZ]}
	][n]
DiagonalSequenceReduce[CatalanNumber[n_], n_] /; PlausibleVariableQ[n] :=
(* unnecessarily complicated
	DiagonalSequence[
		(y + 1) (2 x y^2 + x y + x - 1)/(x y^2 + 2 x y + x - 1),
		{x, y}
	][n]
*)
	DiagonalSequence[
		(1 - \[FormalX])/(1 - (1 + \[FormalX])^2 \[FormalY]),
		{\[FormalX], \[FormalY]}
	][n]
DiagonalSequenceReduce[MotzkinNumber[n_], n_] /; PlausibleVariableQ[n] :=
(* unnecessarily complicated
	DiagonalSequence[
		(-1 + x - y + x y + x^2 y + x y^2 + 2 x^2 y^2 + 3 x^2 y^3 + 2 x^2 y^4)/(-1 + x + x y + x^2 y + 2 x^2 y^2 + x^2 y^3),
		{x, y}
	][n]
*)
	DiagonalSequence[
		(1 - \[FormalX]^2)/(1 - (1 + \[FormalX] + \[FormalX]^2) \[FormalY]),
		{\[FormalX], \[FormalY]}
	][n]
(* Furstenberg *)
DiagonalSequenceReduce[
(* xxx allow a general series center x0? *)
	(sequence : AlgebraicSequence[
		seriesroot : SeriesRoot[{polynomialfunction_Function, root : HoldPattern[SeriesData][x_, x0 : 0, __]}, OptionsPattern[]],
		OptionsPattern[]
	]?SeriesRootAlgebraicSequenceObjectQ)[n_],
	n_?PlausibleVariableQ
] :=
Module[{modulus, polynomial, rootdata, shiftedseriesroot, initialterms, shiftlength, shiftedpolynomial, y, failed},
	failed = Catch[
		modulus = SeriesRootAlgebraicSequenceModulus[sequence];
		polynomial = polynomialfunction[y];
		y = SelectFirst[
			RotateRight[Symbol /@ CharacterRange["\[FormalA]", "\[FormalZ]"], 2],
			FreeQ[polynomial, #] &,
(* xxx this exposes y... need to choose a symbol that isn't already in  polynomial .  one nice thing about AlgebraicSequence not using a Function was that i could just reuse the same variables
   should it take GeneratedParameters or something?  what does DifferenceRoot do if there's a conflict? *)
			y
		];
(* TODO Don't append if there's already a Modulus option. *)
		rootdata = ImplicitFunctionTheoremRoot[Append[seriesroot, Modulus -> modulus]];
		If[MatchQ[rootdata, _ImplicitFunctionTheoremRoot],
			Message[DiagonalSequenceReduce::soln, polynomialfunction, root]; Throw[True]
		];
		{shiftedseriesroot, initialterms, shiftlength} = rootdata;
(* e.g.
{SeriesRoot[
  Function[\[FormalY], -2 \[FormalY] - \[FormalY]^2 + 12 x + 
    16 \[FormalY] x + 6 \[FormalY]^2 x - 16 x^2 - 24 \[FormalY] x^2 - 
    8 \[FormalY]^2 x^2 + 16 x^3 + 16 \[FormalY] x^3 + 
    4 \[FormalY]^2 x^3], x], 1 + x + 2 x^2, 3}
*)
		shiftedpolynomial = First[shiftedseriesroot][y];
		False
	];
	If[modulus == 0,
		DiagonalSequence[
			Plus[
				initialterms /. x -> x y,
				(x y)^Max[shiftlength - 1, 0] y (D[shiftedpolynomial, y] /. x -> x y) / Cancel[(shiftedpolynomial /. x -> x y)/y]
			],
			{x, y}
		],
		DiagonalSequence[
			Plus[
				initialterms /. x -> x y,
(* PolynomialMod expands; should I reduce coefficients in less aggressive way that doesn't lose factorization info? *)
				(x y)^Max[shiftlength - 1, 0] y PolynomialMod[D[shiftedpolynomial, y] /. x -> x y, modulus] / PolynomialMod[(shiftedpolynomial /. x -> x y)/y, modulus]
			],
			{x, y},
			Modulus -> modulus
		]
	][n] /; !failed
(*
(* xxx do i need this? if so why does the input allow a SeriesRoot object? *)
(* This condition implies there's a unique power series root with constant term 0
   If we can subtract initial terms to get into that situation, we can use Furstenberg and then add on the terms to the ratianal expression.
   The problem is that we don't know how many terms we'll need to subtract.  Well we could use the terms provided in  root . *)
		ImplicitFunctionTheoremPolynomialQ[polynomial, x, y]
*)
(* xxx this condition has a modulus in it; what's it doing here?  maybe only need this when working mod p?
		And[
			Divisible[Coefficient[polynomial /. x -> 0, y, 0], modulus],
			GCD[Coefficient[polynomial /. x -> 0, y, 1], modulus] == 1
		]
*)
]
DiagonalSequenceReduce[
	s : AlgebraicSequence[_Function, Except[_Rule], OptionsPattern[]][n_],
	n_?PlausibleVariableQ
] :=
With[{sequence = AlgebraicSequenceReduce[s, n]},
	DiagonalSequenceReduce[sequence, n] /; !MatchQ[sequence, _AlgebraicSequenceReduce]
]
DiagonalSequenceReduce[
(* xxx check Laurent polynomial-ness *)
	ConstantTermSequence[powerpolynomial_, factorpolynomial_, variables_List][n_],
	n_?PlausibleVariableQ
] :=
Module[{y},
	y = SelectFirst[
		RotateRight[Symbol /@ CharacterRange["\[FormalA]", "\[FormalZ]"], 2],
		FreeQ[{powerpolynomial, factorpolynomial}, #] &,
(* xxx this exposes y...
   should it take GeneratedParameters or something?  what does DifferenceRoot do if there's a conflict? *)
		y
	];
	DiagonalSequence[
(* xxx top and bottom might not be polynomials; simplify or something? *)
		factorpolynomial / (1 - powerpolynomial Times @@ variables y),
		Append[variables, y]
	][n]
]
DiagonalSequenceReduce[
	ConstantTermSequence[powerpolynomial_, variables_][n_],
	n_
] :=
	DiagonalSequenceReduce[ConstantTermSequence[powerpolynomial, 1, variables][n], n]
DiagonalSequenceReduce[
	ConstantTermSequence[powerpolynomial_, factorpolynomial_, variable : Except[_List]][n_],
	n_
] :=
	DiagonalSequenceReduce[ConstantTermSequence[powerpolynomial, factorpolynomial, {variable}][n], n]
DiagonalSequenceReduce[sequence : _DiagonalSequence[n_], n_] /; PlausibleVariableQ[n] :=
	sequence
(* XXX Fibonacci, LucasL, JacobsthalNumber, Tribonacci, PolygonalNumber, etc.;
   ConstantRecursiveSequence, DifferenceRoot where possible *)
SyntaxInformation[DiagonalSequenceReduce] = {"ArgumentsPattern" -> {_, _, OptionsPattern[]}}
(* older
DiagonalSequenceReduce::soln = "Unable to obtain a polynomial for `1` satisfying the conditions of implicit function theorem."
*)
(* Should this message also indicate that there may be no roots? *)
DiagonalSequenceReduce::soln = "Polynomial function `1` has multiple roots near `2`. Specify more terms."

SetAttributes[DigitGet, Listable]
DigitGet[n_Integer, numerationsystem_, position_Integer?NonNegative] :=
With[{digitlist = DigitList[n, numerationsystem, position + 1]},
	Last[digitlist] /; !MatchQ[digitlist, _DigitList]
]
SyntaxInformation[DigitGet] = {"ArgumentsPattern" -> {_, _, _}}

DigitList[0, base_Integer : 10] /; base >= 2 =
	{}
DigitList[n_Integer?Positive, base_Integer : 10] /; base >= 2 :=
	Reverse[IntegerDigits[n, base]]
DigitList[n_Integer?NonNegative, base_Integer /; base >= 2, length_Integer?NonNegative] :=
	Reverse[IntegerDigits[n, base, length]]
DigitList[n_Integer?Negative, base_Integer /; base >= 2, length_Integer?NonNegative] :=
	Reverse[IntegerDigits[Ceiling[-n, base^length] + n, base, length]]
(* When the third argument is a small integer, these are inefficient in that they compute the full representation and then truncate. *)
DigitList[n_Integer, base_Integer /; base <= -2, length : (_Integer?NonNegative | Automatic) : Automatic] :=
	PadRight[
		Mod[Most[NestWhileList[(# - Mod[#, -base])/base &, n, # != 0 &]], -base],
		length
	]
(* Mixed base. *)
(* TODO Does it really make sense to allow 1 as a base in mixed radix? *)
DigitList[0, {__Integer?Positive}] :=
	{}
DigitList[n_Integer, baselist : {__Integer?Positive}, length : (_Integer?NonNegative | Automatic) : Automatic] :=
	PadRight[
		Reverse[IntegerDigits[n, MixedRadix[Reverse[baselist]]]],
		length
	] /; $VersionNumber >= 10.2
DigitList[
	n_Integer?NonNegative,
	numerationsystem : "Fibonacci" | "Tribonacci" | _?LinearNumerationSystemQ,
	length : (_Integer?NonNegative | Automatic) : Automatic
] :=
	PadRight[
		GreedyPartitionDigitList[n, NumerationSystemBasisFunction[numerationsystem]],
		length
	]
(* This version seems to be faster than using GreedyPartitionDigitList. *)
DigitList[n_Integer?NonNegative, "Factorial", length : (_Integer?NonNegative | Automatic) : Automatic] :=
Module[{a = 2, b = 1},
	PadRight[
		Mod[#, a++] & /@
			Most[NestWhileList[(# - Mod[#, ++b])/b &, n, # != 0 &]],
		length
	]
]
SyntaxInformation[DigitList] = {"ArgumentsPattern" -> {_, _., _.}}

DigitsCount[n_Integer?NonNegative, base_Integer /; base >= 2, digit_Integer, options : OptionsPattern[]] :=
	DigitsCount[n, base, {digit}, options]
DigitsCount[n_Integer?NonNegative, base_Integer /; base >= 2, digits : {__Integer}, OptionsPattern[]] :=
Module[{digitlist = DigitList[n, base]},
	If[TrueQ[OptionValue[LeadingZeros]],
		(* This convention doesn't make perfect sense, but it's useful. *)
		digitlist = Join[digitlist, ConstantArray[0, Length[digits] - 1]]
	];
	SequenceCount[digitlist, digits, Overlaps -> True]
]
Options[DigitsCount] = {LeadingZeros -> False}
SyntaxInformation[DigitsCount] = {"ArgumentsPattern" -> {_, _, _, OptionsPattern[]}}

ExponentialFit[data : {{_, Except[0 | 0.]} ..}, variable_] :=
Module[{x},
	Times @@ (Exp[CoefficientList[Fit[MapAt[Log, 2] /@ data, {1, x}, x], x, 2]]^{1, x}) /. x -> variable
]
ExponentialFit[data : {___?NumericQ}, variable_, offset_ : 1] :=
	ExponentialFit[Transpose[{Range[offset, offset + Length[data] - 1], data}], variable]
SyntaxInformation[ExponentialFit] = {"ArgumentsPattern" -> {_, _, _.}}

FactorForm[n : _Integer | _Rational | Complex[_Integer | _Rational, _Integer | _Rational]] :=
Interpretation[
	Replace[
		Replace[
			FactorInteger[n],
			{{p_, 1} :> p, {p_, a_} :> Superscript[p, a]},
			{1}
		],
		{{primepower_} :> primepower, composite_ :> Row[composite, "\[Times]"]}
	],
	n
]
FactorForm[expr_] :=
	expr /.
		n : _Integer | _Rational | Complex[_Integer | _Rational, _Integer | _Rational] :>
			FactorForm[n]
SyntaxInformation[FactorForm] = {"ArgumentsPattern" -> {_}}

(* TODO could probably combine the two cases *)
FactorGrid[
	list : {(_Integer | _Rational) ...},
	zero_ : Null
] :=
Module[{factors = Complement[First /@ Flatten[FactorInteger[list], 1], Range[-1, 1]]},
	Grid[
		Prepend[
			MapThread[Prepend, {
				(RationalExponent[#, factors] & /@ list) /. 0 -> zero,
				Replace[
					list,
					n_Integer d_. | Rational[n_, d_] :>
						Divide @@ Function[x, If[IntegerLength[x] <= 18,
							x,
							Interpretation[
								Row[ReplacePart[
									Riffle[StringJoin /@
										MapAt[
											# /. {Longest[0 ...], a__} :> {If[x >= 0, "", "-"], a} &,
											Drop[Partition[PadLeft[
												ToString /@ IntegerDigits[x],
												Ceiling[IntegerLength[x], 3]
											], 3], {4, -4}],
											1
										],
										Spacer[2]
									],
									6 -> "\[CenterEllipsis]"
									]
								],
								x
							]
						]] /@ {n, d},
					{1}
				]
			}],
			Prepend[factors, Null]
		],
		Alignment -> Right,
		Dividers -> {{False, True}, {False, True}},
		ItemSize -> Full
	]
]
FactorGrid[
	list : {(
		_Integer |
		_Rational |
		Complex[_Integer | _Rational, _Integer | _Rational]
	) ...},
	zero_ : Null
] :=
Module[{factorlist, factors},
	factorlist = FactorInteger[list, GaussianIntegers -> True] /.
		{0 | 1 | I | -1 | -I, _} -> Sequence[];
	factors = SortBy[Union @@ Map[First, factorlist, {2}], Abs];
	Grid[
		Prepend[
			MapThread[
				Prepend,
				{
					Replace[factors, Append[Rule @@@ #, _ -> zero], {1}] & /@ factorlist,
					list
				}
			],
			Prepend[factors, Null]
		],
		Alignment -> Right,
		Dividers -> {{False, True}, {False, True}},
		ItemSize -> Full
	]
]
SyntaxInformation[FactorGrid] = {"ArgumentsPattern" -> {_, _.}}

FindAutomaticSequenceAutomaton[
	array_,
	numerationsystem_,
	options : OptionsPattern[]
] :=
With[{automaticsequence = FindAutomaticSequenceFunction[array, numerationsystem, options]},
	First[automaticsequence] /; !MatchQ[automaticsequence, _FindAutomaticSequenceFunction]
]
Options[FindAutomaticSequenceAutomaton] = {FlattenInputAlphabet -> True, IndexedStateNames -> True, Monitor -> False}
SyntaxInformation[FindAutomaticSequenceAutomaton] = {"ArgumentsPattern" -> {{__}, _, OptionsPattern[]}}

FindAutomaticSequenceFunction[
	array_,
	numerationsystem_?PositiveNumerationSystemQ,
	options : OptionsPattern[]
] :=
	FindAutomaticSequenceFunction[array, ConstantArray[numerationsystem, ArrayDepth[array]], options]
FindAutomaticSequenceFunction[
	array_List,
	numerationsystemlist : {__?PositiveNumerationSystemQ},
	OptionsPattern[]
] /;
	Length[numerationsystemlist] <= ArrayDepth[array] :=
Module[{dimension, relations, basissequences, redundantsequencechains, initialconditions, edges, newbasissequence, numerationsystem, automaton, failed},
	failed = Catch[
(* xxx This shouldn't be a concern anymore.
If[MemberQ[numerationsystemlist, Except[_Integer]],
	Print[Style["RELATIONS INVOLVING PREFIXES THAT AREN'T EXTENDABLE BY THE SAME WORDS MAY NOT BE CORRECT", Red]]
];
*)
		dimension = Length[numerationsystemlist];
		{relations, basissequences, redundantsequencechains} =
			FindSequenceRelations[array, numerationsystemlist, "AutomaticSequence", Monitor -> OptionValue[Monitor]];
		If[relations === $Failed,
			Throw[True]
		];
		initialconditions =
			# -> array[[Sequence @@ (MapThread[FromDigitList, {#, numerationsystemlist}] + 1)]] & /@ Join[
				basissequences,
				Last /@ redundantsequencechains
			];
		edges = Join[
			Join @@ Function[basissequence,
				Function[subsequence,
					newbasissequence = Replace[subsequence, relations];
					(* In general numeration systems there are kernel sequences with multiple represenations (e.g. {{1}} and {{1, 0}} in Fibonacci).
					   We need separate states for each of these representations, because they don't have the same out-edges.
					   (For example, the 0 edge from {{1}} must go to {{1, 0}}, but the 0 edge from {{1, 0}} isn't necessarily a loop.
					   So we don't draw an edge labeled 0 to a state ending in 1 (because from such states it's only valid to read 0 next);
					   instead it goes to the unique child of that state (which ends in 0).) *)
					If[
						Or @@ MapThread[
							Function[{subsequenceprefix, endprefix, numsystem},
								Or[
									numsystem === "Fibonacci" && MatchQ[subsequenceprefix, {___, 0}] && MatchQ[endprefix, {___, 1}],
									numsystem === "Tribonacci" && MatchQ[subsequenceprefix, {___, 0}] && MatchQ[endprefix, {___, 1, 1}]
								]
							],
							{
								subsequence,
								newbasissequence,
								numerationsystemlist
							}
						],
(*
(* xxx what if this isn't a sequence we know about (meaning we don't know its out-edges or its output value)? *)
Print[(Append[#, 0] &) /@ newbasissequence];
*)
						newbasissequence = (Append[#, 0] &) /@ newbasissequence
					];
					{basissequence -> newbasissequence, Last /@ subsequence}
				] /@
					ArithmeticSubsequences[basissequence, numerationsystemlist]
			] /@
				Replace[
					basissequences,
					redundantsequencechains,
					{1}
				],
			Function[redundantsequencechain,
				{redundantsequencechain, Last /@ Last[redundantsequencechain]}
			] /@ redundantsequencechains
		];
		If[TrueQ[OptionValue[FlattenInputAlphabet]] && dimension == 1,
			edges = MapAt[First, 2] /@ edges;
			numerationsystem = First[numerationsystemlist]
			,
			numerationsystem = numerationsystemlist
		];
		automaton = Automaton[
			edges,
			ConstantArray[{}, dimension],
			initialconditions
		];
		If[TrueQ[OptionValue[IndexedStateNames]],
			automaton = IndexAutomaton[automaton]
		];
		False
	];
	AutomaticSequence[automaton, numerationsystem] /; !failed
]
FindAutomaticSequenceFunction[
	array_,
	numerationsystem_,
	n_,
	options : OptionsPattern[]
] :=
With[{automaticsequence = FindAutomaticSequenceFunction[array, numerationsystem, options]},
	automaticsequence[n] /; !MatchQ[automaticsequence, _FindAutomaticSequenceFunction]
]
Options[FindAutomaticSequenceFunction] = {FlattenInputAlphabet -> True, IndexedStateNames -> True, Monitor -> False}
SyntaxInformation[FindAutomaticSequenceFunction] = {"ArgumentsPattern" -> {{__}, _, _., OptionsPattern[]}}

FindAutomaticSequenceRecurrence[
	array_,
	numerationsystem_?PositiveNumerationSystemQ,
	symbol : Except[Rule][__],
	options : OptionsPattern[]
] :=
	FindAutomaticSequenceRecurrence[array, ConstantArray[numerationsystem, Length[symbol]], symbol, options]
FindAutomaticSequenceRecurrence[
	array_List,
	numerationsystemlist : {__?PositiveNumerationSystemQ},
	symbol : (a : Except[Rule])[__?PlausibleVariableQ],
	OptionsPattern[]
] /;
	Length[numerationsystemlist] == Length[symbol] <= ArrayDepth[array] :=
Module[{dimension, relations, basissequences, initialconditions, failed, head},
	failed = Catch[
		dimension = Length[numerationsystemlist];
		{relations, basissequences} =
			(* We don't need the  redundantsequencechains  since they are implied by the recurrence we output. *)
			Most[FindSequenceRelations[array, numerationsystemlist, "AutomaticSequence", Monitor -> OptionValue[Monitor]]];
		If[relations === $Failed,
			Throw[True]
		];
		initialconditions = DeleteDuplicates[
			(* Apply symbolic  head  instead of the actual head  a  because otherwise
			   down values for  a  can prevent  SymbolicSubsequence[ ]  from evaluating. *)
			Equal[
				SymbolicSubsequence[#, numerationsystemlist, head @@ ConstantArray[0, dimension]],
				array[[Sequence @@ (MapThread[FromDigitList, {#, numerationsystemlist}] + 1)]]
			] & /@
				basissequences
		];
		relations = Equal @@@ Map[
			SymbolicSubsequence[#, numerationsystemlist, symbol] &,
			relations,
			{2}
		];
		False
	];
	(Switch[OptionValue["Output"],
		"Full" | Full,
			Join[relations, initialconditions],
(*
		"Uniform",
			Join[
				(* TODO *) relations,
				DeleteDuplicates[initialconditions]
			],
*)
		"Condensed" | _,
			KeyValueMap[
(* rename rightside? *)
				Function[{rightside, class},
(* I think I don't actually like this convention.
					Equal @@ Switch[rightside,
						_a, Prepend[class, rightside],
						_, Append[class, rightside]
					]
*)
					Equal @@ Append[class, rightside]
				],
				GroupBy[Join[relations, initialconditions], Last -> First]
			]
	] /. head -> a) /; !failed
]
Options[FindAutomaticSequenceRecurrence] = {"Output" -> Automatic, Monitor -> False}
SyntaxInformation[FindAutomaticSequenceRecurrence] = {"ArgumentsPattern" -> {{__}, _, _, OptionsPattern[]}}

FindPolynomialCoefficientList[data_, offset_] :=
Module[{var},
	CoefficientList[
		(* This If statement results in a measurable speed increase when the offset is 1. *)
		If[offset === 1,
			InterpolatingPolynomial[data, var],
			InterpolatingPolynomial[Transpose[{Range[offset, offset + Length[data] - 1], data}], var]
		],
		var,
		Length[data]
	]
]
FindPolynomialCoefficientList[data_, offsets_, f_] :=
With[{depth = Length[offsets]},
	Fold[
		Function[{array, offsetandpermutation},
			Replace[
(* xxx I might only need to unpad at the bottom level.  But is that any faster?  *)
(* Actually, is it wrong if I unpad at higher levels? *)
				UnpadRight[Map[f[FindPolynomialCoefficientList[#, offsetandpermutation[[1]]]] &, array, {depth - 1}]],
				{
					{} -> {},
					unpaddedarray_ :> Transpose[unpaddedarray, offsetandpermutation[[2]]]
				}
			]
		],
		data,
		Transpose[{
			Reverse[offsets],
			Append[
				TwoWayRule[#, depth] & /@ Range[depth - 1, 1, -1],
				RotateLeft[Range[depth]]
			]
		}]
	]
]

(* PolynomialCoefficientMod is in another package.
FindPolynomial[data_List /; ArrayDepth[data] == 1, var_, Modulus -> k_ /; Positive[k] && !PrimeQ[k]] :=
	PolynomialCoefficientMod[FindPolynomial[data, var], var, k]
*)
(* TODO Should these accept a Modulus option? *)
(* xxx Do I need a separate down value for this? *)
(* First argument is a 1-dimensional array. *)
FindPolynomial[data_List /; ArrayDepth[data] == 1, var : Except[_List], offset : Except[_Rule] : 1, OptionsPattern[]] :=
With[
	{f = Replace[
		OptionValue[IntermediateFunction],
		{
			Automatic -> (Expand[#, var] &),
			None -> Identity
		}
	]},
	f[InterpolatingPolynomial[data, var] /. var -> var - offset + 1]
]
(* First argument is a higher-dimensional array. *)
FindPolynomial[data_List, vars_List, offsets_List, OptionsPattern[]] /; ArrayDepth[data] == Length[vars] == Length[offsets] :=
Module[{f, g},
	{f, g} = Replace[
		OptionValue[IntermediateFunction],
		{
			Automatic -> {
				With[{symbolicvariables = Alternatives @@ Variables[data]},
					Expand[#, symbolicvariables] &
				],
				Expand[#, Alternatives @@ vars] &
			},
			None -> {Identity, Identity},
			h_ :> {h, h}
		}
	];
	g[FromCoefficientList[FindPolynomialCoefficientList[data, offsets, f], vars]]
]
FindPolynomial[data_List, vars_List, options : OptionsPattern[]] /; ArrayDepth[data] == Length[vars] :=
	FindPolynomial[data, vars, ConstantArray[1, Length[vars]], options]
Options[FindPolynomial] = {IntermediateFunction -> Automatic}
SyntaxInformation[FindPolynomial] = {"ArgumentsPattern" -> {{__}, _, _., OptionsPattern[]}}

FindQuasiPolynomial[data_List, var_, modulus_Integer?Positive, offset : Except[_Rule] : 1(*, OptionsPattern[]*)] :=
Module[{piecewise, x(*, k = OptionValue[Modulus]*)},
	piecewise = SequenceRiffle[
		FindPolynomial[#, x] & /@ Unriffle[data, modulus],
		x
	] /. x -> var - offset + 1;
	Replace[
		piecewise,
		HoldPattern[Piecewise][cases : {{_, _} ..}, val_ : 0] :>
			Piecewise[
				(MapAcross[
(* TODO Instead of Expand this used DiscreteRefine, which is in another package now!
   So for now I've disabled the Modulus option.
					{
						(* Passing Modulus to InterpolatingPolynomial directly does not work for nonprime moduli.
						   Plus, this way we take advantage of DiscreteRefine simplification for nonprime moduli. *)
						Switch[k,
							0, Identity,
							_, DiscreteRefine[Mod[#, k], var] &
						],
						DiscreteRefine[#, var] &
					},
*)
					{Expand, Identity},
					#
				] &) /@ cases,
				val
			]
	]
]
(*
Options[FindQuasiPolynomial] = {Modulus -> 0}
*)
SyntaxInformation[FindQuasiPolynomial] = {"ArgumentsPattern" -> {{__}, _, _, _.(*, OptionsPattern[]*)}}

FindRegularSequenceFunction[
	array_,
	numerationsystem_?PositiveNumerationSystemQ,
	options : OptionsPattern[]
] :=
	FindRegularSequenceFunction[array, ConstantArray[numerationsystem, ArrayDepth[array]], options]
FindRegularSequenceFunction[
	array_List,
	numerationsystemlist : {__?PositiveNumerationSystemQ},
	OptionsPattern[]
] /;
	And[
		Length[numerationsystemlist] <= ArrayDepth[array],
		(* Check that the array contains no lists on the bottom level, since RowReduce would complain.
		   We don't need such a check for FindAutomaticSequence* because the output can be anything. *)
		!MemberQ[array, _List, {Length[numerationsystemlist]}]
	] :=
Module[{relations, basissequences, redundantsequencechains, basissequencecount, failed},
	failed = Catch[
(* xxx This shouldn't be a concern anymore.
If[MemberQ[numerationsystemlist, Except[_Integer]],
	Print[Style["RELATIONS INVOLVING PREFIXES THAT AREN'T EXTENDABLE BY THE SAME WORDS MAY NOT BE CORRECT", Red]]
];
*)
		If[MemberQ[array, _DirectedInfinity, {Length[numerationsystemlist]}],
			Message[FindRegularSequenceFunction::inf]; Throw[True]
		];
(* xxx Do I need to use  redundantsequencechains ? *)
		{relations, basissequences, redundantsequencechains} =
			FindSequenceRelations[array, numerationsystemlist, "RegularSequence", Monitor -> OptionValue[Monitor]];
		If[relations === $Failed,
			Throw[True]
		];
		basissequencecount = Length[basissequences];
		relations = Join[
			MapIndexed[#1 -> UnitVector[basissequencecount, First[#2]] &, basissequences],
			relations
		];
(*
If[TrueQ[OptionValue[Monitor]],
	Print["appended relations: ", Multicolumn[MapAt[Row /@ # &, #, 1] & /@ relations, 4]]
];
*)
		False
	];
	RegularSequence[
		If[basissequencecount == 0,
			{},
			UnitVector[basissequencecount, 1]
		],
		(* Use Normal[SparseArray[{..., positioni -> matrixrowi, ...}]] for this whole array? *)
		Outer[
			Function[basissequence,
				Replace[
(* XXX This is extending prefixes.  But how does it deal with the fact that not all representations are valid in e.g. base Tribonacci?
We probably need to use the redundantsequencechains.
Probably need to add extra basis sequences like we did for FindAutomaticSequenceFunction. *)
					MapThread[Append, {basissequence, {##}}],
					Append[
						relations,
						(* xxx I shouldn't need this eventually, but now it indicates problems, at least in 10.1 with the abort weirdness or something *)
						_ -> $Failed
					]
				]
			] /@ basissequences &,
			Sequence @@ NumerationSystemDigitList /@ numerationsystemlist
		],
		array[[Sequence @@ (MapThread[FromDigitList, {#, numerationsystemlist}] + 1)]] & /@ basissequences,
		Replace[numerationsystemlist, {numerationsystem_} :> numerationsystem]
	] /; !failed
]
FindRegularSequenceFunction[
	array_,
	numerationsystem_,
	n_,
	options : OptionsPattern[]
] :=
With[{regularsequence = FindRegularSequenceFunction[array, numerationsystem, options]},
	regularsequence[n] /; !MatchQ[regularsequence, _FindRegularSequenceFunction]
]
Options[FindRegularSequenceFunction] = {Monitor -> False}
SyntaxInformation[FindRegularSequenceFunction] = {"ArgumentsPattern" -> {{__}, _, _., OptionsPattern[]}}

FindRegularSequenceRecurrence[
	array_,
	numerationsystem_?PositiveNumerationSystemQ,
	symbol : Except[Rule][__],
	options : OptionsPattern[]
] :=
	FindRegularSequenceRecurrence[array, ConstantArray[numerationsystem, Length[symbol]], symbol, options]
FindRegularSequenceRecurrence[
	array_List,
	numerationsystemlist : {__?PositiveNumerationSystemQ},
	symbol : (a : Except[Rule])[__?PlausibleVariableQ],
	OptionsPattern[]
] /;
	And[
		Length[numerationsystemlist] == Length[symbol] <= ArrayDepth[array],
		(* Check that the array contains no lists on the bottom level, since RowReduce would complain.
		   We don't need such a check for FindAutomaticSequence* because the output can be anything. *)
		!MemberQ[array, _List, {Length[numerationsystemlist]}]
	] :=
Module[{dimension, relations, basissequences, initialconditions, failed, head},
	failed = Catch[
		If[MemberQ[array, _DirectedInfinity, {Length[numerationsystemlist]}],
			Message[FindRegularSequenceRecurrence::inf]; Throw[True]
		];
		dimension = Length[numerationsystemlist];
		{relations, basissequences} =
			(* We don't need the  redundantsequencechains  since they are implied by the recurrence we output. *)
			Most[FindSequenceRelations[array, numerationsystemlist, "RegularSequence", Monitor -> OptionValue[Monitor]]];
		If[relations === $Failed,
			Throw[True]
		];
		initialconditions = DeleteDuplicates[
			(* Apply symbolic  head  instead of the actual head  a  because otherwise
			   down values for  a  can prevent  SymbolicSubsequence[ ]  from evaluating. *)
			Equal[
				SymbolicSubsequence[#, numerationsystemlist, head @@ ConstantArray[0, dimension]],
				array[[Sequence @@ (MapThread[FromDigitList, {#, numerationsystemlist}] + 1)]]
			] & /@
				basissequences
		];
		basissequences =
			SymbolicSubsequence[#, numerationsystemlist, symbol] & /@ basissequences;
		relations =
			SymbolicSubsequence[First[#], numerationsystemlist, symbol] == Last[#].basissequences & /@ relations;
		False
	];
	(Switch[OptionValue["Output"],
		"Full" | Full,
			Join[relations, initialconditions],
(*
		"Uniform",
			Join[
				(* TODO *) relations,
				DeleteDuplicates[initialconditions]
			],
*)
		"Condensed" | _,
			KeyValueMap[
(* rename rightside? *)
				Function[{rightside, class},
(* I think I don't actually like this convention.
					Equal @@ Switch[rightside,
						_a, Prepend[class, rightside],
						_, Append[class, rightside]
					]
*)
					Equal @@ Append[class, rightside]
				],
				GroupBy[Join[relations, initialconditions], Last -> First]
			]
	] /. head -> a) /; !failed
]
Options[FindRegularSequenceRecurrence] = {"Output" -> Automatic, Monitor -> False}
SyntaxInformation[FindRegularSequenceRecurrence] = {"ArgumentsPattern" -> {{__}, _, _, OptionsPattern[]}}

(* TODO add this to FromCoefficientList? *)
(* The offsets are for the exponents, not the variables. *)
FromCoefficientListWithOffsets[coefficientlist_List, variables_List, offsets_List] /; ArrayDepth[coefficientlist] >= Length[variables] == Length[offsets] >= 1 :=
	Total[
		coefficientlist (Outer[Times, ##] &) @@
			DiscretePower[
				variables,
				MapThread[
					Range[#2, #2 + #1 - 1] &,
					{
						Dimensions[coefficientlist, Length[variables]],
						offsets
					}
				]
			],
		Length[variables]
	]
	
FromCoefficientList[coefficientlist_List, variables_List] /; ArrayDepth[coefficientlist] >= Length[variables] >= 1 :=
	Total[
		coefficientlist (Outer[Times, ##] &) @@
			DiscretePower[
				variables,
				Range[0, # - 1] & /@ Dimensions[coefficientlist, Length[variables]]
			],
		Length[variables]
	]
FromCoefficientList[coefficientlist_List, var : Except[_List]] :=
	FromCoefficientList[coefficientlist, {var}]
FromCoefficientList[{}, _List] :=
	0
FromCoefficientList[expression_, {}] :=
	expression
SyntaxInformation[FromCoefficientList] = {"ArgumentsPattern" -> {_, _}}

(* xxx I think I don't want these first two down values.  They make sense from the dot product formula but not from the numeration system perspective.
FromDigitList[{}, 0] :=
	0
FromDigitList[digits_List, 0] :=
	First[digits]
*)
FromDigitList[digits_List, base_Integer : 10] /; Abs[base] >= 2 :=
	digits . base^Range[0, Length[digits] - 1]
FromDigitList[digits_List, numerationsystem : "Fibonacci" | "Tribonacci"] :=
	digits . Map[NumerationSystemBasisFunction[numerationsystem], Range[0, Length[digits] - 1]]
FromDigitList[digits_List, LinearNumerationSystem[kernel_, initialterms_]?LinearNumerationSystemQ] :=
	digits . LinearRecurrence[kernel, initialterms, {1, Length[digits]}]
FromDigitList[digits_List, "Factorial"] :=
	digits . Range[Length[digits]]!
(* Mixed base. *)
FromDigitList[digits_List, bases_List] /; Length[bases] + 1 >= Length[digits] :=
	PadRight[digits, Length[bases] + 1] . FoldList[Times, 1, bases]
SyntaxInformation[FromDigitList] = {"ArgumentsPattern" -> {_, _.}}

FromRecurrence[equation_Equal, s_[m_]] :=
	FromRecurrence[{equation}, s[m]]
FromRecurrence[equations : HoldPattern[And][__Equal], s_[m_]] :=
	FromRecurrence[List @@ equations, s[m]]
FromRecurrence[equationlist : {(_Equal | True) ..}, s_Symbol[m_Symbol]] /;
	And[
		PlausibleVariableQ[m],
		!MemberQ[Attributes[s], Protected]
	] :=
Module[{equations, initialconditions, recurrence, initialconditionarguments, recurrencearguments, solution, n, block, failed},
	failed = Catch[
		equations = Replace[
			DeleteCases[equationlist, True],
			equal_ /; Length[equal] >= 3 :>
				With[{constants = Select[List @@ equal, FreeQ[#, s] &]},
					If[Length[constants] == 1,
						Sequence @@ (# == First[constants] &) /@ DeleteCases[List @@ equal, First[constants]],
						Message[FromRecurrence::init]; Throw[True]
					]
				],
			{1}
		];
		initialconditions = Cases[equations, s[_Integer] == constant_ | constant_ == s[_Integer] /; FreeQ[constant, m]];
		If[initialconditions === {},
			Message[FromRecurrence::init]; Throw[True]
		];
		initialconditions = Union[Replace[initialconditions, constant : Except[_s] == term_s :> term == constant, {1}]];
		recurrence = DeleteCases[equations, Alternatives @@ initialconditions];
		If[Length[recurrence] != 1,
			Message[FromRecurrence::soln]; Throw[True]
		];
		recurrence = First[recurrence];
		initialconditionarguments = (#[[1, 1]] &) /@ initialconditions;
		(* TODO I'm not actually using most of the recurrence arguments, so internal arguments like m+.5 won't be caught. *)
		recurrencearguments = Union[Cases[recurrence, s[argument_ /; FreeQ[argument, _s] && !FreeQ[argument, m]] :> argument, Infinity]];
		solution = Solve[recurrence, s[Last[recurrencearguments]]];
		If[Length[solution] != 1,
			Message[FromRecurrence::soln]; Throw[True]
		];
		solution = First[solution];
		(* Expressions that are used in the SetDelayed need to be localized by With instead of Module. *)
		With[
			{
				order = Last[recurrencearguments] - First[recurrencearguments],
				min = First[initialconditionarguments],
				threshold = First[initialconditionarguments] + 2 (Last[recurrencearguments] - First[recurrencearguments]),
				expression = solution[[1, 2]] /. m -> n + m - Last[recurrencearguments]
			}
			,
			If[!IntegerQ[order] || initialconditionarguments =!= First[initialconditionarguments] + Range[0, order - 1],
				Message[FromRecurrence::init]; Throw[True]
			];
			Set @@@ initialconditions;
			Table[
				s[n] = expression,
				{n, Last[initialconditionarguments] + 1, Last[initialconditionarguments] + order}
			];
			SetAttributes[block, HoldAll];
			((s[Pattern[#1, _Integer] /; #1 >= min] := s[n] = #2) &)[
				n,
				block[{$RecursionLimit = Infinity},
					With[{result = expression},
						If[n >= threshold, s[n - order] =.];
						result
					]
				]
			]
		];
		DownValues[s] = DownValues[s] /. block -> Block;
		False
	];
	s /; !failed
]
FromRecurrence[equationlist : Except[{(_Equal | True) ..}, _List] /; MatchQ[Flatten[equationlist], {(_Equal | True) ..}], s_[m_]] :=
	FromRecurrence[Flatten[equationlist], s[m]]
SyntaxInformation[FromRecurrence] = {"ArgumentsPattern" -> {_, _}}
FromRecurrence::init = "Recurrence supplied with bad initial conditions."
FromRecurrence::soln = "Recurrence does not have a unique solution."

GeneratingFunctionRelations[eqn_Equal, expr_, genfun_] :=
	GeneratingFunctionRelations[{eqn}, expr, genfun]
GeneratingFunctionRelations[eqns_And, expr_, genfun_] :=
	GeneratingFunctionRelations[List @@ eqns, expr, genfun]
GeneratingFunctionRelations[
	eqns : {HoldPattern[Equal][_, _] ..},
	(a : Except[List])[v__],
	(f : Except[List])[x__]
] /; Length[{v}] == Length[{x}] :=
Module[
	{
		vars = {v}, formalvars = {x}, MySum,
		monomiallists = MonomialList /@ Subtract @@@ eqns,
		linearsystemq, lowindices, highindices, expr, shiftrules, shiftedlowindices
	},
	linearsystemq = And @@ Flatten[Map[
		MatchQ[#, c_ | c_. a @@ (_Integer | # + Optional[_Integer] &) /@ vars /; FreeQ[c, a | Alternatives @@ vars]] &,
		monomiallists,
		{2}
	]];
	Function[monomiallist,
		lowindices = (Max[Cases[monomiallist, a[___, # + shift_., ___] :> -shift, {0, Infinity}]] &) /@ vars;
		highindices = Replace[lowindices, {-Infinity -> 0, _ -> Infinity}, {1}];
		lowindices =  lowindices /. -Infinity -> 0;
		Collect[Numerator[FragileTogether[Total[
			KeyValueMap[
				Function[{label, coeff},
					expr = Replace[label, {{l_} :> l, _ -> 1}];
					shiftrules = Select[
						Thread[vars -> vars - Replace[List @@ expr - vars, Except[_Integer] -> Null, {1}]],
						FreeQ[#, Null] &
					];
					shiftedlowindices = lowindices + vars - (vars /. shiftrules);
					coeff Times @@ (formalvars^-shiftedlowindices) (
						MySum[
							Times @@ (formalvars^vars) (expr /. shiftrules),
							Sequence @@ Transpose[{
								vars,
								shiftedlowindices,
								highindices
							}]
						] //. {
							MySum[arg_, i___, {s_, l_?Positive, Infinity}, j___] :>
								MySum[arg, i, {s, 0, Infinity}, j] - MySum[arg, i, {s, 0, l - 1}, j],
							MySum[arg_, i___, {s_, l_, u_Integer}, j___] :>
								Sum[MySum[arg, i, j], {s, l, u}]
						} //. {
							MySum[arg_] :> arg,
							MySum[c_ arg_., i__] /; FreeQ[c, Alternatives @@ First /@ {i}] :> c MySum[arg, i]
						} /. {
							MySum[arg_, i__] :>
								With[{sumvars = Replace[vars, Except[Alternatives @@ First /@ {i}] -> 0, {1}]},
									If[MatchQ[arg, Times @@ (formalvars^sumvars) a @@ sumvars],
										f @@ Replace[Transpose[{formalvars, sumvars}], {{_, 0} -> 0, {y_, _} :> y}, {1}],
										MySum[arg, i]
									]
								]
						} /.
							MySum -> Sum
					)
				],
				GroupBy[
					monomiallist,
					Rule[
						Cases[#, a[__], {0, Infinity}] &,
						# /. a[__] -> 1 &
					],
					Total
				]
			]
		]]], _f] == 0
	] /@ monomiallists /; linearsystemq
]
SyntaxInformation[GeneratingFunctionRelations] = {"ArgumentsPattern" -> {_, _, _}}

(* IntegerPrepend doesn't care whether the resulting representation is a canonical representation in the numeration system; for example
   IntegerPrepend[1, "Fibonacci", {1}]
   evaluates without indicent. *)
(* IntegerPrepend doesn't check whether the digits are valid.  For positional numeration systems we don't care. *)
IntegerPrepend[n_Integer, numerationsystem_?NumerationSystemQ, prefix_List] /;
		(* This test suggests that a function testing representability in a numeration system would be useful. *)
		Or[
			NonNegative[n],
			MatchQ[numerationsystem, _Integer?Negative]
		] :=
	FromDigitList[Join[prefix, DigitList[n, numerationsystem]], numerationsystem]
(* These assume that the first argument is some symbolic representation of a non-negative integer.  *)
IntegerPrepend[n_?PlausibleVariableQ, numerationsystem_?NumerationSystemQ, {}] :=
	n
IntegerPrepend[n_?PlausibleVariableQ, base_Integer /; Abs[base] >= 2, prefix_List] :=
	(* It's tempting to use NumerationSystemBasisFunction here, but that doesn't work in general. *)
	base^Length[prefix] n + FromDigitList[prefix, base]
SyntaxInformation[IntegerPrepend] = {"ArgumentsPattern" -> {_, _, _}}

LaurentPolynomialCoefficientList[expression : Except[_List], var : Except[_List](*, exponentspec : Automatic : Automatic*)] :=
	LaurentPolynomialCoefficientList[expression, {var}]
(* This behavior is a departure from CoefficientList. *)
LaurentPolynomialCoefficientList[0, variables : {__}] :=
	Nest[List, {}, Length[variables] - 1]
LaurentPolynomialCoefficientList[expression : Except[_List], vars_List(*, exponentspec : Automatic : Automatic*)] :=
With[{exponentranges = Exponent[expression, vars, MinMax[{##}] &]},
	LaurentPolynomialCoefficientList[expression, vars, exponentranges] /;
		MatchQ[exponentranges, {{__Integer} ...}] && And @@ LessEqual @@@ exponentranges
]
LaurentPolynomialCoefficientList[expression : Except[_List], var : Except[_List], {minexponent_Integer, maxexponent_Integer} /; minexponent <= maxexponent] :=
	LaurentPolynomialCoefficientList[expression, {var}, {{minexponent, maxexponent}}]
LaurentPolynomialCoefficientList[expression_, {}, {}] :=
	expression
LaurentPolynomialCoefficientList[expression : Except[_List], vars_List, exponentranges : {{_Integer, _Integer} ..}] /;
	Length[vars] == Length[exponentranges] && And @@ LessEqual @@@ exponentranges :=
With[
	{mins = MapThread[
		Min[Exponent[expression, #1, Min], First[#2]] &,
		{vars, exponentranges}
	]},
	Drop[CoefficientList[Times @@ (vars^-mins) expression, vars, Last /@ exponentranges - mins + 1], Sequence @@ (First /@ exponentranges - mins)]
]
SyntaxInformation[LaurentPolynomialCoefficientList] = {"ArgumentsPattern" -> {_, _, _.}}

SetAttributes[JacobsthalNumber, {Listable, NumericFunction}]
JacobsthalNumber[x_?NumericQ] := (2^x - (-1)^x)/3
SyntaxInformation[JacobsthalNumber] = {"ArgumentsPattern" -> {_}}

SyntaxInformation[LinearNumerationSystem] = {"ArgumentsPattern" -> {_, _}}

(* This doesn't verify that the sequence of basis elements is increasing. *)
(* TODO Should it accept a single integer base? *)
LinearNumerationSystemQ[LinearNumerationSystem[kernel : {__Integer}, initialterms : {1, ___Integer}]] :=
	Length[kernel] == Length[initialterms]
LinearNumerationSystemQ[_] :=
	False
SyntaxInformation[LinearNumerationSystemQ] = {"ArgumentsPattern" -> {_}}

LinearRecurrenceTable[coefficients_List, initialconditions_List, nmax_Integer?NonNegative, f_ : Identity] :=
	LinearRecurrenceTable[coefficients, initialconditions, {1, nmax}, f]
LinearRecurrenceTable[coefficients_List, initialconditions_List, {nmin : (_Integer?Positive) : 1, nmax_Integer?NonNegative}, f_ : Identity] /;
	Length[coefficients] == Length[initialconditions] && nmin <= nmax :=
Module[{order = Length[coefficients], sequence},
	(* Can these cases be combined? *)
	If[nmax - nmin + 1 >= order,
		sequence = Nest[
			Append[Rest[#], f[Reverse[coefficients].Take[#, -order]]] &,
			initialconditions,
			nmin - 1
		];
		Nest[
			Append[#, f[Reverse[coefficients].Take[#, -order]]] &,
			sequence,
			nmax - nmin + 1 - order
		]
		,
		If[nmax >= order,
			sequence = Nest[
				Append[Rest[#], f[Reverse[coefficients].Take[#, -order]]] &,
				initialconditions,
				nmax - order
			];
			Take[sequence, -(nmax - nmin + 1)]
			,
			Take[initialconditions, {nmin, nmax}]
		]
	]
]
SyntaxInformation[LinearRecurrenceTable] = {"ArgumentsPattern" -> {_, _, _, _.}}

SyntaxInformation[MorphicSequence] = {"ArgumentsPattern" -> {_, _, _.}}

MorphicSequenceReduce[
(* xxx do I have to check anything about this automaton?  deterministic?  (only one initial state?)  complete?  check for unreachable states? *)
(* xxx check that if there's a second argument that AutomatonInputAlphabet[automaton] is {0, 1, ..., k - 1} ? *)
	(sequence : AutomaticSequence[automaton_?AutomatonQ, ___])[n__],
(* xxx need another downvalue where this isn't a list *)
	{n__} (* xxx use /; PlausibleVariableQ[n] *),
(* xxx this can be a list or not, too *)
	k_,
	OptionsPattern[]
] :=
Module[{numerationsystemlist, inputalphabet, (*inputalphabetindex,*) reversedautomaton, edges, initialstate, outputrules, reversedautomatonwithoutoutput},
	numerationsystemlist = AutomaticSequenceNumerationSystemList[sequence];
	If[numerationsystemlist =!= ConstantArray[k, Length[{n}]],
(* xxx message *)
		Print["bad numeration system"]
	];
(* xxx but these have an extra list around them if the input alphabet is flat *)
	inputalphabet = Tuples[NumerationSystemDigitList /@ numerationsystemlist];
(*
	inputalphabet = AutomatonInputAlphabet[automaton];
(* TODO Don't I need to check  !MatchQ[inputalphabet, _AutomatonInputAlphabet] ? *)
(* xxx if the input alphabet is always {0, 1, ..., k - 1} then we don't need this index *)
	inputalphabetindex = First /@ PositionIndex[inputalphabet];
*)
	reversedautomaton = AutomatonReverse[automaton, Monitor -> OptionValue[Monitor]];
	edges = First[reversedautomaton];
	initialstate = reversedautomaton[[2]];
	outputrules = AutomatonOutputRules[reversedautomaton];
	reversedautomatonwithoutoutput = Automaton[edges, initialstate];
	If[reversedautomatonwithoutoutput[{First[inputalphabet]}] =!= initialstate,
		(* Add a new letter on which the morphism is prolongable. *)
		initialstate = 0;
(* testprint *)
If[MemberQ[AutomatonStateList[reversedautomaton], initialstate], Print["problem!  need to use a different initial state"]];
		edges = Join[
			{{initialstate -> initialstate, First[inputalphabet]}},
(* testprint *)
If[Length[numerationsystemlist] >= 2, Print["adding a new state isn't implemented for multidimensional sequences"]];
(* xxx this isn't right for multidimensional sequences *)
(* how so? *)
			Function[letter, {initialstate -> reversedautomatonwithoutoutput[{letter}], letter}] /@ Rest[inputalphabet],
			edges
		];
		outputrules = Join[
			{initialstate -> reversedautomaton[{}]},
			outputrules
		]
	];
(*
Print[AutomatonGraph@reversedautomaton];
*)
	MorphicSequence[
		Normal[GroupBy[
			edges,
			Rule[
				#[[1, 1]] &,
(* xxx only works for base k numeration systems *)
				#[[2]] + 1 -> #[[1, 2]] &
			],
			Normal @* SparseArray
		]],
		initialstate,
(* xxx suppress this if it's the identity map? *)
		outputrules
	][n]
]
MorphicSequenceReduce[
	expression_,
	n_?PlausibleVariableQ,
	numerationsystem : _Integer?Positive(* more general numeration system? at least check that it's an integer >= 2? *) : 2,
	options : OptionsPattern[]
] :=
With[{automaticsequence = AutomaticSequenceReduce[expression, n, numerationsystem]},
	MorphicSequenceReduce[automaticsequence, n, numerationsystem, options] /;
		!MatchQ[automaticsequence, _AutomaticSequenceReduce]
]
Options[MorphicSequenceReduce] = {Monitor -> False}
SyntaxInformation[MorphicSequenceReduce] = {"ArgumentsPattern" -> {_, _, _., OptionsPattern[]}}

MorphismAdjacencyMatrix[
	rules : {(_String?(StringLength[#] == 1 &) -> _String) ..},
	alphabetorder : {__String?(StringLength[#] == 1 &)} | Automatic : Automatic
] :=
Module[{alphabet, alphabetpositionindex, sparsearrayrules, failed},
	failed = Catch[
		If[!DuplicateFreeQ[First /@ rules],
			Message[MorphismAdjacencyMatrix::left, rules]; Throw[True]
		];
		alphabet = If[ListQ[alphabetorder],
			alphabetorder,
			DeleteDuplicates[Join[
				First /@ rules,
				Join @@ Characters /@ Last /@ rules
			]]
		];
		alphabetpositionindex = First /@ PositionIndex[alphabet];
		sparsearrayrules = MapIndexed[
			Function[{rule, position},
				KeyValueMap[
					Function[{letter, count},
						{First[position], Lookup[alphabetpositionindex, letter, Message[MorphismAdjacencyMatrix::alph, letter, alphabet]; Throw[True]]} -> count
					],
					CharacterCounts[Last[rule]]
				]
			],
			Join[
				rules,
				# -> # & /@ DeleteCases[alphabet, Alternatives @@ First /@ rules]
			]
		];
		False
	];
	SparseArray[
		Join @@ sparsearrayrules,
		{Length[alphabet], Length[alphabet]}
	] /; !failed
]
MorphismAdjacencyMatrix[
	SubstitutionSystem[rules : {(_String?(StringLength[#] == 1 &) -> _String) ..}],
	alphabetorder : {__String?(StringLength[#] == 1 &)} | Automatic : Automatic
] :=
With[{matrix = MorphismAdjacencyMatrix[rules, alphabetorder]},
	matrix /; !MatchQ[matrix, _MorphismAdjacencyMatrix]
]
(* This doesn't check that the images have the same dimension, or that no lists appear as letters. *)
MorphismAdjacencyMatrix[
	rules : {(Except[_List] -> _List) ..},
	alphabetorder : _List | Automatic : Automatic
] :=
Module[{alphabet, alphabetpositionindex, sparsearrayrules, failed},
	failed = Catch[
		If[!DuplicateFreeQ[First /@ rules],
			Message[MorphismAdjacencyMatrix::left, rules]; Throw[True]
		];
		alphabet = If[ListQ[alphabetorder],
			alphabetorder,
			DeleteDuplicates[Join[
				First /@ rules,
				Flatten[Last /@ rules]
			]]
		];
		alphabetpositionindex = First /@ PositionIndex[alphabet];
		sparsearrayrules = MapIndexed[
			Function[{rule, position},
				KeyValueMap[
					Function[{letter, count},
						{First[position], Lookup[alphabetpositionindex, letter, Message[MorphismAdjacencyMatrix::alph, letter, alphabet]; Throw[True]]} -> count
					],
					Counts[Flatten[Last[rule]]]
				]
			],
			Join[
				rules,
				# -> {#} & /@ DeleteCases[alphabet, Alternatives @@ First /@ rules]
			]
		];
		False
	];
	SparseArray[
		Join @@ sparsearrayrules,
		{Length[alphabet], Length[alphabet]}
	] /; !failed
]
MorphismAdjacencyMatrix[
	SubstitutionSystem[rules : {(Except[_List] -> _List) ..}],
	alphabetorder : _List | Automatic : Automatic
] :=
With[{matrix = MorphismAdjacencyMatrix[rules, alphabetorder]},
	matrix /; !MatchQ[matrix, _MorphismAdjacencyMatrix]
]
SyntaxInformation[MorphismAdjacencyMatrix] = {"ArgumentsPattern" -> {_, _.}}
MorphismAdjacencyMatrix::alph = "Letter `1` doesn't belong to the alphabet `2`."
MorphismAdjacencyMatrix::left = "The left sides of the morphism rules `1` are not distinct."

(* This doesn't check that the images have the same dimension, or that no lists appear as letters. *)
MorphismPower[
	rules : {(_String?(StringLength[#] == 1 &) -> _String) ..} | {(Except[_List] -> _List) ..},
	n_Integer?NonNegative
] :=
With[{failed = !DuplicateFreeQ[First /@ rules]},
	If[failed,
		Message[MorphismPower::left, rules]
	];
	(First[#] -> SubstitutionSystem[rules, First[#], {{n}}] &) /@ rules /;
		!failed
]
MorphismPower[
	SubstitutionSystem[rules : {(_String?(StringLength[#] == 1 &) -> _String) ..} | {(Except[_List] -> _List) ..}],
	n_Integer?NonNegative
] :=
With[{morphism = MorphismPower[rules, n]},
	SubstitutionSystem[morphism] /; !MatchQ[morphism, _MorphismPower]
]
SyntaxInformation[MorphismPower] = {"ArgumentsPattern" -> {_, _}}
MorphismPower::left = "The left sides of the morphism rules `1` are not distinct."


(*** MotzkinNumber code ***)

$CacheMotzkinNumbers = False

$MotzkinNumberDirectory =
With[{directory = FileNameJoin[{$HomeDirectory, "Library", "Mobile Documents", "com~apple~CloudDocs", "Data", "Motzkin numbers"}]},
	If[DirectoryQ[directory], directory, $HomeDirectory]
]

MN[0] = MN[1] = 1
MN[n_Integer?Positive /; $CacheMotzkinNumbers || n <= 4] := MN[n] =
Block[{$RecursionLimit = Infinity},
	(3 (n - 1) MN[n - 2] + (2 n + 1) MN[n - 1])/(n + 2)
]
MN[n_Integer?Positive] := MN[n] =
Block[{$RecursionLimit = Infinity},
	With[{result = (3 (n - 1) MN[n - 2] + (2 n + 1) MN[n - 1])/(n + 2)},
		MN[n - 2] =.;
		result
	]
]

ClearMotzkinNumberCache[] := (
	DownValues[MN] = Join[
		Take[DownValues[MN], 2],
		(* If the number of down values of MN changes, then this needs to change. *)
		Take[DownValues[MN], -4]
	];
	Null
)
SyntaxInformation[ClearMotzkinNumberCache] = {"ArgumentsPattern" -> {}}

SetAttributes[ImportMotzkinNumber, Listable]
ImportMotzkinNumber[n_] :=
	If[FileExistsQ[FileNameJoin[{$MotzkinNumberDirectory, "M(" <> ToString[n - 1] <> ").m"}]] && FileExistsQ[FileNameJoin[{$MotzkinNumberDirectory, "M(" <> ToString[n] <> ").m"}]],
		MN[n - 1] = Import[FileNameJoin[{$MotzkinNumberDirectory, "M(" <> ToString[n - 1] <> ").m"}]];
		MN[n] = Import[FileNameJoin[{$MotzkinNumberDirectory, "M(" <> ToString[n] <> ").m"}]];
		,
		$Failed
	]
SyntaxInformation[ImportMotzkinNumber] = {"ArgumentsPattern" -> {_}}

SetAttributes[MotzkinNumber, {Listable, NumericFunction}]
MotzkinNumber[n_Integer?NonNegative] :=
	If[
(* XXX Should I maintain a list of indices that we've cached instead of checking DownValues?  What's the performance hit involved in doing these checks, if I'm just computing individual Motzkin numbers with Hypergeometric2F1? *)
		And[
			MemberQ[DownValues[MN], _[_[HoldPattern[MN][n - 2]], _]],
			MemberQ[DownValues[MN], _[_[HoldPattern[MN][n - 1]], _]]
		],
		MN[n],
(* This should probably cache its value if  $CacheAllMotzkinNumbers===True . *)
		Hypergeometric2F1[(1 - n)/2, -n/2, 2, 4]
	]
MotzkinNumber[-1] = 1
MotzkinNumber[x_?NumericQ] := GegenbauerC[x + 2, -(x + 1), -1/2] / (x + 1)
MotzkinNumber[n_, Import -> True] := Import[FileNameJoin[{$MotzkinNumberDirectory, "M(" <> ToString[n] <> ").m"}]]
MotzkinNumber[n_, Import -> False] := MotzkinNumber[n]
Options[MotzkinNumber] = {Import -> False}
SyntaxInformation[MotzkinNumber] = {"ArgumentsPattern" -> {_, OptionsPattern[]}}

(*** end MotzkinNumber code ***)


$OEISData =
<|
	"A000004" -> <|
		"Class" -> "Constant",
		"Function" -> (0 &)
	|>,
	"A000012" -> <|
		"Class" -> "Constant",
		"Function" -> (1 &)
	|>,
	"A007395" -> <|
		"Class" -> "Constant",
		"Function" -> (2 &)
	|>,
	"A010692" -> <|
		"Class" -> "Constant",
		"Function" -> (10 &)
	|>,
	"A010701" -> <|
		"Class" -> "Constant",
		"Function" -> (3 &)
	|>,
	"A010709" -> <|
		"Class" -> "Constant",
		"Function" -> (4 &)
	|>,
	"A010716" -> <|
		"Class" -> "Constant",
		"Function" -> (5 &)
	|>,
	"A010722" -> <|
		"Class" -> "Constant",
		"Function" -> (6 &)
	|>,
	"A010727" -> <|
		"Class" -> "Constant",
		"Function" -> (7 &)
	|>,
	"A010731" -> <|
		"Class" -> "Constant",
		"Function" -> (8 &)
	|>,
	"A010734" -> <|
		"Class" -> "Constant",
		"Function" -> (9 &)
	|>,
	"A010850" -> <|
		"Class" -> "Constant",
		"Function" -> (11 &)
	|>,
	"A010851" -> <|
		"Class" -> "Constant",
		"Function" -> (12 &)
	|>,
	"A010852" -> <|
		"Class" -> "Constant",
		"Function" -> (13 &)
	|>,
	"A010853" -> <|
		"Class" -> "Constant",
		"Function" -> (14 &)
	|>,
	"A010854" -> <|
		"Class" -> "Constant",
		"Function" -> (15 &)
	|>,
	"A010855" -> <|
		"Class" -> "Constant",
		"Function" -> (16 &)
	|>,
	"A010856" -> <|
		"Class" -> "Constant",
		"Function" -> (17 &)
	|>,
	"A010857" -> <|
		"Class" -> "Constant",
		"Function" -> (18 &)
	|>,
	"A010858" -> <|
		"Class" -> "Constant",
		"Function" -> (19 &)
	|>,
	"A010859" -> <|
		"Class" -> "Constant",
		"Function" -> (20 &)
	|>,
	"A010860" -> <|
		"Class" -> "Constant",
		"Function" -> (21 &)
	|>,
	"A010861" -> <|
		"Class" -> "Constant",
		"Function" -> (22 &)
	|>,
	"A010862" -> <|
		"Class" -> "Constant",
		"Function" -> (23 &)
	|>,
	"A010863" -> <|
		"Class" -> "Constant",
		"Function" -> (24 &)
	|>,
	"A010864" -> <|
		"Class" -> "Constant",
		"Function" -> (25 &)
	|>,
	"A010865" -> <|
		"Class" -> "Constant",
		"Function" -> (26 &)
	|>,
	"A010866" -> <|
		"Class" -> "Constant",
		"Function" -> (27 &)
	|>,
	"A010867" -> <|
		"Class" -> "Constant",
		"Function" -> (28 &)
	|>,
	"A010868" -> <|
		"Class" -> "Constant",
		"Function" -> (29 &)
	|>,
	"A010869" -> <|
		"Class" -> "Constant",
		"Function" -> (30 &)
	|>,
	"A010870" -> <|
		"Class" -> "Constant",
		"Function" -> (31 &)
	|>,
	"A010871" -> <|
		"Class" -> "Constant",
		"Function" -> (32 &)
	|>
|>

OEISsequencepattern = Alternatives @@ Keys[$OEISData]

OEISData[
	OEISSequence[anumber_String],
	property_
] :=
With[{result = OEISData[anumber, property]},
	result /; !MatchQ[result, _OEISData]
]
OEISData[
	anumber : OEISsequencepattern,
	property : "Class" | "Function" | "Properties" | "URL"
] :=
	Switch[property,
		"Properties",
			{"Class", "Function", "URL"},
		"URL",
			URL[URLBuild[{"https://oeis.org", anumber}]],
		_,
(* XXX Is this the right way to do this?  Use Part instead? *)
			$OEISData[anumber][property]
	]
SyntaxInformation[OEISData] = {"ArgumentsPattern" -> {_, _}}

OEISSequence[anumber_String /; StringMatchQ[anumber, "A" ~~ Repeated[DigitCharacter, {6}]]][n_] :=
With[{function = $OEISData[anumber]["Function"]},
	function[n] (*/; test XXX*)
]
SyntaxInformation[OEISSequence] = {"ArgumentsPattern" -> {_}}

OEISWebLookup[terms : {__Integer}] :=
	SystemOpen[URLBuild[{"https://oeis.org", "search"}, {"q" -> StringTake[ToString[terms], {2, -2}]}]]
OEISWebLookup[anumber_String /; StringMatchQ[anumber, "A" ~~ Repeated[DigitCharacter, {6}]]] :=
	SystemOpen[URLBuild[{"https://oeis.org", anumber}]]
SyntaxInformation[OEISWebLookup] = {"ArgumentsPattern" -> {_}}

(* TODO I have a Method->"AdamczewskiBell" version too.  Include it here? *)
OrePolynomial[polynomial_, variables_List /; variables != {}, p_Integer /; p >= 2, options : OptionsPattern[]] /;
	And[
		PolynomialQ[polynomial, variables],
		!FreeQ[polynomial, Last[variables]],
		MatchQ[OptionValue[OrePolynomial, {options}, Modulus], 0 | _?PrimeQ] || Message[OrePolynomial::modp, Modulus, OptionValue[OrePolynomial, {options}, Modulus]]
	] :=
Module[{y = Last[variables], modulus = OptionValue[Modulus], reducedpolynomial, degree, nullspace, orepolynomial, minexponent, residuelist},
	(* TODO Avoid expanding by using CoefficientRules instead? *)
	reducedpolynomial = Expand[polynomial, Modulus -> modulus];
	(* Test whether the input already has the desired exponents. *)
	If[MatchQ[Log[p, Exponent[reducedpolynomial, y, List]], {__Integer?NonNegative}],
		orepolynomial = reducedpolynomial
		,
		degree = Exponent[reducedpolynomial, y];
		(* TODO Give Modulus to NullSpace? *)
		nullspace = NullSpace[Transpose[
			CoefficientList[#, y, degree] & /@
				Table[
					PolynomialRemainder[y^p^i, reducedpolynomial, y, Modulus -> modulus],
					{i, 0, degree}
				]
		]];
(* TODO Issue a warning message here?
		If[Length[nullspace] != 1,
			Print["warning; null space has dimension ", Length[nullspace]]
		];
*)
		orepolynomial = Dot[
			Expand[
				(* TODO Give Modulus to Cancel?  PolynomialLCM? *)
				Cancel[PolynomialLCM @@ Denominator[Together[Last[nullspace]]] Last[nullspace]],
				Modulus -> modulus
			],
			y^p^Range[0, degree]
		]
	];
	If[p == modulus && PrimeQ[p],
		(* Get a nonzero linear coefficient. *)
		minexponent = Exponent[orepolynomial, y, Min, Modulus -> p];
		residuelist = If[Length[variables] == 1,
			{},
			CoefficientRules[Coefficient[orepolynomial, y, minexponent], Most[variables], Modulus -> p][[-1, 1]]
		];
		orepolynomial = FromCoefficientRules[
			Cases[
				CoefficientRules[orepolynomial, variables, Modulus -> p],
				(exponents_ /; MatchQ[Mod[Most[exponents] - residuelist, minexponent], {0 ...}] -> coefficient_) :>
					(Quotient[exponents, minexponent] -> coefficient)
			],
			variables
		];
		orepolynomial = Cancel[orepolynomial/PolynomialGCD[Sequence @@ Last /@ CoefficientRules[orepolynomial, y], Modulus -> p], Modulus -> p];
		orepolynomial = Collect[orepolynomial, y]
	];
	orepolynomial
]
OrePolynomial[polynomial_, variable : Except[_List], p_Integer, options : OptionsPattern[]] :=
	OrePolynomial[polynomial, {variable}, p, options]
OrePolynomial[polynomial_, p_Integer, variablespec_, options : OptionsPattern[]] :=
(
	Message[OrePolynomial::syntax, polynomial, variablespec, p];
	OrePolynomial[polynomial, variablespec, p, options]
)
Options[OrePolynomial] = {Modulus -> 0}
SyntaxInformation[OrePolynomial] = {"ArgumentsPattern" -> {_, _, _, OptionsPattern[]}}
OrePolynomial::syntax = "The syntax of OrePolynomial has changed.  Using OrePolynomial[`1`, `2`, `3`]."

SetAttributes[Radical, Listable]
Radical[0] = Infinity
Radical[n_Integer] := Times @@ First /@ FactorInteger[Abs[n]]
SyntaxInformation[Radical] = {"ArgumentsPattern" -> {_}}


(*** ReduceAutomaton code ***)

(* TODO  complementpattern[0 | 1, 2]  evaluates to  Alternatives[] , so check that it doesn't occur. *)
complementpattern[pattern_, numerationsystem_] :=
	Replace[
		Alternatives @@ DeleteCases[NumerationSystemDigitList[numerationsystem], pattern],
		HoldPattern[Alternatives][x_] :> x
	]

ConstantAutomaton[n_Integer?NonNegative, numerationsystem_?PositiveNumerationSystemQ] :=
Module[{digitlist, acceptingstate, absorbingstate},
	digitlist = DigitList[n, numerationsystem];
	acceptingstate = Length[digitlist] + 1;
	absorbingstate = acceptingstate + 1;
	Automaton[
		Join[
			Join @@ MapIndexed[
				Function[{digit, position},
					{
						{position[[1]] -> position[[1]] + 1, {digit}},
						{position[[1]] -> absorbingstate, {complementpattern[digit, numerationsystem]}}
					}
				],
				digitlist
			],
			{
				{acceptingstate -> acceptingstate, {0}},
				{acceptingstate -> absorbingstate, {complementpattern[0, numerationsystem]}},
				{absorbingstate -> absorbingstate, {_}}
			}
		],
		1,
		(* TODO Is this pattern safe?  The other automata give all explicit rules. *)
		{acceptingstate -> True, _ -> False},
		InputAlphabet -> Tuples[NumerationSystemDigitList[numerationsystem], 1]
	]
]

EqualAutomaton[base_Integer /; base >= 2] :=
Module[{digit},
	Automaton[
		Join[
			Join @@ Table[
				{
					{1 -> 1, {digit, digit}},
					{1 -> 2, {digit, complementpattern[digit, base]}}
				},
				{digit, 0, base - 1}
			],
			{{2 -> 2, {_, _}}}
		],
		1,
		{1 -> True, 2 -> False},
		InputAlphabet -> Tuples[Range[0, base - 1], 2]
	]
]
EqualAutomaton["Fibonacci" | "Tribonacci"] :=
	EqualAutomaton[2]

PlusAutomaton[base_Integer /; base >= 2] :=
Module[{sum, carry, i, j},
	Automaton[
		Join[
			Flatten[
				Table[
					sum = carry + i + j;
					{
						{carry -> Quotient[sum, base], {i, j, Mod[sum, base]}},
						{carry -> 2, {i, j, complementpattern[Mod[sum, base], base]}}
					}
					,
					{carry, 0, 1},
					{i, 0, base - 1},
					{j, 0, base - 1}
				],
				3
			],
			{{2 -> 2, {_, _, _}}}
		],
		0,
		{0 -> True, 1 -> False, 2 -> False},
		InputAlphabet -> Tuples[Range[0, base - 1], 3]
	]
]
(* If we end up computing time-consuming automata for other numeration systems, it may be worthwhile to not compute them multiple times. *)
PlusAutomaton["Fibonacci"] :=
 Automaton[{{1 -> 2, {0, 0, 0}}, {1 -> 3, {0, 0, 1}}, {1 -> 
     4, {0, 1, 0}}, {1 -> 2, {0, 1, 1}}, {1 -> 4, {1, 0, 0}}, {1 -> 
     2, {1, 0, 1}}, {1 -> 5, {1, 1, 0}}, {1 -> 4, {1, 1, 1}}, {2 -> 
     2, {0, 0, 0}}, {2 -> 6, {0, 0, 1}}, {2 -> 7, {0, 1, 0}}, {2 -> 
     2, {0, 1, 1}}, {2 -> 7, {1, 0, 0}}, {2 -> 2, {1, 0, 1}}, {2 -> 
     8, {1, 1, 0}}, {2 -> 7, {1, 1, 1}}, {3 -> 9, {0, 0, 0}}, {3 -> 
     10, {0, 0, 1}}, {3 -> 11, {0, 1, 0}}, {3 -> 9, {0, 1, 1}}, {3 -> 
     11, {1, 0, 0}}, {3 -> 9, {1, 0, 1}}, {3 -> 12, {1, 1, 0}}, {3 -> 
     11, {1, 1, 1}}, {4 -> 11, {0, 0, 0}}, {4 -> 9, {0, 0, 1}}, {4 -> 
     12, {0, 1, 0}}, {4 -> 11, {0, 1, 1}}, {4 -> 12, {1, 0, 0}}, {4 ->
      11, {1, 0, 1}}, {4 -> 13, {1, 1, 0}}, {4 -> 12, {1, 1, 
     1}}, {5 -> 7, {0, 0, 0}}, {5 -> 2, {0, 0, 1}}, {5 -> 8, {0, 1, 
     0}}, {5 -> 7, {0, 1, 1}}, {5 -> 8, {1, 0, 0}}, {5 -> 7, {1, 0, 
     1}}, {5 -> 14, {1, 1, 0}}, {5 -> 8, {1, 1, 1}}, {6 -> 9, {0, 0, 
     0}}, {6 -> 10, {0, 0, 1}}, {6 -> 15, {0, 1, 0}}, {6 -> 9, {0, 1, 
     1}}, {6 -> 15, {1, 0, 0}}, {6 -> 9, {1, 0, 1}}, {6 -> 15, {1, 1, 
     0}}, {6 -> 15, {1, 1, 1}}, {7 -> 11, {0, 0, 0}}, {7 -> 15, {0, 0,
      1}}, {7 -> 12, {0, 1, 0}}, {7 -> 11, {0, 1, 1}}, {7 -> 12, {1, 
     0, 0}}, {7 -> 11, {1, 0, 1}}, {7 -> 13, {1, 1, 0}}, {7 -> 12, {1,
      1, 1}}, {8 -> 15, {0, 0, 0}}, {8 -> 15, {0, 0, 1}}, {8 -> 
     15, {0, 1, 0}}, {8 -> 15, {0, 1, 1}}, {8 -> 15, {1, 0, 0}}, {8 ->
      15, {1, 0, 1}}, {8 -> 14, {1, 1, 0}}, {8 -> 15, {1, 1, 
     1}}, {9 -> 15, {0, 0, 0}}, {9 -> 15, {0, 0, 1}}, {9 -> 11, {0, 1,
      0}}, {9 -> 15, {0, 1, 1}}, {9 -> 11, {1, 0, 0}}, {9 -> 15, {1, 
     0, 1}}, {9 -> 12, {1, 1, 0}}, {9 -> 11, {1, 1, 1}}, {10 -> 6, {0,
      0, 0}}, {10 -> 16, {0, 0, 1}}, {10 -> 2, {0, 1, 0}}, {10 -> 
     6, {0, 1, 1}}, {10 -> 2, {1, 0, 0}}, {10 -> 6, {1, 0, 1}}, {10 ->
      7, {1, 1, 0}}, {10 -> 2, {1, 1, 1}}, {11 -> 15, {0, 0, 
     0}}, {11 -> 9, {0, 0, 1}}, {11 -> 15, {0, 1, 0}}, {11 -> 15, {0, 
     1, 1}}, {11 -> 15, {1, 0, 0}}, {11 -> 15, {1, 0, 1}}, {11 -> 
     15, {1, 1, 0}}, {11 -> 15, {1, 1, 1}}, {12 -> 7, {0, 0, 
     0}}, {12 -> 2, {0, 0, 1}}, {12 -> 8, {0, 1, 0}}, {12 -> 7, {0, 1,
      1}}, {12 -> 8, {1, 0, 0}}, {12 -> 7, {1, 0, 1}}, {12 -> 15, {1, 
     1, 0}}, {12 -> 8, {1, 1, 1}}, {13 -> 12, {0, 0, 0}}, {13 -> 
     11, {0, 0, 1}}, {13 -> 13, {0, 1, 0}}, {13 -> 12, {0, 1, 
     1}}, {13 -> 13, {1, 0, 0}}, {13 -> 12, {1, 0, 1}}, {13 -> 17, {1,
      1, 0}}, {13 -> 13, {1, 1, 1}}, {14 -> 8, {0, 0, 0}}, {14 -> 
     7, {0, 0, 1}}, {14 -> 15, {0, 1, 0}}, {14 -> 8, {0, 1, 
     1}}, {14 -> 15, {1, 0, 0}}, {14 -> 8, {1, 0, 1}}, {14 -> 15, {1, 
     1, 0}}, {14 -> 15, {1, 1, 1}}, {15 -> 15, {0, 0, 0}}, {15 -> 
     15, {0, 0, 1}}, {15 -> 15, {0, 1, 0}}, {15 -> 15, {0, 1, 
     1}}, {15 -> 15, {1, 0, 0}}, {15 -> 15, {1, 0, 1}}, {15 -> 15, {1,
      1, 0}}, {15 -> 15, {1, 1, 1}}, {16 -> 15, {0, 0, 0}}, {16 -> 
     18, {0, 0, 1}}, {16 -> 15, {0, 1, 0}}, {16 -> 15, {0, 1, 
     1}}, {16 -> 15, {1, 0, 0}}, {16 -> 15, {1, 0, 1}}, {16 -> 15, {1,
      1, 0}}, {16 -> 15, {1, 1, 1}}, {17 -> 15, {0, 0, 0}}, {17 -> 
     15, {0, 0, 1}}, {17 -> 14, {0, 1, 0}}, {17 -> 15, {0, 1, 
     1}}, {17 -> 14, {1, 0, 0}}, {17 -> 15, {1, 0, 1}}, {17 -> 19, {1,
      1, 0}}, {17 -> 14, {1, 1, 1}}, {18 -> 15, {0, 0, 0}}, {18 -> 
     15, {0, 0, 1}}, {18 -> 15, {0, 1, 0}}, {18 -> 15, {0, 1, 
     1}}, {18 -> 15, {1, 0, 0}}, {18 -> 15, {1, 0, 1}}, {18 -> 11, {1,
      1, 0}}, {18 -> 15, {1, 1, 1}}, {19 -> 13, {0, 0, 0}}, {19 -> 
     12, {0, 0, 1}}, {19 -> 17, {0, 1, 0}}, {19 -> 13, {0, 1, 
     1}}, {19 -> 17, {1, 0, 0}}, {19 -> 13, {1, 0, 1}}, {19 -> 20, {1,
      1, 0}}, {19 -> 17, {1, 1, 1}}, {20 -> 15, {0, 0, 0}}, {20 -> 
     15, {0, 0, 1}}, {20 -> 15, {0, 1, 0}}, {20 -> 15, {0, 1, 
     1}}, {20 -> 15, {1, 0, 0}}, {20 -> 15, {1, 0, 1}}, {20 -> 21, {1,
      1, 0}}, {20 -> 15, {1, 1, 1}}, {21 -> 15, {0, 0, 0}}, {21 -> 
     8, {0, 0, 1}}, {21 -> 15, {0, 1, 0}}, {21 -> 15, {0, 1, 
     1}}, {21 -> 15, {1, 0, 0}}, {21 -> 15, {1, 0, 1}}, {21 -> 15, {1,
      1, 0}}, {21 -> 15, {1, 1, 1}}}, 1, {1 | 2 -> True, _ -> False}, InputAlphabet -> Tuples[{0, 1}, 3]]
(* TODO
PlusAutomaton[n_Integer?Positive, "Tribonacci"] :=
*)

TimesAutomaton[n_Integer?Positive, base_Integer /; base >= 2] :=
Module[{sum, carry, digit},
	Automaton[
		Join[
			Flatten[
				Table[
					sum = carry + n digit;
					{
						{carry -> Quotient[sum, base], {digit, Mod[sum, base]}},
						{carry -> n, {digit, complementpattern[Mod[sum, base], base]}}
					}
					,
					{carry, 0, n - 1},
					{digit, 0, base - 1}
				],
				2
			],
			{{n -> n, {_, _}}}
		],
		0,
		Join[{0 -> True}, Table[carry -> False, {carry, 1, n}]],
		InputAlphabet -> Tuples[Range[0, base - 1], 2]
	]
]
(* TODO
TimesAutomaton[n_Integer?Positive, "Fibonacci"] :=
TimesAutomaton[n_Integer?Positive, "Tribonacci"] :=
*)

(* To accept a representation of an integer with a different number of leading zeros than it had as part of the pair that was accepted in the automaton before applying Exists,
   any rejecting state from which an accepting state can be reached by reading some (positive) number of 0 tuples needs to be switched to an accepting state.  (Currently I'm doing this after determinizing.)
   If I expose ExistsAutomaton, this could be controlled by an option, but for reading integers I'll always want to do it. *)
ExistsAutomaton[
	varstodelete_List,
	{
		inputautomaton_Automaton,
		variables_
	},
	numerationsystem_,
	OptionsPattern[]
] :=
Module[{variablepositions, automaton, temporarycells = {}, failed},
	failed = Catch[
		If[TrueQ[OptionValue[Monitor]],
			AppendTo[temporarycells, PrintTemporary["Computing the automaton for an Exists expression..."]];
			AppendTo[temporarycells, PrintTemporary[Tab, "Input state count: ", AutomatonStateCount[inputautomaton]]]
		];
		variablepositions = Position[variables, Alternatives @@ varstodelete, {1}, Heads -> False];
		If[Length[variablepositions] != Length[varstodelete],
			Throw[True]
		];
		(* For numeration systems such as Fibonacci, not all words are canonical representations,
		   so it can happen that a path to an accepting state was not a valid path before edge components were deleted.
		   To fix this, we intersect with the language of the tuples of canonical representations before deleting components. *)
		automaton = Switch[numerationsystem,
			_Integer,
				inputautomaton,
			"Fibonacci",
				AutomatonProduct[
					inputautomaton,
					Automaton[
						Append[
							Join @@ Function[state,
								{
									state -> If[MemberQ[state + #, 2], 0, #],
									#
								} & /@
									Tuples[{0, 1}, Length[variables]]
							] /@ Tuples[{0, 1}, Length[variables]],
							{0 -> 0, _}
						],
						ConstantArray[0, Length[variables]],
						{0 -> False, _ -> True},
						InputAlphabet -> AutomatonInputAlphabet[inputautomaton]
					],
					And @@ # &,
					Minimize -> OptionValue[Minimize]
				]
		];
		(* Delete components of the edges. *)
		automaton = MapAt[
			(* If there are patterns present in edge labels, then DeleteDuplicates may not remove all duplicates.  TODO Is that okay? *)
			Function[edges, DeleteDuplicates[MapAt[Delete[#, variablepositions] &, 2] /@ edges]],
			automaton,
			1
		];
		(* Delete components of the input alphabet tuples. *)
		automaton = MapAt[
			Function[inputalphabet, DeleteDuplicates[(Delete[#, variablepositions] &) /@ inputalphabet]],
			automaton,
			{4, 2}
		];
(* xxx old; can delete
		automaton = Automaton[
			(* If there are patterns present in edge labels, then DeleteDuplicates may not remove all duplicates.  TODO Is that okay? *)
			DeleteDuplicates[ListMapAt[Delete[#, variablepositions] &, First[automaton], 2]],
			initialstate,
(* old; not correct
This code identifies accepting states that have no valid paths and makes them rejecting states, but it's not sufficient.
					Switch[numerationsystem,
						_Integer,
							outputrules,
						"Fibonacci",
							Module[{reachability, remainingstates, currentstate, newreachability},
								reachability[initialstate] = ConstantArray[0, Length[variables]];
								remainingstates = Cases[edges, {initialstate -> state_, _} :> state];
								(* This might also be possible using DepthFirstScan. *)
statelist = AutomatonStateList[inputautomaton];
Monitor[
								While[remainingstates != {},
									currentstate = First[remainingstates];
									remainingstates = Rest[remainingstates];
									newreachability = MapThread[
										Min,
										Join[
											{Replace[reachability[currentstate], _reachability -> ConstantArray[Infinity, Length[variables]]]},
											Cases[
												edges,
												(* This assumes explicit edge labels (no patterns).  TODO Are we guaranteed to have them? *)
												{state_ -> currentstate, label_} :>
													(* This uses 0 and 1 in a dual way; in  label , they are input alphabet letters,
													   but they also happen to be the number of 1s in each component. *)
													label + Replace[reachability[state], _reachability -> ConstantArray[Infinity, Length[variables]]]
											]
										]
									];
									If[newreachability =!= reachability[currentstate],
										reachability[currentstate] = newreachability;
										remainingstates = DeleteDuplicates[Join[
											Cases[edges, {currentstate -> state_, _} :> state],
											remainingstates
										]]
									]
								];
,
Column[{
	{reachability[currentstate], newreachability},
	remainingstates,
	reachability /@ statelist
}]
];
Print[reachability /@ statelist];
								Function[s, s -> Replace[s, outputrules] && Max[reachability[s]] <= 1] /@
									AutomatonStateList[inputautomaton]
							]
*)
			outputrules,
			InputAlphabet -> DeleteDuplicates[(Delete[#, variablepositions] &) /@ AutomatonInputAlphabet[XXX]]
		];
*)
		automaton = AutomatonPadRight[
			AutomatonDeterminize[
				automaton,
				Or @@ # &,
				(* Instead of minimizing here, we minimize below. *)
				Minimize -> False
			],
			Length[variables] - Length[varstodelete]
		];
		If[TrueQ[OptionValue[Minimize]],
			If[TrueQ[OptionValue[Monitor]],
				AppendTo[temporarycells, PrintTemporary[Tab, "State count: ", AutomatonStateCount[automaton]]];
				AppendTo[temporarycells, PrintTemporary[Tab, "minimizing..."]]
			];
			automaton = AutomatonMinimize[automaton]
		];
		If[TrueQ[OptionValue[Monitor]],
			AppendTo[temporarycells, PrintTemporary[Tab, "Output state count: ", AutomatonStateCount[automaton]]];
			NotebookDelete[temporarycells]
		];
		False
	];
	{
		automaton,
		Delete[variables, variablepositions]
	} /; !failed
]
Options[ExistsAutomaton] = {Minimize -> True, Monitor -> False}

(*
TODO $Failed outputs in the input automata here that aren't specified by the output rules aren't getting addressed.
And Verbatim[_] is too specific; it doesn't support general patterns.
*)
(* If exposed, this should check that the arity of each automaton matches the corresponding number of variables, because if these are different then it really messes things up.
   [TODO That note is from an older version; still relevant?] *)
OrAutomaton[
	{
		inputautomaton1 : Automaton[edges1_, initialstate1_, outputrules1_, InputAlphabet -> inputalphabet1_],
		variables1_
	},
	{
		inputautomaton2 : Automaton[_, initialstate2_, outputrules2_, InputAlphabet -> _],
		unsortedvariables2_
	},
	numerationsystem_,
	OptionsPattern[]
] :=
Module[{combinedvariables, permutation, edges2, inputalphabet2, variables2, freevariablepositions1, freevariablepositions2, automaton, temporarycells = {}},
	If[TrueQ[OptionValue[Monitor]],
		AppendTo[temporarycells, PrintTemporary["Computing the automaton for an Or expression..."]];
		AppendTo[temporarycells, PrintTemporary[Tab, "Input state counts: ", {AutomatonStateCount[inputautomaton1], AutomatonStateCount[inputautomaton2]}]]
	];
	combinedvariables = DeleteDuplicates[Join[variables1, unsortedvariables2]];
	permutation = InversePermutation[Ordering[(Position[combinedvariables, #][[1, 1]] &) /@ unsortedvariables2]];
	{edges2, inputalphabet2} = ({#[[1]], #[[4, 2]]} &)[
		AutomatonPermute[inputautomaton2, unsortedvariables2, permutation]
	];
	variables2 = Permute[unsortedvariables2, permutation];
	freevariablepositions1 = Position[combinedvariables, Alternatives @@ Complement[variables2, variables1]];
	freevariablepositions2 = Position[combinedvariables, Alternatives @@ Complement[variables1, variables2]];
	automaton = AutomatonProduct[
		AutomatonInputAlphabetInsert[
			Automaton[edges1, initialstate1, outputrules1, InputAlphabet -> inputalphabet1],
			numerationsystem,
			freevariablepositions1,
			_
		],
		AutomatonInputAlphabetInsert[
			Automaton[edges2, initialstate2, outputrules2, InputAlphabet -> inputalphabet2],
			numerationsystem,
			freevariablepositions2,
			_
		],
		Or @@ # &,
		Minimize -> OptionValue[Minimize]
	];
	If[TrueQ[OptionValue[Monitor]],
		AppendTo[temporarycells, PrintTemporary[Tab, "Output state count: ", AutomatonStateCount[automaton]]];
		NotebookDelete[temporarycells]
	];
	{
		automaton,
		combinedvariables
	}
]
Options[OrAutomaton] = {Minimize -> True, Monitor -> False}

(* If this receives an underdetermined automaton with no output for $Failed then of course that's incorrect, but it will output without complaining. *)
NotAutomaton[
	{
		(* This pattern for  outputrules  is not general enough to expose.
		   There may even be problems currently if an AutomaticSequence automaton uses a dispatch table or something. *)
		Automaton[edges_, initialstate_, outputrules : {(_ -> True | False) ..}, InputAlphabet -> inputalphabet_],
		variables_
	}
] :=
	{
		Automaton[edges, initialstate, MapAt[Not, 2] /@ outputrules, InputAlphabet -> inputalphabet],
		variables
	}

ReduceAutomaton[
	expression_,
	numerationsystem_?PositiveNumerationSystemQ
] :=
	ReduceAutomaton[expression, numerationsystem, {}]
ReduceAutomaton[
	expression_,
	numerationsystem_?PositiveNumerationSystemQ,
	(* This doesn't catch options inside lists or specificed with RuleDelayed. *)
	options__Rule
] :=
	ReduceAutomaton[expression, numerationsystem, {}, options]
ReduceAutomaton[
	expression_,
	numerationsystem_?PositiveNumerationSystemQ,
	variable : Except[_List],
	options : OptionsPattern[]
] :=
	ReduceAutomaton[expression, numerationsystem, {variable}, options]
ReduceAutomaton[
	expression_,
	numerationsystem_?PositiveNumerationSystemQ,
	variables_List /; Sort[variables] === Sort[Variables[variables]] || Message[ReduceAutomaton::ivar, First[Complement[variables, Variables[variables]]]],
	OptionsPattern[]
] :=
Module[
	{
		expandedexpression, conflictingsymbols, automatoncomputationrules, automaton, finalvariables, minimize, $inequalityheadpattern, failed,
		information, monitor, constructioncount, completedconstructioncount, statecounts,
		and, exists, forall, not, or, plus, quantifiedexpression, symbol, synchronizedsequence, times, with
	},
	failed = Catch[
		information = TrueQ[OptionValue[Information]];
		If[TrueQ[OptionValue[Monitor]] && 10 < $VersionNumber < 11,
			Message[Monitor::abort]
		];
		monitor = TrueQ[OptionValue[Monitor]] && !(10 < $VersionNumber < 11);
		minimize = OptionValue[Minimize];
		$inequalityheadpattern = Equal | Greater | GreaterEqual | Less | LessEqual | Unequal;
		(* Add a wrapper to be able to identify atomic expressions. *)
		expandedexpression = expression /.
			variable : Alternatives @@ variables :> symbol[variable];
		(* Convert three-argument versions of Exists and ForAll. *)
		expandedexpression = expandedexpression //. {
			HoldPattern[Exists][vars_, condition_, expr_] :> Exists[vars, condition && expr],
			HoldPattern[ForAll][vars_, condition_, expr_] :> ForAll[vars, Implies[condition, expr]]
		};
		(* Put single quantified variables into lists. *)
		expandedexpression = expandedexpression //.
			(quantifier : Exists | ForAll)[x : Except[_List], expr_] :> quantifier[{x}, expr];
		(* Replace Exists with a new wrapper; this prevents  !Exists[x,f[x]]  from evaluating to  ForAll[x,!f[x]] . *)
		expandedexpression = expandedexpression //. {
			HoldPattern[Exists][vars_List, expr_] :> exists[symbol /@ vars, expr /. variable : Alternatives @@ vars :> symbol[variable]],
			HoldPattern[ForAll][vars_List, expr_] :> forall[symbol /@ vars, expr /. variable : Alternatives @@ vars :> symbol[variable]]
		};
		(* Check for quantified variables that the user claims are free or are quantified twice in nested quantifiers. *)
		conflictingsymbols = Cases[expandedexpression, symbol[symbol[variable_]] :> variable, {0, Infinity}];
		If[conflictingsymbols != {},
			Message[ReduceAutomaton::quant, DeleteDuplicates[conflictingsymbols /. symbol -> Identity]]; Throw[True]
		];
		(* Remove assertions that symbols are integers. *)
		expandedexpression = expandedexpression /.
			Element[_symbol, Integers] -> True;
		(* Move negative terms to the other side of an equation or inequality.
		   This doesn't look into unexpanded expressions, and it doesn't move terms in Inequality. *)
		expandedexpression = expandedexpression //.
			(head : $inequalityheadpattern)[w___, Plus[x : Times[_Integer?Negative, _.], y_.], z___] :>
				head @@ Join[{w} - x, {y}, {z} - x];
		(* Rewrite automatic sequences. *)
		expandedexpression = expandedexpression //. {
(* TODO this and its reverse?
			AutomaticSequence[m_Automaton][x__symbol] == c_Integer(*?NonNegative*) :> ,
*)
			AutomaticSequence[m_Automaton(*, XXX optional numeration system *)][x__] :>
				(* TODO This doesn't support base Fibonacci. *)
				With[{sequence = SynchronizedSequenceReduce[AutomaticSequence[m(*, XXX optional numeration system *)][x], {x}, numerationsystem, Minimize -> minimize]},
					(* At one point this condition prevented an infinite loop for  ReduceAutomaton[ThueMorse[x] == 0, 3, x] .
					   It's no longer needed for that, but we probably still want the test. *)
					sequence /; !MatchQ[sequence, _SynchronizedSequenceReduce] || Message[ReduceAutomaton::auto, AutomaticSequence[m][x]]
				],
			Divisible[x_, m_Integer?Positive] :>
				Mod[x, m] == 0,
(* TODO Update documentation to include support for BaumSweet. *)
			BaumSweet[x_] /; numerationsystem === 2 :>
				AutomaticSequence[$BaumSweetAutomaton][x],
(* TODO XXX But the new RudinShapiro is a problem because here we're only supposed to be dealing with non-negative integers. *)
			RudinShapiro[x_] /; numerationsystem === 2 :>
				AutomaticSequence[$RudinShapiroAutomaton][x],
			ThueMorse[x_] /; numerationsystem === 2 :>
				AutomaticSequence[$ThueMorseAutomaton][x]
		};
		(* Replace subexpressions with quantified variables.  New symbols for Plus and SynchronizedSequence prevent an infinite loop. *)
		expandedexpression = expandedexpression //. {
			Mod[x_, m_Integer?Positive] :>
				With[{q = symbol[Unique[]], r = symbol[Unique[]]},
					quantifiedexpression[r, exists[{q, r}, m q + r == x && r < m]]
				],
			(* TODO Must the arguments be distinct? *)
			SynchronizedSequence[m_Automaton][x__] :>
				With[{y = symbol[Unique[]]},
					quantifiedexpression[y, exists[{y}, synchronizedsequence[m][x] == y]]
				],
			Times[c_Integer /; c >= 2, x_] :>
				With[{y = symbol[Unique[]]},
					quantifiedexpression[y, exists[{y}, times[c, x] == y]]
				],
			Plus[x_, y_, z___] :>
				With[{w = symbol[Unique[]]},
					quantifiedexpression[Plus[w, z], exists[{w}, plus[x, y] == w]]
				]
		};
		(* Rewrite equalities and inequalities using only two arguments. *)
		expandedexpression = expandedexpression /.
			inequality : ($inequalityheadpattern | Inequality)[_, _, __] :> LogicalExpand[inequality];
		(* Convert boolean expressions to expressions in Not and Or, and convert ForAll to Exists. *)
		expandedexpression = expandedexpression //. {
			(booleanhead : And | Equivalent | Implies | Majority | Nand | Nor | Xnor | Xor | _BooleanFunction)[a__] :>
				(* Introduce new symbols for the arguments to avoid creating multiple copies of an expression
				   that would then each be evaluated. *)
				With[{expressionnames = Table[Unique[], {Length[{a}]}]},
					with[Thread[expressionnames -> {a}], BooleanConvert[booleanhead @@ expressionnames, "OR"]]
				],
			forall[vars_, expr_] :> !exists[vars, !expr]
		};
		(* Replace Not and Or with inert wrappers. *)
		expandedexpression = expandedexpression //. {
			Not[a_] :> not[a],
			Or[a_, b_, c___] :> Or[or[a, b], c]
		};
		(* Convert inequalities to expressions in Equal.  These rules don't introduce And, Exists, Not, Or, Plus, or Times. *)
		expandedexpression = expandedexpression //. {
			y_ > x_ :> x < y,
			y_ >= x_ :> x <= y,
(* TODO Are these alternatives better or worse?
			y_ > x_ :> not[y <= x],
			y_ >= x_ :> not[y < x],
*)
			x_ != y_ :> not[x == y],
(* TODO Alternatively this could replace with  x<=y+1 .  Better or worse?  Currently it duplicates expressions that then each get evaluated. *)
			x_ < y_ :> and[x <= y, x != y],
			x_ <= y_ :>
				With[{z = symbol[Unique[]]},
					exists[{z}, plus[x, z] == y]
				]
		};
		(* Replace additive constants with quantified variables.  This is done after converting inequalities to Equal because 3 <= x has been converted to an expression in plus[3, z]. *)
		expandedexpression = expandedexpression //. {
			((x : Except[_symbol]) == c_Integer?NonNegative) | (c_Integer?NonNegative == (x : Except[_symbol])) :>
				With[{y = symbol[Unique[]]},
					exists[{y}, and[x == y, y == c]]
				],
			plus[x_, c_Integer?NonNegative] | plus[c_Integer?NonNegative, x_] :>
				With[{y = symbol[Unique[]]},
					quantifiedexpression[plus[x, y], exists[{y}, y == c]]
				]
		};
		(* Pull quantifiers out of arguments of arithmetic functions and predicates and up into arguments of boolean functions.
		   Equal and plus only have two arguments, even though it looks like these patterns catch more. *)
		expandedexpression = expandedexpression //. {
			Equal[x___, quantifiedexpression[y_, exists[vars_, condition_]], z___] :>
				exists[vars, and[condition, Equal[x, y, z]]],
			(head : plus | times | synchronizedsequence[_])[x___, quantifiedexpression[y_, condition_], z___] :>
				quantifiedexpression[head[x, y, z], condition]
		};
		(* Convert conjunction wrappers. *)
		expandedexpression = expandedexpression //.
			and[a_, b_] :> not[or[not[a], not[b]]];
		(* Join nested quantified variable lists to reduce the number of ExistsAutomaton evaluations. *)
		expandedexpression = expandedexpression //. {
			exists[vars1_, exists[vars2_, expr_]] :> exists[Join[vars1, vars2], expr],
			not[not[a_]] :> a
		};
		If[information,
			Print["Expression depth: ", Depth[expandedexpression]];
			Print["Expression byte count: ", ByteCount[expandedexpression]];
			Print["Number of distinct variables: ", Length[DeleteDuplicates[Cases[expandedexpression, symbol[variable_] :> variable, {0, Infinity}]]]];
			Print["Number of Exists expressions: ", Count[expandedexpression, _exists, {0, Infinity}]];
			Print["Number of Or expressions: ", Count[expandedexpression, _or, {0, Infinity}]];
			statecounts = Cases[expandedexpression, m_Automaton :> AutomatonStateCount[m], {0, Infinity}]
		];
		If[monitor,
			constructioncount = Count[expandedexpression, _exists | _or, {0, Infinity}];
			completedconstructioncount = 0
		];
(* This is useful for debugging.
Print[expandedexpression /. {and -> Inactive[And], exists -> Inactive[Exists], not -> Inactive[Not], or -> Inactive[Or], plus -> Inactive[Plus], synchronizedsequence -> Inactive[SynchronizedSequence], times -> Inactive[Times], symbol -> Identity, with -> Inactive[With], m_Automaton :> Automaton[Skeleton[AutomatonStateCount[m]]]}];
*)
		(* Compute the automata. *)
		automatoncomputationrules = {
			exists[vars_, a : {_Automaton, _List}] :>
				With[{m = (*(Print[#[[1]]];#[[2]])&@(AbsoluteTiming@*)ExistsAutomaton[vars, a, numerationsystem, Minimize -> minimize, Monitor -> monitor](*)*)},
(*
Print[Exists];
Print[Tab, vars];
Print[Tab, a];
Print[Tab, m];
*)
(*
If[!MatchQ[m, {_Automaton, _List}],
	Print[Style["problem in ExistsAutomaton", Red]]
];
*)
					If[information,
						AppendTo[statecounts, AutomatonStateCount[First[m]]]
					];
					If[monitor,
						completedconstructioncount++
					];
					m
				],
			or[a : {_Automaton, _List}, b : {_Automaton, _List}] :>
				With[{m = OrAutomaton[a, b, numerationsystem, Minimize -> minimize, Monitor -> monitor]},
(*
Print[Or];
Print[Tab, a];
Print[Tab, b];
Print[Tab, m];
*)
(*
If[!MatchQ[m, {_Automaton, _List}],
	Print[Style["problem in OrAutomaton", Red]]
];
*)
					If[information,
						AppendTo[statecounts, AutomatonStateCount[First[m]]]
					];
					If[monitor,
						completedconstructioncount++
					];
					m
				],
			not[a : {_Automaton, _List}] :> NotAutomaton[a],
			(x_symbol == c_Integer?NonNegative) | (c_Integer?NonNegative == x_symbol) :> {ConstantAutomaton[c, numerationsystem], {x}},
			x_symbol == y_symbol :> {EqualAutomaton[numerationsystem], {x, y}},
(* TODO Does this help at all?
			z_symbol == plus[x_symbol, y_symbol] :> plus[x, y] == z,
*)
			(* TODO This doesn't support base Tribonacci. *)
			plus[x_symbol, y_symbol] == z_symbol :> {PlusAutomaton[numerationsystem], {x, y, z}},
			synchronizedsequence[m_][x__symbol] == y_symbol :> {m, {x, y}},
			times[c_, x_symbol] == y_symbol :>
				(* TODO This doesn't support base Fibonacci. *)
				With[{timesautomaton = TimesAutomaton[c, numerationsystem]},
(*
Print[Times];
*)
					{timesautomaton, {x, y}} /; !MatchQ[timesautomaton, _TimesAutomaton] || Message[ReduceAutomaton::times, numerationsystem]
				]
(* TODO Do I really need the  times  wrapper, or can I use this rule instead?
			(c_Integer /; c >= 2) x_ :> TimesAutomaton[c, x]
*)
		};
		If[monitor, Monitor, List][
			expandedexpression = expandedexpression //.
				with[rule_ /; FreeQ[rule, with], subexpression_] :>
					(subexpression /. (rule //. automatoncomputationrules));
			expandedexpression = expandedexpression //. automatoncomputationrules
			,
			Row[{"Number of completed automaton constructions: ", completedconstructioncount, " (of ", constructioncount, ")"}]
		];
		If[information,
			Print["Maximal state count (for a minimal automaton): ", Max[statecounts]];
		];
		(* The data in  expandedexpression  is now a {automaton,variablelist} pair (unless it matches  True | False ). *)
		(* Handle an explicit True or False expression. *)
		expandedexpression = Replace[expandedexpression,
			boolean : True | False :> {
				Automaton[
					(* TODO Are these edge patterns acceptable? *)
					{{1 -> 1, ConstantArray[_, Length[variables]]}},
					1,
					{1 -> boolean},
					(* The explicit InputAlphabet is (primarily?) to get through AutomatonPermute later. *)
					InputAlphabet -> Tuples[NumerationSystemDigitList[numerationsystem], Length[variables]]
				],
				symbol /@ variables
			}
		];
		If[MatchQ[expandedexpression, {_Automaton, _List}],
			{automaton, finalvariables} = expandedexpression;
			(* Permute the automaton according to the input variables list. *)
			automaton = AutomatonPermute[
				automaton,
				finalvariables,
				InversePermutation[Ordering[(Position[symbol /@ variables, #][[1, 1]] &) /@ finalvariables]]
			];
			(* Add blanks for free variables. *)
			automaton = AutomatonInputAlphabetInsert[
				automaton,
				numerationsystem,
				Position[symbol /@ variables, Alternatives @@ Complement[symbol /@ variables, finalvariables]],
				_
			];
			If[TrueQ[OptionValue[FlattenInputAlphabet]] && Length[variables] == 1,
				(* This isn't particularly general. *)
				automaton = Automaton[
					MapAt[First, 2] /@ automaton[[1]],
					automaton[[2]],
					automaton[[3]],
					InputAlphabet -> First /@ automaton[[4,2]]
				]
			]
		];
		False
	];
	automaton /; !failed && MatchQ[automaton, _Automaton] && SubsetQ[symbol /@ variables, finalvariables]
]
Options[ReduceAutomaton] = {FlattenInputAlphabet -> True, Information -> False, Minimize -> True, Monitor -> False}
SyntaxInformation[ReduceAutomaton] = {"ArgumentsPattern" -> {_, _, _., OptionsPattern[]}}
ReduceAutomaton::auto = "Unable to convert automatic sequence `1`."
ReduceAutomaton::quant = "Variables `1` are quantified too many times."
ReduceAutomaton::times = "Times automaton for base `1` is not implemented."

(*** end ReduceAutomaton code ***)


(* Compute a value of a sequence. *)
(sequence : RegularSequence[u_, matrixarray_, v_, ___]?RegularSequenceObjectQ)[n__Integer] :=
Module[{numerationsystemlist = RegularSequenceNumerationSystemList[sequence], digitlists, failed = False},
	If[Length[{n}] != Length[numerationsystemlist],
		failed = True
		,
		digitlists = MapThread[DigitList, {{n}, numerationsystemlist}];
		If[MemberQ[digitlists, _DigitList],
			failed = True
		]
	];
	Dot @@ Join[
		{u},
		matrixarray[[##]] & @@@
			Transpose[PadRight[digitlists] + 1],
		{v}
	] /; !failed
]
(* Compute multiple values of a one-dimensional sequence.  This allows faster computation. *)
(* TODO Maybe MapIndexed would be cleaner than MapThread here.  (It's the usual problem of inverting PolygonalNumber.) *)
(* TODO Support negative bases, other numeration systems. *)
(RegularSequence[u_, matrixlist_, v_, {base_Integer /; base >= 2}]?RegularSequenceObjectQ)[list : {_Integer?NonNegative, __Integer?NonNegative}] :=
Module[{length, zeromatrixpowers, i = -1, j},
	length = IntegerLength[Max[list], base];
	zeromatrixpowers = NestList[#.First[matrixlist] &, IdentityMatrix[Length[First[matrixlist]]], length - 1];
	(#.v &) /@ Nest[
		Function[vectors,
			i++;
			Join[
				vectors,
				Flatten[Outer[
					#2.#1 &,
					Rest[matrixlist],
					MapThread[Dot, {
						vectors,
						Prepend[
							Join @@ Table[
								ConstantArray[zeromatrixpowers[[i - j]], (base - 1) base^j],
								{j, 0, i - 1}
							],
							zeromatrixpowers[[i + 1]]
						]
					}],
				1], 1]
			]
		],
		{u},
		length
	][[list + 1]]
]
(* Compute multiple values of a multi-dimensional sequence. *)
(sequence_RegularSequence?RegularSequenceObjectQ)[list_List] :=
	(* This is inefficient in that it reapplies RegularSequenceObjectQ to the sequence for every entry in the list. *)
	sequence /@ list
SyntaxInformation[RegularSequence] = {"ArgumentsPattern" -> {_, _, _, _.}}

RegularSequenceGeneratorTable[sequence_RegularSequence, nmax_Integer?NonNegative] :=
	RegularSequenceGeneratorTable[sequence, {nmax}]
(* TODO This only evaluates for positive integer bases. *)
RegularSequenceGeneratorTable[sequence : RegularSequence[_, matrixarray_, v_, ___]?RegularSequenceObjectQ, {nmax__Integer?NonNegative}] :=
Module[{baselist, dimension, variables, failed},
	failed = Catch[
		baselist = RegularSequenceNumerationSystemList[sequence];
		dimension = Length[baselist];
		If[Length[{nmax}] != dimension || !MatchQ[baselist, {__Integer?(# >= 2 &)}],
			Throw[True]
		];
		variables = Table[Unique[], {dimension}];
		False
	];
	Transpose[
(* xxx probably this would be better with Outer than Table *)
		Table[
			Dot @@ Append[
				matrixarray[[##]] & @@@
					Transpose[PadRight[MapThread[DigitList, {variables, baselist}]] + 1],
				v
			],
			Evaluate[Sequence @@ Thread[{variables, 0, {nmax}}]]
		],
		RotateLeft[Range[dimension + 1]]
	] /; !failed
]
SyntaxInformation[RegularSequenceGeneratorTable] = {"ArgumentsPattern" -> {_, _}}

RegularSequenceMatrixForm[expr_] :=
	expr /. {
		sequence_?RegularSequenceObjectQ :>
			MapAt[
				Map[MatrixForm, #, {Length[RegularSequenceNumerationSystemList[sequence]]}] &,
				sequence,
				2
			],
		FindRegularSequenceFunction[array_, numerationsystemlist_, options : OptionsPattern[]] :>
(*
			FindRegularSequenceFunction[
				If[Length[list] >= 10,
					Append[Take[list, 10], Skeleton[Length[list] - 10]],
					{Skeleton[Length[list]]}
				],
				numerationsystemlist
			]
*)
			FindRegularSequenceFunction[Short[array], numerationsystemlist, options]
	}
SyntaxInformation[RegularSequenceMatrixForm] = {"ArgumentsPattern" -> {_}}

RegularSequenceMatrixLength[RegularSequence[u_, _, __]?RegularSequenceObjectQ] :=
	Length[u]
SyntaxInformation[RegularSequenceMatrixLength] = {"ArgumentsPattern" -> {_}}

(* TODO This only evaluates for positive integer bases. *)
(* TODO This would ideally figure out what the basis sequences are. *)
RegularSequenceRecurrence[
	sequence : RegularSequence[_, matrixarray_, v_, ___]?RegularSequenceObjectQ,
	a_[nsequence__?PlausibleVariableQ] /; FreeQ[a, Alternatives[nsequence]]
] :=
Module[{baselist, sequencedimension, basis, failed},
	failed = Catch[
		baselist = RegularSequenceNumerationSystemList[sequence];
		sequencedimension = Length[baselist];
		If[Length[{nsequence}] != sequencedimension || !MatchQ[baselist, {__Integer?(# >= 2 &)}],
			Throw[True]
		];
		basis = (Subscript[a, #][nsequence] &) /@ Range[Length[v]];
		False
	];
	Thread[{
		Transpose[
			MapIndexed[
				Function[{matrix, indices},
					Thread[(basis /. Thread[{nsequence} -> baselist {nsequence} + indices - 1]) == matrix.basis]
				],
				matrixarray,
				{sequencedimension}
			],
			Range[sequencedimension + 1, 1, -1]
		],
		Thread[(basis /. Alternatives[nsequence] -> 0) == v]
	}] /; !failed
]
SyntaxInformation[RegularSequenceRecurrence] = {"ArgumentsPattern" -> {_, _}}

(* TODO Check that n is a symbol or something simple like a[1].  If it's something like 3 n + 2 then the FreeQ checks in SequenceNumerationSystemList won't work as intended.
	Actually I'll need more general down values than these anyway, to make RudinShapiro[3 n + 2] and such work. *)
(* TODO These (except possibly for SternBrocot) were obtained from FindRegularSequenceFunction.  Are there better matrices? *)
RegularSequenceReduce[BaumSweet[n_], n_, {2}] /; PlausibleVariableQ[n] :=
	RegularSequence[{1, 0}, {{{0, 1}, {1, 0}}, {{1, 0}, {0, 0}}}, {1, 1}, 2][n]
RegularSequenceReduce[RudinShapiro[n_], n_, {2}] /; PlausibleVariableQ[n] :=
	RegularSequence[{1, 0}, {{{1, 0}, {1, 0}}, {{0, 1}, {0, -1}}}, {1, 1}, 2][n]
RegularSequenceReduce[ThueMorse[n_], n_, {2}] /; PlausibleVariableQ[n] :=
	RegularSequence[{1, 0}, {{{1, 0}, {0, 1}}, {{0, 1}, {1, 0}}}, {0, 1}, 2][n]
RegularSequenceReduce[SternBrocot[n_], n_, {2}] /; PlausibleVariableQ[n] :=
	RegularSequence[{1, 0}, {{{1, 0}, {1, 1}}, {{0, 1}, {-1, 2}}}, {0, 1}, 2][n]
RegularSequenceReduce[BitLength[n_], n_, {2}] /; PlausibleVariableQ[n] :=
	RegularSequence[{1, 0, 0}, {{{0, 1, 0}, {-1, 2, 0}, {-1, 1, 1}}, {{0, 0, 1}, {-1, 0, 2}, {-1, 0, 2}}}, {0, 0, 1}, 2][n]
RegularSequenceReduce[BitShiftRight[n_], n_, {2}] /; PlausibleVariableQ[n] :=
	RegularSequence[{1, 0, 0}, {{{0, 1, 0}, {0, 2, 0}, {0, 2, 1}}, {{0, 1, 0}, {0, 0, 1}, {0, -2, 3}}}, {0, 0, 1}, 2][n]
RegularSequenceReduce[DigitCount[n_, base_, 0], n_?PlausibleVariableQ, {base_Integer /; base >= 2}] :=
	RegularSequence[
		{1, 0, 0},
		Join[
			{{{0, 1, 0}, {-1, 2, 0}, {-1, 1, 1}}},
			ConstantArray[{{0, 0, 1}, {0, 1, 0}, {0, 0, 1}}, base - 1]
		],
		{1, 1, 0},
		base
	][n]
RegularSequenceReduce[
	DigitCount[n_, base_, d_Integer] /; 1 <= d <= base - 1,
	n_?PlausibleVariableQ,
	{base_Integer /; base >= 2}
] :=
	RegularSequence[
		{1, 0},
		ReplacePart[
			ConstantArray[IdentityMatrix[2], base],
			d + 1 -> {{0, 1}, {-1, 2}}
		],
		{0, 1},
		base
	][n]
RegularSequenceReduce[
	IntegerExponent[n_ + 1, base_],
	n_?PlausibleVariableQ,
	{base_Integer /; base >= 2}
] :=
	RegularSequence[
		{1, 0},
		Join[
			ConstantArray[{{0, 0}, {-1, 1}}, base - 1],
			{{0, 1}, {-1, 2}}
		],
		{0, 1},
		base
	][n]
RegularSequenceReduce[IntegerLength[n_], n_, {10}] /; PlausibleVariableQ[n] :=
	RegularSequenceReduce[IntegerLength[n, 10], n, {10}]
RegularSequenceReduce[
	IntegerLength[n_, base_],
	n_?PlausibleVariableQ,
	{base_Integer /; base >= 2}
] :=
	RegularSequence[
		{1, 0, 0},
		Join[
			{{{0, 1, 0}, {-1, 2, 0}, {-1, 1, 1}}},
			ConstantArray[{{0, 0, 1}, {-1, 0, 2}, {-1, 0, 2}}, base - 1]
		],
		{0, 0, 1},
		base
	][n]
(* TODO 2-argument forms of BitShiftRight; BitGet, BitSet, BitClear; BitAnd, BitOr, BitXor; DigitGet, DigitsCount *)
(* TODO Mod *)
(* TODO IntegerReverse *)
(* TODO IntegerPrepend ? *)
(* TODO BitShiftLeft and BitNot (and 2-argument BitShiftLeft) for general bases *)
RegularSequenceReduce[BitNot[n_], n_, {2}] /; PlausibleVariableQ[n] :=
	RegularSequence[{1, 0}, {{{0, 1}, {-2, 3}}, {{2, 0}, {2, 1}}}, {-1, -1}, 2][n]
RegularSequenceReduce[BitShiftLeft[n_], n_, {2}] /; PlausibleVariableQ[n] :=
	RegularSequence[{1, 0}, {{{2, 0}, {2, 1}}, {{0, 1}, {-2, 3}}}, {0, 2}, 2][n]
(* TODO
RegularSequenceReduce[
	0,
	n_?PlausibleVariableQ,
	(* TODO support multidimensional sequences *)
	{numerationsystem_?PositiveNumerationSystemQ}
] :=
	representation of the 0 sequence
*)
RegularSequenceReduce[
	expression_,
	n_?PlausibleVariableQ,
	(* TODO support multidimensional sequences *)
	{base_Integer /; base >= 2}
] /; FreeQ[expression, n] :=
	RegularSequence[{1}, ConstantArray[{{1}}, base], {expression}, base][n]
(* TODO polynomials *)
(* xxx need a version of this where the automaton doesn't have a flattened input alphabet *)
RegularSequenceReduce[
(* xxx do we need a AutomaticSequenceObjectQ analogous to RegularSequenceObjectQ? *)
	(sequence : AutomaticSequence[automaton_, ___])[n_],
	n_?PlausibleVariableQ,
	numerationsystemlist : {__?PositiveNumerationSystemQ}
] :=
Module[{statelist = AutomatonStateList[automaton], edges = First[automaton], stateindex},
	RegularSequence[
		UnitVector[Length[statelist], FirstPositionLevel1[statelist, automaton[[2]]]],
		Outer[
			Function[digitlist,
				SparseArray[
(* Similar code occurs in AutomatonMinimize.  Write a separate function for it? *)
					Table[
						FirstCase[
							edges,
							{statelist[[stateindex]] -> state_, label_ /; MatchQ[digitlist, label]} :>
(* Use PositionIndex here?
More generally, anywhere in the package I use FirstPosition on the same list multiple times, would it be faster to use PositionIndex? *)
								({stateindex, FirstPositionLevel1[statelist, state]} -> 1)
(*,  necessary?
							Message[AutomatonMinimize::undef, digitlist, state]; Throw[True]
*)
						],
						{stateindex, 1, Length[statelist]}
					],
					{Length[statelist], Length[statelist]}
				]
			],
			Sequence @@ NumerationSystemDigitList /@ numerationsystemlist
		],
		Replace[
			statelist,
			AutomatonOutputRules[automaton],
			{1}
		],
		Replace[numerationsystemlist, {numerationsystem_} :> numerationsystem]
	][n] /; AutomaticSequenceNumerationSystemList[sequence] === numerationsystemlist
]
RegularSequenceReduce[
(* TODO support more than 2 arguments? *)
	Plus[
		(sequencea : RegularSequence[ua_, matricesa_, va_, ___]?RegularSequenceObjectQ)[n_],
		(sequenceb : RegularSequence[ub_, matricesb_, vb_, ___]?RegularSequenceObjectQ)[n_]
	],
	n_?PlausibleVariableQ,
	numerationsystemlist : {__?PositiveNumerationSystemQ}
] :=
With[{dimension = ArrayDepth[matricesa] - 2},
	RegularSequence[
		Join[ua, ub],
		MapThread[
			Function[{ma, mb}, BlockDiagonalMatrix[{ma, mb}]],
			{matricesa, matricesb},
			dimension
		],
		Join[va, vb],
		Replace[numerationsystemlist, {numerationsystem_} :> numerationsystem]
	][n] /; dimension == ArrayDepth[matricesb] - 2 && numerationsystemlist === RegularSequenceNumerationSystemList[sequencea] === RegularSequenceNumerationSystemList[sequenceb]
]
(* TODO try to extract monomials into a single polynomial term? *)
RegularSequenceReduce[
	plus_Plus,
	n_?PlausibleVariableQ,
	numerationsystemlist : {__?PositiveNumerationSystemQ}
] :=
With[{regularsequences = RegularSequenceReduce[#, n, numerationsystemlist] & /@ List @@ plus},
	RegularSequenceReduce[Total[regularsequences], n, numerationsystemlist] /; MatchQ[regularsequences, {(_RegularSequence[n]) ..}]
]
RegularSequenceReduce[
(* TODO support more than 2 arguments *)
	Times[
		c_,
		(sequence_?RegularSequenceObjectQ)[n_]
	] /; FreeQ[c, n],
	n_?PlausibleVariableQ,
	(*numerationsystemlist :*) {__?PositiveNumerationSystemQ}
] :=
(* we haven't done
		Replace[numerationsystemlist, {numerationsystem_} :> numerationsystem]
to the fourth argument here
*)
	MapAt[c # &, sequence, 1]
RegularSequenceReduce[
(* TODO support more than 2 arguments *)
	Times[
		(sequencea : RegularSequence[ua_, matricesa_, va_, ___]?RegularSequenceObjectQ)[n_],
		(sequenceb : RegularSequence[ub_, matricesb_, vb_, ___]?RegularSequenceObjectQ)[n_]
	],
	n_?PlausibleVariableQ,
	numerationsystemlist : {__?PositiveNumerationSystemQ}
] :=
With[{dimension = ArrayDepth[matricesa] - 2},
	RegularSequence[
		Join @@ TensorProduct[ua, ub],
		MapThread[
			ArrayFlatten @* TensorProduct,
			{matricesa, matricesb},
			dimension
		],
		Join @@ TensorProduct[va, vb],
		Replace[numerationsystemlist, {numerationsystem_} :> numerationsystem]
	][n] /; dimension == ArrayDepth[matricesb] - 2 && numerationsystemlist === RegularSequenceNumerationSystemList[sequencea] === RegularSequenceNumerationSystemList[sequenceb]
]
RegularSequenceReduce[
	product_Times,
	n_?PlausibleVariableQ,
	numerationsystemlist : {__?PositiveNumerationSystemQ}
] :=
With[{regularsequences = RegularSequenceReduce[#, n, numerationsystemlist] & /@ List @@ product},
	RegularSequenceReduce[Times @@ regularsequences, n, numerationsystemlist] /; MatchQ[regularsequences, {(_RegularSequence[n]) ..}]
]
(* AutomaticSequenceReduce doesn't exist yet
RegularSequenceReduce[
(* TODO support more than 2 arguments? *)
	Power[
		x_,
(*
(* xxx do we need a AutomaticSequenceObjectQ analogous to RegularSequenceObjectQ? *)
		(sequence_AutomaticSequence)[n_]
*)
		ThueMorse[n_]
	],
	n_?PlausibleVariableQ,
(*
	numerationsystemlist : {__?PositiveNumerationSystemQ}
*)
	{2}
] /; FreeQ[x, n] :=
With[{automaticsequence = AutomaticSequenceReduce[ThueMorse[n], n, {2}]},
	Replace[
		AutomatonOutputRules[First[automaticsequence]],
		AutomatonOutputAlphabet[First[automaticsequence]] -> x^AutomatonOutputAlphabet[First[automaticsequence]]
	] /; !MatchQ[automaticsequence, _AutomaticSequenceReduce]
]
*)
RegularSequenceReduce[
	(sequence_RegularSequence?RegularSequenceObjectQ)[n_],
	n_?PlausibleVariableQ,
	numerationsystemlist : {__?PositiveNumerationSystemQ}
] :=
	sequence[n] /; numerationsystemlist === RegularSequenceNumerationSystemList[sequence]
RegularSequenceReduce[
	expression : _List | (Equal | Greater | GreaterEqual | Less | LessEqual | Unequal | Inequality)[__],
	n_?PlausibleVariableQ,
	numerationsystemlist : {__?PositiveNumerationSystemQ}
] :=
	RegularSequenceReduce[#, n, numerationsystemlist] & /@ expression
RegularSequenceReduce[expression_, n_?PlausibleVariableQ, numerationsystem : Except[_List]] :=
	RegularSequenceReduce[expression, n, {numerationsystem}]
RegularSequenceReduce[list_List, n_?PlausibleVariableQ] :=
	RegularSequenceReduce[#, n] & /@ list
RegularSequenceReduce[expression_, n_?PlausibleVariableQ] :=
With[{numerationsystemlist = SequenceNumerationSystemList[expression, n]},
	RegularSequenceReduce[expression, n, numerationsystemlist] /; !MatchQ[numerationsystemlist, _SequenceNumerationSystemList | Automatic]
]
SyntaxInformation[RegularSequenceReduce] = {"ArgumentsPattern" -> {_, _, _.}}

If[$VersionNumber < 10.2,
SetAttributes[RudinShapiro, Listable];
RudinShapiro[n_Integer?NonNegative] :=
	(-1)^DigitsCount[n, 2, {1, 1}];
SyntaxInformation[RudinShapiro] = {"ArgumentsPattern" -> {_}}
]

Options[SeriesRoot] = {Modulus -> 0}
SyntaxInformation[SeriesRoot] = {"ArgumentsPattern" -> {_, OptionsPattern[]}}

(* TODO AlgebraicSequence *)
SequenceComplexity[AutomaticSequence[automaton_, ___] | AutomaticSequence[automaton_, ___][__]] :=
	AutomatonStateCount[automaton]
(* TODO ConstantTermSequence *)
(* TODO DiagonalSequence *)
(* TODO MorphicSequence *)
SequenceComplexity[(RegularSequence[u_, _, __]?RegularSequenceObjectQ) | (RegularSequence[u_, _, __]?RegularSequenceObjectQ)[__]] :=
	Length[u]
SyntaxInformation[SequenceComplexity] = {"ArgumentsPattern" -> {_}}

SequenceRiffle[functions_List, var_] :=
With[{modulus = Length[functions]},
	Piecewise[MapIndexed[
		{
			#1 /. var -> (var + Mod[1 - First[#2], modulus])/modulus,
			Mod[var, modulus] == First[#2] - 1
		} &,
		RotateRight[functions]
	]]
]
SyntaxInformation[SequenceRiffle] = {"ArgumentsPattern" -> {{__}, _}}

SeriesSolve[True, _[x_], {x_, x0_, _Integer} /; FreeQ[x0, x], OptionsPattern[]] :=
	{{}}
SeriesSolve[False, _[x_], {x_, x0_, _Integer} /; FreeQ[x0, x], OptionsPattern[]] :=
	{}
SeriesSolve[equation_Equal, f_[x_], {x_, x0_, _Integer}, OptionsPattern[]] /;
	And[
		FreeQ[equation, f],
	 	FreeQ[x0, x]
	 ] :=
	{}
SeriesSolve[lhs_ == rhs_, f_[x_], {x_, x0_, seriesaccuracyminus1_Integer} /; FreeQ[x0, x], options : OptionsPattern[]] :=
Module[{polynomial, modulus, coefficientrules, y, failed},
	failed = Catch[
		If[!MatchQ[OptionValue[MaxDenominator], _Integer?Positive | Infinity],
			Message[SeriesSolve::maxd, OptionValue[MaxDenominator]]; Throw[True]
		];
		modulus = OptionValue[Modulus];
		If[!MatchQ[modulus, _Integer?NonNegative],
			Message[SeriesSolve::rmod, modulus]; Throw[True]
		];
(* There's less need for this if we support rational expressions (or series-expandable expressions) in x as coefficients of f[x]^i.
		polynomial = If[modulus == 0,
			(* Clear denominators to rewrite the equation as a polynomial equation if possible. *)
			(Denominator[#2] Numerator[#1] - Denominator[#1] Numerator[#2] &)[
				FragileTogether[lhs],
				FragileTogether[rhs]
			],
			lhs - rhs
		];
*)
		polynomial = lhs - rhs /. f[x] -> y;
		Quiet[
			Check[
				coefficientrules = CoefficientRules[polynomial, y, Modulus -> modulus],
				Message[SeriesSolve::nmod, lhs == rhs, modulus]; Throw[True],
				CoefficientRules::nmod
			],
			CoefficientRules::nmod
		];
		If[
			Or[
				!FreeQ[coefficientrules, y],
				!AllTrue[coefficientrules, PolynomialQ[Last[#], x] &]
			],
			Message[SeriesSolve::poly, lhs == rhs, x, f[x]]; Throw[True]
		];
		False
	];
	{f[x] -> #} & /@ SeriesRootSeriesList[{{y, polynomial}, {0, -Infinity}}, {x, x0, seriesaccuracyminus1}, options] /;
		!failed
]
Options[SeriesSolve] = {MaxDenominator -> Infinity, Method -> Automatic, Modulus -> 0}
SyntaxInformation[SeriesSolve] = {"ArgumentsPattern" -> {_, _, _, OptionsPattern[]}}
SeriesSolve::maxd = "Max denominator `1` must be a positive integer or \[Infinity]."
SeriesSolve::poly = "`1` must be a polynomial equation in `2` and `3`."
SeriesSolve::rmod = "Modulus `1` must be a non\[Hyphen]negative integer."
SeriesSolve::soln = "Unable to extend `1` to a solution. Possibly a non\[Hyphen]zero numeric quantity was assumed to be zero."

SetAttributes[SternBrocot, Listable]
SternBrocot[n_Integer?NonNegative] :=
	RegularSequence[{1, 0}, {{{1, 0}, {1, 1}}, {{0, 1}, {-1, 2}}}, {0, 1}, 2][n]
SyntaxInformation[SternBrocot] = {"ArgumentsPattern" -> {_}}

SynchronizedSequenceReduce[
	sequence : AutomaticSequence[inputautomaton_?AutomatonQ(*, XXX optional numeration system *)][nsequence__],
	{nsequence__?PlausibleVariableQ},
(* TODO Allow this argument to be optional and get the numeration system from the automatic sequence. *)
	base_Integer /; base >= 2,
	OptionsPattern[]
] :=
Module[
	{
		inputalphabet, sequencedimension, automaton, statelist, outputalphabet, liftedautomaton, maxoutputvaluelength, edgeunion, outputrulesunion, synchronizedautomaton,
		outputvalue, state, absorbingstate, outputvaluedigitlist, failed
	},
	failed = Catch[
		inputalphabet = AutomatonInputAlphabet[inputautomaton];
		If[MatchQ[inputalphabet, _AutomatonInputAlphabet],
			Message[SynchronizedSequenceReduce::input]; Throw[True]
		];
		sequencedimension = Length[{nsequence}];
		(* Add explicit output rules and input alphabet. *)
		Switch[Sort[inputalphabet],
			Range[0, base - 1] /; sequencedimension == 1,
				automaton = Automaton[
					MapAt[List, 2] /@ inputautomaton[[1]],
					inputautomaton[[2]],
					AutomatonOutputRules[inputautomaton],
					InputAlphabet -> Tuples[Range[0, base - 1], sequencedimension]
				],
			Tuples[Range[0, base - 1], sequencedimension],
				automaton = Automaton[
					inputautomaton[[1]],
					inputautomaton[[2]],
					AutomatonOutputRules[inputautomaton],
					InputAlphabet -> Tuples[Range[0, base - 1], sequencedimension]
				],
			_,
				Message[SynchronizedSequenceReduce::inalph, inputalphabet, base]; Throw[True]
		];
		statelist = AutomatonStateList[automaton];
		outputalphabet = AutomatonOutputAlphabet[automaton];
		If[!MatchQ[outputalphabet, {__Integer?NonNegative}],
			Message[SynchronizedSequenceReduce::outalph, outputalphabet]; Throw[True]
		];
(* This could be the minimum length that distinguishes between all the output values.  That would be more efficient in cases when the output values have very different lengths.
   Would we need to change anything below?  Yeah, we'd have to keep reading to make sure the output is actually the one that is determined by the length.  So would it actually be more efficient? *)
		maxoutputvaluelength = Max[IntegerLength[outputalphabet, base]];
		liftedautomaton = AutomatonInputAlphabetInsert[automaton, base, {{sequencedimension + 1}}, 0];
		(* Make one copy of the automaton for each letter in the output alphabet.
		   After reading enough digits of the supposed output value to know which value it is, we stay in the corresponding automaton.
		   Before that, we create a state for each possible input (using the  state  wrapper). *)
		{edgeunion, outputrulesunion} = Join @@@ Transpose[Table[
			(* Rename the states in this automaton copy so they are unique. *)
			Replace[
				AutomatonStateReplace[
					(* Change the output rules so that a state outputs  True  precisely when it previously output  outputvalue . *)
					(* This uses the fact that we've arranged  liftedautomaton  to have output rules in its third argument. *)
					ReplacePart[
						liftedautomaton,
						Rule[
							3,
							Function[s, s -> Replace[s, liftedautomaton[[3]]] === outputvalue] /@ statelist
						]
					],
					s_ :> {s, outputvalue}
				],
				Automaton[edges_, _, outputrules_, ___Rule] :>
					{
						Join[
							outputvaluedigitlist = DigitList[outputvalue, base, maxoutputvaluelength];
							(* Connect states at level maxoutputvaluelength-1 to the correct automaton copy. *)
							Function[inputvaluedigitlists,
								{
									state[Most /@ Append[inputvaluedigitlists, outputvaluedigitlist]] -> {
										(* This uses the fact that we've arranged the input alphabet to consist of lists of digits, not digits. *)
										Take[automaton, 2][Transpose[inputvaluedigitlists]],
										outputvalue
									},
									Last /@ Append[inputvaluedigitlists, outputvaluedigitlist]
								}
							] /@ Tuples[Range[0, base - 1], {sequencedimension, maxoutputvaluelength}],
							edges
						],
						outputrules
					}
			],
			{
				outputvalue,
				outputalphabet
			}
		]];
		synchronizedautomaton = Automaton[
			DeleteDuplicatesBy[
				Join[
					(* Generate out-edges for all states up through level  maxoutputvaluelength - 2 . *)
					(* But in fact once we've read enough of the last component to know that it doesn't correspond to any output value, then we could move to  absorbingstate .
					   If I do that, then I may need to apply AutomatonPadRight to the origial input automaton; see discussion. *)
					Function[digitlists,
						{state[Most /@ digitlists] -> state[digitlists], Last /@ digitlists}
					] /@
						Join @@ Function[length,
							Tuples[Range[0, base - 1], {sequencedimension + 1, length}]
						] /@
							Range[1, maxoutputvaluelength - 1],
					edgeunion,
					(* Connect relevant states at level  maxoutputvaluelength - 1  to the terminal rejecting state. *)
					(* This only connects states at level  maxoutputvaluelength - 1  since above we generated out-edges for all earlier states.
					   TODO This is somewhat inefficient; it generates all edges and then relies on DeleteDuplicatesBy. *)
					Function[digitlists,
						{state[Most /@ digitlists] -> absorbingstate, Last /@ digitlists}
					] /@
						Tuples[Range[0, base - 1], {sequencedimension + 1, maxoutputvaluelength}],
					{{absorbingstate -> absorbingstate, ConstantArray[_, sequencedimension + 1]}}
				],
				MapAt[First, 1]
			],
			state[ConstantArray[{}, sequencedimension + 1]],
			Join[
				Select[
					Function[inputvalues,
						state[PadRight[DigitList[#, base] & /@ Append[inputvalues, AutomaticSequence[automaton] @@ inputvalues]]] -> True
					] /@
						Tuples[Range[0, base^(maxoutputvaluelength - 1) - 1], sequencedimension],
					Length[#[[1, 1, 1]]] <= maxoutputvaluelength - 1 &
				],
				outputrulesunion,
				(* TODO Do I want to list the rejecting states explicitly here instead of determinizing below? *)
				{_ -> False}
			],
			(* Including this is necessary for use in ReduceAutomaton, but for other applications it may be unnecessary. *)
			InputAlphabet -> Tuples[Range[0, base - 1], sequencedimension + 1]
		];
		(* Determinizing is necessary for use in ReduceAutomaton because the automaton may get passed to AutomatonProduct. *)
		(* Note that this applies IndexAutomaton; if we don't then the automaton contains private symbols  state  and  absorbingstate . *)
		synchronizedautomaton = AutomatonDeterminize[
			synchronizedautomaton,
			Or @@ # &,
			Minimize -> OptionValue[Minimize]
		];
		False
	];
	SynchronizedSequence[synchronizedautomaton][nsequence] /; !failed
]
SynchronizedSequenceReduce[
	originalsequence_[n_],
	n_?PlausibleVariableQ,
(* TODO Allow this argument to be optional and get the numeration system from the automatic sequence. *)
	base_Integer /; base >= 2,
	options : OptionsPattern[]
] :=
With[{sequence = SynchronizedSequenceReduce[originalsequence[n], {n}, base, options]},
	sequence /; !MatchQ[sequence, _SynchronizedSequenceReduce]
]
Options[SynchronizedSequenceReduce] = {Minimize -> True}
SyntaxInformation[SynchronizedSequenceReduce] = {"ArgumentsPattern" -> {_, _, _., OptionsPattern[]}}
SynchronizedSequenceReduce::inalph = "Input alphabet `1` must be a list of base\[Hyphen]`2` digits."
SynchronizedSequenceReduce::input = "Unable to determine the input alphabet."
SynchronizedSequenceReduce::outalph = "Output alphabet `1` must be a list of non\[Hyphen]negative integers."

(*
SynchronizedSequence[automaton_?AutomatonQ][n__Integer?NonNegative] :=
*)
SyntaxInformation[SynchronizedSequence] = {"ArgumentsPattern" -> {_}}

If[$VersionNumber < 10.2,
SetAttributes[ThueMorse, Listable];
ThueMorse[n_Integer?NonNegative] :=
	Mod[DigitCount[n, 2, 1], 2];
SyntaxInformation[ThueMorse] = {"ArgumentsPattern" -> {_}}
]

SyntaxInformation[TransitionSequence] = {"ArgumentsPattern" -> {___}}


(*** Tribonacci code ***)

(* If we don't cache values, then identifying Tribonacci-regularity of sequences is really slow. *)
TN[n_] := TN[n] = MatrixPower[{{1, 1, 1}, {1, 0, 0}, {0, 1, 0}}, n - 2][[1, 1]]

SetAttributes[Tribonacci, Listable]
Tribonacci[n_Integer] :=
	TN[n]
SyntaxInformation[Tribonacci] = {"ArgumentsPattern" -> {_}}

(*** end Tribonacci code ***)



End[]

Protect["IntegerSequences`*"]
Unprotect[$CacheMotzkinNumbers]
Unprotect[$MotzkinNumberDirectory]

EndPackage[]
