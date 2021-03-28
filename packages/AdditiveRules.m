(* :Title: Additive Rules *)

(* :Context: AdditiveRules` *)

(* :Author: Eric Rowland *)

(* :Date: {2010, 2, 8} *)

(* :Package Version: .92 *)

(* :Mathematica Version: 6 *)

(* :Discussion:
	AdditiveRules is a package for studying additive cellular automaton rules over a commutative monoid.
	Documentation can be found at  https://ericrowland.github.io/packages.html .
*)


BeginPackage["AdditiveRules`"]

AdditionMonoid::usage =
"AdditionMonoid[k] gives the number of the monoid which represents addition modulo k."

AdditionTable::usage =
"AdditionTable[k, m] gives the addition table of the k\[Hyphen]element groupoid number m."

AdditiveQ::usage =
"AdditiveQ[{n, k, r}, m] yields True if the k\[Hyphen]color, radius r rule n is additive with respect to commutative monoid number m, and False otherwise.
AdditiveQ[{n, k, r}] uses addition modulo k."

AdditiveRule::usage =
"AdditiveRule[k, r] gives the k\[Hyphen]color, radius r rule that represents addition modulo k.
AdditiveRule[k, r, m] gives the rule that represents the addition of the commutative monoid number m.
AdditiveRule[k, {f_1, f_2, ..., f_(2r+1)}, m] uses weight functions f_1, f_2, ... (given as integers to be interpreted as lists of their base\[Hyphen]k digits) that distribute over the operation of monoid number m."

AdditiveRules::usage =
"AdditiveRules[k, r] lists the k\[Hyphen]color, radius r rules that are additive modulo k.
AdditiveRules[k, r, m] lists the rules that are additive with respect to commutative monoid number m.
AdditiveRules[k, r, All] lists every rule that is additive with respect to some k\[Hyphen]element commutative monoid."

AssociativeGroupoidQ::usage =
"AssociativeGroupoidQ[k, g] yields True if the k\[Hyphen]element groupoid number g is associative, and False otherwise.
AssociativeGroupoidQ[additiontable] determines g from its k\[Times]k addition table."

CommutativeGroupoidQ::usage =
"CommutativeGroupoidQ[k, g] yields True if the k\[Hyphen]element groupoid number g is commutative, and False otherwise.
CommutativeGroupoidQ[additiontable] determines g from its k\[Times]k addition table."

CommutativeMonoidQ::usage =
"CommutativeMonoidQ[k, g] yields True if the k\[Hyphen]element groupoid number g is a commutative monoid, and False otherwise.
CommutativeMonoidQ[additiontable] determines g from its k\[Times]k addition table."

CommutativeMonoids::usage =
"CommutativeMonoids[k] finds the k\[Hyphen]element commutative monoids with identity element 0 and the further restriction that a\[CirclePlus]a \[LessEqual] a+1 in the addition of the monoid.
(This implementation is only practical for k \[LessEqual] 5.)"

DistributiveQ::usage =
"DistributiveQ[k, g, f] yields True if the function number f on Range[0, k-1] preserves the operation of the commutative k\[Hyphen]element groupoid number g, and False otherwise.
DistributiveQ[additiontable, valuelist] determines g from its k\[Times]k addition table and f from its list of values."

EquivalentGroupoids::usage =
"EquivalentGroupoids[k, g] gives an unsorted list of all groupoids that are equivalent to the k\[Hyphen]element groupoid number g under a permutation of elements.
EquivalentGroupoids[additiontable] determines g from its k\[Times]k addition table."

GroupoidClass::usage =
"GroupoidClass[k, g] gives the representative k\[Hyphen]element groupoid in the equivalence class of groupoid number g.
GroupoidClass[additiontable] determines g from its k\[Times]k addition table."

GroupoidNumber::usage =
"GroupoidNumber[additiontable] gives the number of the k\[Hyphen]element groupoid defined by the given k\[Times]k addition table."

GroupoidQ::usage =
"GroupoidQ[k, g] yields True if the k\[Hyphen]element object number g is a groupoid (i.e., has no two identical elements), and False otherwise.
GroupoidQ[additiontable] determines g from its k\[Times]k addition table."

IdentityElement::usage =
"IdentityElement[k, m] gives the identity element of the k\[Hyphen]element commutative monoid number m.
IdentityElement[additiontable] determines m from its k\[Times]k addition table.
If m is not a commutative monoid, IdentityElement[k, m] gives the left identity elements."

InequivalentCommutativeMonoids::usage =
"For k \[LessEqual] 6, InequivalentCommutativeMonoids[k] lists representatives of the inequivalent k\[Hyphen]element commutative monoids.
(Representatives are chosen so that 0 is the identity element.)"

MonoidClass::usage =
"MonoidClass[k, m] gives the representative k\[Hyphen]element monoid in the equivalence class of commutative monoid number m.
MonoidClass[additiontable] determines m from its k\[Times]k addition table."

SortGroupoids::usage =
(*
"SortGroupoids[k, list] sorts a list of k\[Hyphen]element groupoid numbers by the directed graphs of their addition table diagonals (and then lexicographically)."
*)
"SortGroupoids[k, list] sorts a list of k\[Hyphen]element groupoid numbers lexicographically by addition tables."

WeightFunctions::usage =
"WeightFunctions[k, m] lists the function numbers f which distribute over the addition of the k\[Hyphen]element commutative groupoid number m.
WeightFunctions[k] uses addition modulo k.
WeightFunctions[additiontable] determines m from its k\[Times]k addition table."


(*
CanonicalForest::usage =
"CanonicalForest[list] gives the canonical representation of the given (unlooped) oriented forest (in pointer code) on nodes {0, 1, ..., Length[list]-1}, where the roots point to -1."

CanonicalTree::usage =
"CanonicalTree[tree] gives the canonical representation of an unlabelled rooted tree in nested form."

FromPointerCode::usage =
"FromPointerCode[list] gives the unlabelled rooted tree with the given pointer code in nested form."

LevelCode::usage =
"LevelCode[tree] gives the level code (in preorder traversal) of the given unlabelled rooted tree in nested form."

PointerCode::usage =
"PointerCode[tree] gives the pointer code of the given unlabelled rooted tree in nested form."

UnloopGraph::usage =
"UnloopGraph[list] gives the spanning forest obtained by unlooping the cycles in the given graph in pointer code."
*)


Unprotect["AdditiveRules`*"]

Begin["`Private`"]

CanonicalRotation[{}, p_:1] := {}
CanonicalRotation[list_List] :=
	First[Sort[NestList[RotateLeft, list, Length[list] - 1]]]
CanonicalRotation[list_List, p_] :=
	First[Sort[NestList[RotateLeft, list, Length[list] - 1], p]]
(* TODO Use this modern version?
CanonicalRotation[list : _[]] :=
	list
CanonicalRotation[list : _[__]] :=
	FirstSortedElement[
		RotateLeft[list, #[[1]] - 1] & /@
			Position[list, FirstSortedElement[list], {1}, Heads -> False]
	]
CanonicalRotation[list : _[__], p_] :=
	FirstSortedElement[
		NestList[RotateLeft, list, Max[0, Length[list] - 1]],
		p
	]

FirstSortedElement[list : _[__]] :=
	list[[First[Ordering[list, 1]]]]
FirstSortedElement[list : _[__], p_] :=
	list[[First[Ordering[list, 1, p]]]]
*)

ClassifyBy[list_List, f_] :=
	({#[[1,1]], #[[2]]} &) /@ Transpose /@
		Split[Sort[({f[#], #} &) /@ list], Equal @@ First /@ {##} &]
(* TODO Use this modern version?
ClassifyBy[list_List, f_ : Identity, g_ : Identity, h_ : Identity] :=
	Last[Reap[Sow[g[#], {f[#]}] & /@ list, _, {h[#2], #1} &]]
*)

FixedPointPeriod[f_, expr_, n_:Infinity] :=
Module[{list = {expr}, val = expr, i = 0},
	While[
		! MemberQ[list, val = f[val], {1}] && i <= n,
		AppendTo[list, val]; i++
	];
	If[i <= n,
		Take[list, {Position[list, val, {1}, 1][[1,1]], -1}],
		{}
	]
]

PartitionAt[list_List, {}] := {list}
PartitionAt[list_List, n_Integer] := PartitionAt[list, {n}]
PartitionAt[list_List, positions_List] :=
With[{el = Min[positions]},
	Join[
		{Take[list, el]},
		PartitionAt[Take[list, el - Length[list]], DeleteCases[positions - el, 0, 1, 1]]
	]
]

ToRule[n_Integer?NonNegative /; n < 256] := {n, 2, 1}
ToRule[{n_Integer?NonNegative, k : (_Integer?Positive) : 2, r : (_?NonNegative) : 1} /; IntegerQ[2 r] && n < k^k^(2 r + 1)] := {n, k, r}

ValidRuleQ[rule_] := MatchQ[ToRule[rule], {_, _, _}]
(*
ValidRuleQ[{n_, k_, s_}] :=
	Element[{n, k, s}, Integers] && k >= 1 && s >= 1 && 0 <= n < k^k^s
*)


InequivalentCommutativeMonoids[1] = {1};
InequivalentCommutativeMonoids[2] = {6, 14};
InequivalentCommutativeMonoids[3] = {19488, 10578, 17139, 13008, 8229};
InequivalentCommutativeMonoids[4] = {2947211748, 4020953572, 3219841508, 458142180, 1260302820, 3152982500, 1465275876,
	2539017700, 3612759524, 3885389284, 3613808100, 2812696036, 3886437860, 3085325796, 2268485092, 2144785892, 2145834468,
	1532667364, 2675631588};
InequivalentCommutativeMonoids[5] = {150156204227896680, 209760849003287305, 269365493778677930, 281305496220084180,
	269369308475943555, 221704666141959180, 281309310917349805, 233644668583365430, 178804592899771680, 178808407597037305,
	152541160282584180, 214537626347037305, 18522598269302930, 66191055300552930, 149679519656021680, 233167984011490430,
	74791969309084180, 134396614084474805, 253605903635256055, 86731971750490430, 146336616525881055, 205941261301271680,
	277485908518068555, 134400428781740430, 253609718332521680, 146340431223146680, 253613533029787305, 217888893137209180,
	277493537912599805, 229828895578615430, 267930097971193555, 279870100412599805, 279873915109865430, 255997724924318555,
	279877729807131055, 220273849191896680, 279878493967287305, 232213851633302930, 184457656564943555, 253613533273927930,
	217888893381349805, 277493538156740430, 229828895822756055, 279877730051271680, 148725387521974805, 208330032297365430,
	267934677072756055, 279874679514162305, 267938491770021680, 220273849436037305, 279878494211427930, 232213851877443555,
	184457656809084180, 177373776193849805, 177377590891115430, 151110343576662305, 213106809641115430, 119195063797365430,
	119198878494631055, 119202693191896680, 119203457352052930, 119202693436037305, 119199642898927930, 119203457596193555,
	119200407059084180, 119198114822756055, 80515860915334180, 140120505690724805, 80515861159474805, 82900053054006055,
	142504697829396680, 202597623612599805, 202597623856740430, 75268959106427930, 135841015506818555, 92933464725959180,
	140601921757209180, 205464118576052930};
InequivalentCommutativeMonoids[6] =
{4130412538048399276402811190, 5849483337796821867431469366,
9287624937293667049488785718, 4416961183659756497133904182,
6136031983408179088162562358, 7855102783156601679191220534,
9860722228516381490950971702, 5849489478739036332246966582,
9287631078235881514304282934, 6136038124350393552978059574,
9287637219178095979119780150, 8141663710652387829553307958,
9860734510400810420581966134, 8428212356263745050284400950,
9621925550354432898579833142, 9908474195965790119310926134,
9908480336908004584126423350, 9335389186627504607479734582,
9908486477850219048941920566, 8189416701723787239224779062,
9908487501472209830253437238, 8475965347335144459955872054,
9287637219200032929760158006, 8141663710674324780193685814,
9860734510422747371222343990, 8428212356285682000924778806,
9908486477872155999582298422, 6183791115443729913289908534,
7902861915192152504318566710, 9621932714940575095347224886,
9908481360551932316078317878, 9621938855882789560162722102,
8189416701745724189865156918, 9908487501494146780893815094,
8475965347357081410596249910, 6852392341565261611472003382,
6852398482507476076287500598, 6231544106515129322961379638,
7998379155597389471980986678, 5157190360560586806307463478,
5157196501502801271122960694, 5157202642445015735938457910,
5157203666067006517249974582, 5157202642466952686578835766,
5157197525146729003074855222, 5157203666088943467890352438,
5157198548768719784386371894, 4241836183574586752209658166,
5960906983323009343238316342, 4241836183596523702850036022,
4289588151045932331209990454, 6008658950794354922238648630,
7735706834457447284617257270, 7735706834479384235257635126,
4138371369743750233259811126, 5873380985470526069678317878,
4536344513921554710421152054, 5968872809000834545534214454,
4129086122960362905882783030, 6134711709262357182458031414,
8426885941175708679764372790, 452136587039130983134850358,
1884664882118410818247912758, 8474638932247108089435843894,
4129086122982299856523160886, 8426885941197645630404750646,
452136587061067933775228214, 1884664882140347768888290614,
6182464700355693542769880374, 8474638932269045040076221750,
452136587042787611759897910, 1884664882122067446872960310,
4176839114035418944179301686, 8474638932250764718060891446,
412342427663082530320379190, 1844870722742362365433441590,
4137044954655713862739782966, 4423594453306721517406562358,
8434845625910710070557059126, 4535018098832908993213409334,
5967546393912188828326471734, 4312170807831721356858894390,
2063769269592337179720994230, 3782840069340759770749652406,
8940052468586027543835626934, 2350317915203694400452087222,
4069388714952116991480745398, 5788459514700539582509403574,
7507530314448962173538061750, 9799698405420099206028905910,
3782846210282974235565149622, 5501917010031396826593807798,
8940058609528242008651124150, 4069394855894331456296242614,
5788465655642754047324900790, 4355943501505688677027335606,
8940070891412670938282118582, 8080646028498320009446739382,
9799716828246742600475397558, 8367194674109677230177832374,
2398069882653103028812041654, 4117140682401525619840699830,
5836211482149948210869358006, 2111527377983960272896445878,
3830598177732382863925104054, 5549668977480805454953762230,
2398076023595317493627538870, 4117146823343740084656197046,
5836217623092162675684855222, 7841837068451942487444606390,
2111539659868389202527440310, 3830610459616811793556098486,
5549681259365234384584756662, 8128397995947728637806693814,
9608653694707559242017721782, 9895202340318916462748814774,
9035562544427059265371033014, 9608659835649773706833218998,
9895214622203345392379809206, 9035574826311488195002027446,
9895220763145559857195306422, 2398070906275093810123558326,
4117141706023516401152216502, 3830599201354373645236620726,
4117147846965730865967713718, 6122773433267725142542962102,
8176152010641118828789681590, 9895222810389541419818339766,
8462700656252476049520774582, 3782846210304911186205527478,
8940058609550178959291502006, 4069394855916268406936620470,
8940070891434607888922496438, 8080646028520256960087117238,
9799716828268679551115775414, 8367194674131614180818210230,
4117146823365677035296574902, 3830610459638748744196476342,
8128397995969665588447071670, 4117147846987667816608091574,
8940070891456544839562874294, 8080646028542193910727495094,
9799716828290616501756153270, 8367194674153551131458588086,
9895220763189433758476062134, 6170526424382998453495188918,
7889597224131421044523847094, 9608668023879843635552505270,
9895216669491200856283598262, 9608674164822058100368002486,
8176152010684992730070437302, 9895222810433415321099095478,
8462700656296349950801530294, 6839127650504530151677283766,
6839133791446744616492780982, 6218279415454397863166660022,
7985114464536658012186267062, 9282311742756756720470511030,
9855409033979471161932697014, 9855415174921685626748194230,
8995781519972042894185909686, 9855427456806114556379188662,
9903161001428879790292651446, 9903167142371094255108148662,
9043533487421451522545864118, 9903179424255523184739143094,
9903162025050870571604168118, 9903168165993085036419665334,
9903174306935299501235162550, 8948031599766615828448988598,
9903181471499504747362176438, 9903167142393031205748526518,
9043533487443388473186241974, 9903179424277460135379520950,
9616619520403664766328950198, 9903168166015021987060043190,
8948029552566508167106710966, 9807675489400579829299989942,
9903179424299397086019898806, 8948025458868275264914247094,
9234574104479632485645340086, 8948031599810489729729744310,
9616626684989806963096341942, 9903175330601164183827434934,
9616632825932021427911839158, 9903181471543378648642932150,
8948026482490266046225763766, 9903176354223154965138951606,
8136357851261413747350162870, 9855428651009836338378821046,
8422906496872770968081255862, 9903180618459244966738775478,
8184110842332813157021633974, 9903181642081235748050292150,
8470659487944170377752726966, 7037922400829598738912759222,
8184110842354750107662011830, 9903181642103172698690670006,
8470659487966107328393104822, 7037922400851535689553137078,
8088604860233888238959447478, 9807675659982310829988105654,
8375153505845245459690540470, 9903179594881128086708014518,
8184110842376687058302389686, 9903181642125109649331047862,
8470659487988044279033482678, 7037922400873472640193514934,
8430866181604725076936609206, 6178485256078349410352188854,
7897556055826772001380847030, 9616626855575194592409505206,
9903175501186551813140598198, 9616632996517409057225002422,
8184110842380343686927437238, 9903181642128766277956095414,
8470659487991700907658530230, 7037922400877129268818562486,
6847086482199881108534283702, 6847092623142095573349780918,
6226238247149748820023659958, 7993073296232008969043266998,
8940070891456544917927038390, 8080646028542193989091659190,
9799716828290616580120317366, 8367194674153551209822752182,
9895220763189433836840226230, 6170526424382998531859353014,
7889597224131421122888011190, 9608668023879843713916669366,
9895216669491200934647762358, 9608674164822058178732166582,
8176152010684992808434601398, 9895222810433415399463259574,
8462700656296350029165694390, 6839127650504530230041447862,
6839133791446744694856945078, 6218279415454397941530824118,
7985114464536658090550431158, 9903179424299397164384062902,
3790813059623007570192436662, 8948025458868275343278411190,
8948031599810489808093908406, 9616626684989807041460506038,
9903175330601164262191599030, 9616632825932021506276003254,
9903181471543378727007096246, 3790814083244998351503953334,
8948026482490266124589927862, 9903176354223155043503115702,
3814690066574888334135463350, 8184110842376687136666553782,
9903181642125109727695211958, 8470659487988044357397646774,
7037922400873472718557679030, 4125106678683018851829255606,
5844177478431441442857913782, 9282319077928286624915230134,
4411655324294376072560348598, 6130726124042798663589006774,
7849796923791221254617664950, 9855416369151001066377416118,
5844183619373655907673410998, 9282325218870501089730727350,
6130732264985013128404503990, 9282331359812715554546224566,
8136357851287007404979752374, 9855428651035429996008410550,
8422906496898364625710845366, 9616619690989052474006277558,
9903168336600409694737370550, 9903174477542624159552867766,
9330083327262124182906178998, 9903180618484838624368364982,
8184110842358406814651223478, 9903181642106829405679881654,
8470659487969764035382316470, 7037922400855192396542348726,
9282331359834652505186602422, 8136357851308944355620130230,
9855428651057366946648788406, 8422906496920301576351223222,
9903180618506775575008742838, 6178485256078349488716352950,
7897556055826772079745011126, 9616626855575194670773669302,
9903175501186551891504762294, 9616632996517409135589166518,
8184110842380343765291601334, 9903181642128766356320259510,
8470659487991700986022694326, 7037922400877129347182726582,
6847086482199881186898447798, 6847092623142095651713945014,
6226238247149748898387824054, 7993073296232009047407431094,
5151884501195206381733907894, 5151890642137420846549405110,
5151896783079635311364902326, 5151897806701626092676418998,
5151896783101572262005280182, 5151891665781348578501299638,
5151897806723563043316796854, 5151892689403339359812816310,
5151888594937313185207127478, 4236530324209206327636102582,
5955601123957628918664760758, 4236530324231143278276480438,
4284282291680551906636434870, 6003353091428974497665093046,
7730400975092066860043701686, 7730400975114003810684079542,
4133065510378369808686255542, 5868075126105145645104762294,
4531038654556174285847596470, 5963566949635454120960658870,
7833878066145630226506698166, 3438112140348551488301313462,
3438118281290765953116810678, 3438130563175194882747805110,
3438113163970542269612830134, 3438119304912756734428327350,
3438125445854971199243824566, 3438132610419176445370838454,
3438118281312702903757188534, 3438130563197131833388182966,
3438119304934693685068705206, 3438130563219068784028560822,
3438126469520835881836096950, 3438132610463050346651594166,
3438127493142826663147613622, 3438131757378916664747437494,
3438132781000907446058954166, 3438132781022844396699332022,
3438130733800799784716676534, 3438132781044781347339709878,
3438126640106223511149260214, 3438132781048437975964757430,
3438127663728214292460776886, 3438123569262188117855088054,
3438130563219068862392724918, 3438126469520835960200261046,
3438132610463050425015758262, 3438127493142826741511777718,
3438132781044781425703873974, 3438119475520081392746032566,
3438125616462295857561529782, 3438131757404510322377026998,
3438132781026501103688543670, 3438131757426447273017404854,
3438126640106223589513424310, 3438132781048438054328921526,
3438127663728214370824940982, 3438123569262188196219252150,
3438121863927524956745297334, 3438121863949461907385675190,
3438119646105469022059195830, 3438125957673288388843564470,
2234884153727455684932354486, 3953954953475878275961012662,
2234884153749392635572732342, 3953954953497815226601390518,
2234884153771329586213110198, 3953954953519752177241768374,
2282636121220738214573064630, 5720777720717583396630380982,
2234884153774986214838157750, 2282636121224394843198112182,
4001706920972817434226770358, 2234884153771329664577274294,
2282636121220738292937228726, 5720777720717583474994545078,
2234884153753049342561943990, 2234884153774986293202321846,
2282636121224394921562276278, 2290594782312421298465735094,
4009665582060843889494393270, 2290594782334358249106112950,
4009665582082780840134771126, 2234884153756705971186991542,
2290594782316077927090782646, 2290594782305108119579804086,
7449158188819277673694304694, 7449158188841214624334682550,
7449158188863151574975060406, 7449158188866808203600107958,
7449158188863151653339224502, 7449158188844871331323894198,
7449158188866808281964272054, 7449158188848527959948941750,
7449158188837558152437963190, 2082339876881482673935897014,
3801410676629905264964555190, 2368888522492839894666990006,
4087959322241262485695648182, 3801416817572119729780052406,
4087965463183476950511145398, 2090298537991446001479733686,
3809369337739868592508391862, 2082339876881482752300061110,
2098257199101409407387734454, 3817327998849831998416392630,
2090298708573177080532013494, 4095924294875171357107261878,
2098257369683140408075850166, 5539080343979472099170845110,
5539080343979472177535009206, 5539080514561203178223124918,
2817267573208980612510361014, 5682324163367540282736485814,
2817267573208980690874525110, 5682324163367540361100649910,
2065095741541558983033819318, 3788175212531074393371941046,
4073374271817559093498562742, 5792445071565981684527220918,
5744693104138510006807644342, 2522760437061468460985737398,
3955288732140748296098799798, 7512840950705401339249107126,
7847143610242964759935887030};


AdditionMonoid[k_] :=
Module[{i, j},
	GroupoidNumber[Table[Mod[i + j, k], {i, 0, k - 1}, {j, 0, k - 1}]]
]

AdditionTable[k_, groupoid_Integer] :=
	Partition[Reverse[IntegerDigits[groupoid, k, k^2]], k]

AdditiveQ[{n_, k_, r_}] := AdditiveQ[{n, k, r}, AdditionMonoid[k]]
AdditiveQ[{n_, k_, r_}, monoid_Integer] :=
Module[
	{
		additiontable = AdditionTable[k, monoid],
		tuples = Tuples[Range[k - 1, 0, -1], 2 r + 1],
		values = IntegerDigits[n, k, k^(2 r + 1)],
		a, b
	},
	For[a = 1, a <= k^(2 r + 1), a++,
		For[b = 1, b <= a, b++,
			If[
				values[[-(1 + FromDigits[
					additiontable[[##]] & @@@ Transpose[{tuples[[a]], tuples[[b]]} + 1],
					k
				])]] != additiontable[[values[[a]] + 1,values[[b]] + 1]],
				Return[False]
			]
		]
	];
	True
]

AdditiveRule[k_, r_] := AdditiveRule[k, r, AdditionMonoid[k]]
AdditiveRule[k_, r_, monoid_Integer] :=
	AdditiveRule[k, ConstantArray[(k*(k^(k + 1) - 2*k^k + 1))/(k - 1)^2, 2 r + 1], monoid]
AdditiveRule[k_, {functions__Integer}, monoid_Integer] /;
	ValidRuleQ[{0, k, (Length[{functions}]-1)/2}] && And @@ Thread[0 <= {functions} < k^k] :=
With[
	{
		r = (Length[{functions}] - 1)/2,
		functionlists = Reverse /@ IntegerDigits[{functions}, k, k],
		additiontable = AdditionTable[k, monoid]
	},
	{
		FromDigits[
			(Fold[additiontable[[#1 + 1, #2 + 1]] &, First[#], Rest[#]] &) /@
				(Part @@@ Transpose[{functionlists, # + 1}] &) /@
					Tuples[Range[k - 1, 0, -1], 2 r + 1],
			k
		],
		k,
		r
	}
]

AdditiveRules[k_, r_] :=
With[{monoid = AdditionMonoid[k]},
	Sort[(First[AdditiveRule[k, #, monoid]] &) /@
		Tuples[WeightFunctions[k], 2 r + 1]]
]
AdditiveRules[k_, r_, monoid_Integer] /; ValidRuleQ[{0, k, r}] :=
	Union[(First[AdditiveRule[k, #, monoid]] &) /@
		Tuples[WeightFunctions[k, monoid], 2 r + 1]]
AdditiveRules[k_, r_, All] :=
	Union[Flatten[(AdditiveRules[k, r, #] &) /@
		Union[Flatten[(EquivalentGroupoids[k, #] &) /@
			InequivalentCommutativeMonoids[k]]]]]

AssociativeGroupoidQ[k_, groupoid_Integer] :=
	AssociativeGroupoidQ[AdditionTable[k, groupoid]]
AssociativeGroupoidQ[additiontable_?MatrixQ] :=
Module[{commutative = CommutativeGroupoidQ[additiontable], k = Length[additiontable], a, b, c},
	If[!If[commutative, k == Length[Union[additiontable]], GroupoidQ[additiontable]],
		Return[False]
	];
	For[a = 1, a <= k, a++,
		For[b = 1, b <= If[commutative, a, k], b++,
			For[c = 1, c <= If[commutative, a, k], c++,
				If[additiontable[[additiontable[[a,b]] + 1,c]] != additiontable[[a,additiontable[[b,c]] + 1]],
					Return[False]
				]
			]
		]
	];
	True
]

CommutativeGroupoidQ[k_, groupoid_Integer] :=
	CommutativeGroupoidQ[AdditionTable[k, groupoid]]
CommutativeGroupoidQ[additiontable_?MatrixQ] :=
	UnsameQ @@ additiontable && additiontable == Transpose[additiontable]

CommutativeMonoidQ[k_, groupoid_Integer] :=
	CommutativeMonoidQ[AdditionTable[k, groupoid]]
CommutativeMonoidQ[additiontable_?MatrixQ] :=
	MemberQ[additiontable, Range[0, Length[additiontable] - 1]] &&
		CommutativeGroupoidQ[additiontable] && AssociativeGroupoidQ[additiontable]

CommutativeMonoids[1] = {1};
CommutativeMonoids[k_Integer] :=
Module[{additiontable, f, m},
	SetAttributes[f, Listable];
	Sort[Reap[
		For[m = 0, m <= k^((1/2)*k*(k - 1)) - 1, m++,
			If[
				And @@ Thread[First /@ # <= Range[2, k]] &&
					AssociativeGroupoidQ[additiontable = (f[#, Transpose[#]] &)[
						PadLeft[Prepend[#, Range[0, k - 1]], {k, k}]] /. f -> Max],
				Sow[GroupoidNumber[additiontable]]
			] & @
				PartitionAt[
					Reverse[IntegerDigits[m, k, (1/2)*k*(k - 1)]],
					Accumulate[Range[k - 1, 2, -1]]
				]
		]
	][[2,1]]]
]

DistributiveQ[k_, groupoid_Integer, f_Integer] :=
	DistributiveQ[AdditionTable[k, groupoid], IntegerDigits[f, k, k]]
DistributiveQ[additiontable_?MatrixQ, function_?VectorQ] :=
Module[{a, b, k = Length[additiontable]},
	For[a = 1, a <= k, a++,
		For[b = 1, b <= a, b++,
			If[
				function[[-(additiontable[[a,b]] + 1)]] !=
					additiontable[[function[[-a]] + 1,function[[-b]] + 1]],
				Return[False]
			]
		]
	];
	True
]

EquivalentGroupoids[k_, groupoid_Integer] :=
	EquivalentGroupoids[AdditionTable[k, groupoid]]
EquivalentGroupoids[additiontable_?MatrixQ] :=
With[{k = Length[additiontable]},
	Union[
		GroupoidNumber[
			Map[Last, Partition[Sort[Flatten[Transpose[
				{Table[{i, j}, {i, k}, {j, k}], additiontable + 1} /. Thread[Range[k] -> #],
				{3, 1, 2}
			], 1]], k], {2}]
		] & /@ Permutations[Range[0, k - 1]]
	]
]

(* "GroupoidClassLex": *)
GroupoidClass[k_, groupoid_Integer] :=
	GroupoidClass[AdditionTable[k, groupoid]]
GroupoidClass[additiontable_?MatrixQ] :=
	First[SortGroupoids[Length[additiontable], EquivalentGroupoids[additiontable]]]

GroupoidNumber[additiontable_?MatrixQ] :=
	FromDigits[Reverse[Flatten[additiontable]], Length[additiontable]]

GroupoidQ[k_, groupoid_Integer] :=
	GroupoidQ[AdditionTable[k, groupoid]]
GroupoidQ[additiontable_?MatrixQ] :=
With[{k = Length[additiontable]},
	Intersection[
		Flatten[(Subsets[Last[#], {2}] &) /@ ClassifyBy[Range[k], additiontable[[#]] &], 1],
		Flatten[(Subsets[Last[#], {2}] &) /@ ClassifyBy[Range[k], Transpose[additiontable][[#]] &], 1]
	] == {}
]

IdentityElement[k_, monoid_Integer] :=
	IdentityElement[AdditionTable[k, monoid]]
IdentityElement[additiontable_?MatrixQ] :=
	If[Length[#] == 1,
		#[[1,1]],
		Flatten[#]
	] &[Position[additiontable, Range[0, Length[additiontable] - 1]] - 1]

(*
MonoidClass[k_, monoid_Integer] := MonoidClass[AdditionTable[k, monoid]]
MonoidClass[additiontable_?MatrixQ] :=
*)
(* "MonoidClassLex": *)
MonoidClass[k_, monoid_Integer] :=
	MonoidClass[AdditionTable[k, monoid]]
MonoidClass[additiontable_?MatrixQ] :=
	First[SortGroupoids[
		Length[additiontable],
		Select[EquivalentGroupoids[additiontable], IdentityElement[Length[additiontable], #] == 0 &]
	]]

(*
SortGroupoids[k_, list_?VectorQ] := Flatten[(SortGroupoidsLex[k, Last[#1]] &) /@
    Reverse[ClassifyBy[list, Function[g, CanonicalForest[UnloopGraph[(AdditionTable[k, g][[#1,#1]] &) /@ Range[k]]]]]]]
*)
(* "SortGroupoidsLex": *)
SortGroupoids[k_, list_ ? VectorQ] :=
	FromDigits[Reverse[#], k] & /@ Sort[Reverse /@ IntegerDigits[list, k, k^2]]

WeightFunctions[k_] := (FromDigits[Mod[#*Range[k - 1, 0, -1], k], k] &) /@ Range[k, 1, -1]
WeightFunctions[k_, monoid_Integer] := WeightFunctions[AdditionTable[k, monoid]]
WeightFunctions[additiontable_?MatrixQ] :=
Module[{f, k = Length[additiontable]},
	Sort[Reap[
		For[f = 0, f <= k^k - 1, f++,
			If[DistributiveQ[additiontable, IntegerDigits[f, k, k]], Sow[f]]
		]
	][[2,1]]]
]


(*
CanonicalForest[list_?VectorQ] := PointerCode[CanonicalTree[FromPointerCode[list]]]

CanonicalTree[tree_List] := Sort[CanonicalTree /@ tree,
    !OrderedQ[StringJoin @@@ Map[ToString, LevelCode /@ {##1}, {2}]] &]

FromPointerCode[list_?VectorQ] :=
  Module[{nodes = (Flatten[{#1[[1,1]], Last /@ #1}, 1] &) /@
      Last /@ ClassifyBy[Transpose[{Rest[list], List /@ Range[Length[list] - 1]}], First], tree = {0}},
   While[nodes != {}, tree = tree /. {nodes[[1,1]]} -> First[nodes]; nodes = Rest[nodes]]; tree //. {_Integer, s___} -> {s}]

LevelCode[tree_List] := Module[{list = Take[Characters[StringReplace[ToString[tree], {", " -> ""}]], {2, -2}], code = {},
    level = 0}, While[list != {}, If[First[list] == "{", AppendTo[code, level++], level--]; list = Rest[list]]; code]

PointerCode[tree_List] := Module[{i = 0, labelledtree},
   labelledtree = ToExpression[StringReplace[StringReplace[ToString[tree], "{" :> StringJoin["{", ToString[i++], ", "]],
       ", }" -> "}"]]; Prepend[(labelledtree[[Sequence @@ Append[Drop[Position[labelledtree, #1][[1]], -2], 1]]] &) /@
      Range[i - 1], -1]]

UnloopGraph[list_?VectorQ] :=
  With[{roots = Union[Flatten[(CanonicalRotation[FixedPointPeriod[list[[#1 + 1]] &, #1]] &) /@ list]]},
   Last /@ (Transpose[{Range[0, Length[list] - 1], list}] /. {a_?(MemberQ[roots, #1] &), _} -> {a, -1})]
*)


End[]

Protect["AdditiveRules`*"]

EndPackage[]
