import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInitialDefect
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInitialForm5 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 379850724815783547271708647270383616)*x 0 +
  (Nat.rawCast 3422078601943995921366744570003456)*x 1

def slopeInitialForm6 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 2478725600674767712376645316872503296)*x 0 +
  (Nat.rawCast 1711039300971997960683372285001728)*x 1

def slopeInitialForm7 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 9999788963575070526111595236962598912)*x 0 +
  ((Int.negOfNat 338120377419855374786153067652841472).rawCast)*x 1 +
  ((Int.negOfNat 3279491993529662757976463546253312).rawCast)*x 2

def slopeInitialForm8 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 33494418150264365116432156324823826432)*x 0 +
  ((Int.negOfNat 1751296253414311357147228294040518656).rawCast)*x 1 +
  ((Int.negOfNat 617875303128777041357884436250624).rawCast)*x 2

def slopeInitialForm9 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 95480209861156702688760586073372884992)*x 0 +
  ((Int.negOfNat 6822507803843748924092064804567515136).rawCast)*x 1 +
  (Nat.rawCast 121750480136601626495601254149914624)*x 2 +
  (Nat.rawCast 1314965388709961395710369441251328)*x 3

def slopeInitialForm10 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 214476941234379796935576341011790561280)*x 0 +
  ((Int.negOfNat 20946722235923966422332447970943827968).rawCast)*x 1 +
  (Nat.rawCast 498595664081503419633439764840972288)*x 2 +
  (Nat.rawCast 673765732970197756637408170868736)*x 3

def slopeInitialForm11 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 356785083503506326852708437214256693248)*x 0 +
  ((Int.negOfNat 53075498293915712825024336297887531008).rawCast)*x 1 +
  (Nat.rawCast 1973608506280849071434894509653098496)*x 2 +
  ((Int.negOfNat 25044743657109227094655402317447168).rawCast)*x 3 +
  ((Int.negOfNat 290894284450229077163505421910016).rawCast)*x 4

def slopeInitialForm12 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 424240903244442483862613709193255845888)*x 0 +
  ((Int.negOfNat 106734711041681251027417521149070802944).rawCast)*x 1 +
  (Nat.rawCast 5527823923801569297747531223888035840)*x 2 +
  ((Int.negOfNat 57654657956968395990028018488705024).rawCast)*x 3 +
  ((Int.negOfNat 618046446177285328762502400442368).rawCast)*x 4

def slopeInitialForm13 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 345742168246405576639643096240583868416)*x 0 +
  ((Int.negOfNat 155636387162763125485245094979149234176).rawCast)*x 1 +
  (Nat.rawCast 12403197823479197177711199672902615040)*x 2 +
  ((Int.negOfNat 373202363409058012804972614783074304).rawCast)*x 3 +
  (Nat.rawCast 5233868185639027360125811251216384)*x 4 +
  (Nat.rawCast 39036914397842698481907070402560)*x 5

def slopeInitialForm14 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 171532481494357378619623259180151865344)*x 0 +
  ((Int.negOfNat 154102383312486706916717439106500526080).rawCast)*x 1 +
  (Nat.rawCast 22246954041663099233810451240321024000)*x 2 +
  ((Int.negOfNat 906781716247402989098622423178149888).rawCast)*x 3 +
  ((Int.negOfNat 4671644425179794882878504641232896).rawCast)*x 4 +
  (Nat.rawCast 218032508534610551972471305666560)*x 5

def slopeInitialForm15 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 22593563415090983792684291424635584512)*x 0 +
  ((Int.negOfNat 95087697998400852509741630389783363584).rawCast)*x 1 +
  (Nat.rawCast 27526807758219780900866456505135661056)*x 2 +
  ((Int.negOfNat 1498344049813840026567985595575959552).rawCast)*x 3 +
  (Nat.rawCast 61070905414164721813458254227832832)*x 4 +
  ((Int.negOfNat 1250905028909361000154443565498368).rawCast)*x 5 +
  ((Int.negOfNat 3263489665734750297582766915584).rawCast)*x 6

def slopeInitialForm16 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 37117733200767518089756394749861822464).rawCast)*x 0 +
  ((Int.negOfNat 25181988322389285695473132606303764480).rawCast)*x 1 +
  (Nat.rawCast 20755387280325906505976460733216456704)*x 2 +
  ((Int.negOfNat 2212969621807331519782412642842312704).rawCast)*x 3 +
  (Nat.rawCast 104223092000364337882428273837735936)*x 4 +
  (Nat.rawCast 2977764747443577055229431366287360)*x 5 +
  ((Int.negOfNat 37412564634972595011093006385152).rawCast)*x 6

def slopeInitialForm17 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 33153173429017070049724824807058440192).rawCast)*x 0 +
  (Nat.rawCast 12046552554332539416878739946727276544)*x 1 +
  (Nat.rawCast 7240755950216490065613466975856492544)*x 2 +
  ((Int.negOfNat 2206112723979430099187783256200183808).rawCast)*x 3 +
  (Nat.rawCast 55073739232178732628736322681438208)*x 4 +
  ((Int.negOfNat 9201951534792311634692575907020800).rawCast)*x 5 +
  (Nat.rawCast 208061753264598665869170497814528)*x 6 +
  (Nat.rawCast 166213001843439619299751231488)*x 7

def slopeInitialForm18 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 14564946610701212582149502081704132608).rawCast)*x 0 +
  (Nat.rawCast 15727826164472824714080585116716892160)*x 1 +
  ((Int.negOfNat 1821195926059494343071049836153274368).rawCast)*x 2 +
  ((Int.negOfNat 1020080115273413073183223116730466304).rawCast)*x 3 +
  (Nat.rawCast 51394723110810847143894598016827392)*x 4 +
  ((Int.negOfNat 6397917410648923232299473029824512).rawCast)*x 5 +
  ((Int.negOfNat 541905214277181211995508819623936).rawCast)*x 6 +
  (Nat.rawCast 3387503815768361849694481022976)*x 7

def slopeInitialForm19 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 3803827716777410992822698647060742144).rawCast)*x 0 +
  (Nat.rawCast 7697331965300771527451019270168772608)*x 1 +
  ((Int.negOfNat 3389993042605225902898141844478099456).rawCast)*x 2 +
  (Nat.rawCast 158008901426082303957404805589106688)*x 3 +
  (Nat.rawCast 50661481142078366178690166117367808)*x 4 +
  (Nat.rawCast 10624536926356447219366713133891584)*x 5 +
  (Nat.rawCast 1134768764750197199013829341609984)*x 6 +
  ((Int.negOfNat 19574697181368476215986641436672).rawCast)*x 7 +
  ((Int.negOfNat 4717641026226225406543921152).rawCast)*x 8

def slopeInitialForm20 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 540257089883406029737297062981009408).rawCast)*x 0 +
  (Nat.rawCast 1994759820641839902450977907973029888)*x 1 +
  ((Int.negOfNat 1730814619274750901114370284060672000).rawCast)*x 2 +
  (Nat.rawCast 439029251183823708379312276774060032)*x 3 +
  ((Int.negOfNat 5225080962436903609761801160359936).rawCast)*x 4 +
  (Nat.rawCast 7884361036719881275916081631854592)*x 5 +
  ((Int.negOfNat 244101285980303056347728399302656).rawCast)*x 6 +
  (Nat.rawCast 52386885311380771672469142503424)*x 7 +
  ((Int.negOfNat 155650479340407837376489979904).rawCast)*x 8

def slopeInitialForm21 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 14357475819991367175240190871470080).rawCast)*x 0 +
  (Nat.rawCast 177391663248410105862728256388595712)*x 1 +
  ((Int.negOfNat 413896771282466356950726160574054400).rawCast)*x 2 +
  (Nat.rawCast 220167519769608002847755107049668608)*x 3 +
  ((Int.negOfNat 32929544631629268414199867178483712).rawCast)*x 4 +
  (Nat.rawCast 381058546034305102924657729732608)*x 5 +
  ((Int.negOfNat 1562479046629084514215614732042240).rawCast)*x 6 +
  ((Int.negOfNat 98447814113389588112525500612608).rawCast)*x 7 +
  (Nat.rawCast 946265256851693077012659830784)*x 8 +
  (Nat.rawCast 57138358927437169220911104)*x 9

def slopeInitialForm22 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 8006491603912632510541976297275392)*x 0 +
  ((Int.negOfNat 54472956500699721582346626429616128).rawCast)*x 1 +
  ((Int.negOfNat 3114438300820788514331437075267584).rawCast)*x 2 +
  (Nat.rawCast 42932351855094219138779207675412480)*x 3 +
  ((Int.negOfNat 16269646950980947787570770423578624).rawCast)*x 4 +
  (Nat.rawCast 196028969376290997066370727804928)*x 5 +
  ((Int.negOfNat 304381939531176908471361425375232).rawCast)*x 6 +
  (Nat.rawCast 81532402630308156798379172560896)*x 7 +
  ((Int.negOfNat 2647775301388830436849977655296).rawCast)*x 8 +
  (Nat.rawCast 2850551987904399428605181952)*x 9

def slopeInitialForm23 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 1204950849048858866556975458549760)*x 0 +
  ((Int.negOfNat 21022866541847225172579640387043328).rawCast)*x 1 +
  (Nat.rawCast 30016017098378329473057868971245568)*x 2 +
  ((Int.negOfNat 3917514401087927505629895205060608).rawCast)*x 3 +
  ((Int.negOfNat 1684268554954668568727556527751168).rawCast)*x 4 +
  (Nat.rawCast 407275620387469567879683697016832)*x 5 +
  (Nat.rawCast 272429425221852366777001766289408)*x 6 +
  (Nat.rawCast 62178121273147532891489776435200)*x 7 +
  (Nat.rawCast 5048142145729871050867684147200)*x 8 +
  ((Int.negOfNat 18317691825754062567594000384).rawCast)*x 9

def slopeInitialForm24 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 55273439444565149208723805175808)*x 0 +
  ((Int.negOfNat 3016996157010441567330775326523392).rawCast)*x 1 +
  (Nat.rawCast 9862175287733911489482206931320832)*x 2 +
  ((Int.negOfNat 3941783791649507019220978476515328).rawCast)*x 3 +
  (Nat.rawCast 626412622833965680420404823326720)*x 4 +
  ((Int.negOfNat 49716808436400852391639790911488).rawCast)*x 5 +
  (Nat.rawCast 69301255121305158915667141853184)*x 6 +
  ((Int.negOfNat 30394882540426128780019560873984).rawCast)*x 7 +
  ((Int.negOfNat 6047472416616173305338506772480).rawCast)*x 8 +
  (Nat.rawCast 54585164805924473423215460352)*x 9

def slopeInitialForm25 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 178306123089458034635655497121792).rawCast)*x 1 +
  (Nat.rawCast 1473934314738437157796820608352256)*x 2 +
  ((Int.negOfNat 870968066770542068967097623379968).rawCast)*x 3 +
  (Nat.rawCast 136517300303791434627747019751424)*x 4 +
  ((Int.negOfNat 30936213902874530489953576550400).rawCast)*x 5 +
  ((Int.negOfNat 8451491103029986218932195819520).rawCast)*x 6 +
  ((Int.negOfNat 12182256168562767017761547747328).rawCast)*x 7 +
  (Nat.rawCast 1402769081411040623377489330176)*x 8 +
  ((Int.negOfNat 111534962359696234420453244928).rawCast)*x 9

def slopeInitialForm26 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 1085093442705880910191449341952).rawCast)*x 1 +
  (Nat.rawCast 32090805771588964531737251020800)*x 2 +
  ((Int.negOfNat 125136584587933010859694611234816).rawCast)*x 3 +
  (Nat.rawCast 17864067793539643067019495997440)*x 4 +
  (Nat.rawCast 18329626901254530687215515729920)*x 5 +
  ((Int.negOfNat 6535503187803382504162911584256).rawCast)*x 6 +
  (Nat.rawCast 3853006391316093377583192735744)*x 7 +
  (Nat.rawCast 1050953296750980592778487005184)*x 8 +
  (Nat.rawCast 160984456964533470590794727424)*x 9

def slopeInitialForm27 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 24953142403802407639740567257088).rawCast)*x 2 +
  ((Int.negOfNat 31224292108849313779605672296448).rawCast)*x 3 +
  (Nat.rawCast 14170511329270523951463171883008)*x 4 +
  (Nat.rawCast 54855711511834984747339087872)*x 5 +
  ((Int.negOfNat 2638080339289945403280945315840).rawCast)*x 6 +
  (Nat.rawCast 1144724226722545060796606447616)*x 7 +
  ((Int.negOfNat 397818454928143268807253688320).rawCast)*x 8 +
  ((Int.negOfNat 119721767966169309385473392640).rawCast)*x 9

def slopeInitialForm28 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 2906976661455180339089523081216).rawCast)*x 2 +
  ((Int.negOfNat 4581670592995405565286420578304).rawCast)*x 3 +
  (Nat.rawCast 3585981641280589061909844590592)*x 4 +
  ((Int.negOfNat 2253007045835815027690186997760).rawCast)*x 5 +
  (Nat.rawCast 560763103455047600890611499008)*x 6 +
  ((Int.negOfNat 92508191267664651557586075648).rawCast)*x 7 +
  ((Int.negOfNat 92043223653779064381920772096).rawCast)*x 8 +
  (Nat.rawCast 42366273404228471568866476032)*x 9

def slopeInitialForm29 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 788133280157196023097993461760)*x 3 +
  (Nat.rawCast 85329376458584901250405367808)*x 4 +
  (Nat.rawCast 11457298464178779798582067200)*x 5 +
  (Nat.rawCast 331116150296460108659215564800)*x 6 +
  ((Int.negOfNat 118574990072067112239158525952).rawCast)*x 7 +
  (Nat.rawCast 55673280340852255219079184384)*x 8 +
  ((Int.negOfNat 3036615142880296284255682560).rawCast)*x 9

def slopeInitialForm30 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 203187603213219730878042734592)*x 3 +
  (Nat.rawCast 6004427222544244488473149440)*x 4 +
  (Nat.rawCast 43547943099743996954214924288)*x 5 +
  ((Int.negOfNat 62012929443194767017957654528).rawCast)*x 6 +
  (Nat.rawCast 4437691330364049937315921920)*x 7 +
  ((Int.negOfNat 2578982890170485313298759680).rawCast)*x 8 +
  ((Int.negOfNat 3221877429049857082002505728).rawCast)*x 9

def slopeInitialForm31 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 859681124743193764175020032)*x 4 +
  ((Int.negOfNat 12621356975969459045086003200).rawCast)*x 5 +
  ((Int.negOfNat 8748773477926867899871395840).rawCast)*x 6 +
  (Nat.rawCast 7952049811355479338186178560)*x 7 +
  ((Int.negOfNat 2875555439375534746327056384).rawCast)*x 8 +
  (Nat.rawCast 1465020804387785838428160000)*x 9

def slopeInitialForm32 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 3895351592782291648647266304).rawCast)*x 4 +
  (Nat.rawCast 115308073376650005005205504)*x 5 +
  (Nat.rawCast 3465951578604138012843442176)*x 6 +
  ((Int.negOfNat 1492294722302530982277808128).rawCast)*x 7 +
  (Nat.rawCast 819549252314760516401627136)*x 8 +
  ((Int.negOfNat 339668736634767880835039232).rawCast)*x 9

def slopeInitialForm33 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 188752976437952290247147520)*x 5 +
  ((Int.negOfNat 293755091137823391306743808).rawCast)*x 6 +
  (Nat.rawCast 49216559467260364650971136)*x 7 +
  ((Int.negOfNat 119298281243061771520966656).rawCast)*x 8 +
  (Nat.rawCast 52202323684917253351931904)*x 9

def slopeInitialForm34 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 14105262806188904624947200)*x 5 +
  (Nat.rawCast 9102101540651232034553856)*x 6 +
  (Nat.rawCast 10530797113342715586674688)*x 7 +
  (Nat.rawCast 12090214330269120407273472)*x 8 +
  ((Int.negOfNat 5749159820642079926648832).rawCast)*x 9

def slopeInitialForm35 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 1486799822839173070454784).rawCast)*x 6 +
  ((Int.negOfNat 1528859874950641530961920).rawCast)*x 7 +
  ((Int.negOfNat 950959921156114486394880).rawCast)*x 8 +
  (Nat.rawCast 464024322031729791467520)*x 9

def slopeInitialForm36 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 26047480442513503813632)*x 6 +
  (Nat.rawCast 122963936776507619278848)*x 7 +
  (Nat.rawCast 60907228997789662838784)*x 8 +
  ((Int.negOfNat 26941427134406741458944).rawCast)*x 9

def slopeInitialForm37 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 2860857936750927937536).rawCast)*x 7 +
  ((Int.negOfNat 3148443499360728121344).rawCast)*x 8 +
  (Nat.rawCast 1019651651004033662976)*x 9

def slopeInitialForm38 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 70119067077228625920)*x 8 +
  ((Int.negOfNat 17537882402070724608).rawCast)*x 9

def slopeInitialClockForm (A : ℕ) (x : ℕ → ℝ) : ℝ :=
  (4/5)^(5-5)*slopeInitialForm5 x*degreeElevationCoefficient 33 (5-5) A +
  (4/5)^(6-5)*slopeInitialForm6 x*degreeElevationCoefficient 33 (6-5) A +
  (4/5)^(7-5)*slopeInitialForm7 x*degreeElevationCoefficient 33 (7-5) A +
  (4/5)^(8-5)*slopeInitialForm8 x*degreeElevationCoefficient 33 (8-5) A +
  (4/5)^(9-5)*slopeInitialForm9 x*degreeElevationCoefficient 33 (9-5) A +
  (4/5)^(10-5)*slopeInitialForm10 x*degreeElevationCoefficient 33 (10-5) A +
  (4/5)^(11-5)*slopeInitialForm11 x*degreeElevationCoefficient 33 (11-5) A +
  (4/5)^(12-5)*slopeInitialForm12 x*degreeElevationCoefficient 33 (12-5) A +
  (4/5)^(13-5)*slopeInitialForm13 x*degreeElevationCoefficient 33 (13-5) A +
  (4/5)^(14-5)*slopeInitialForm14 x*degreeElevationCoefficient 33 (14-5) A +
  (4/5)^(15-5)*slopeInitialForm15 x*degreeElevationCoefficient 33 (15-5) A +
  (4/5)^(16-5)*slopeInitialForm16 x*degreeElevationCoefficient 33 (16-5) A +
  (4/5)^(17-5)*slopeInitialForm17 x*degreeElevationCoefficient 33 (17-5) A +
  (4/5)^(18-5)*slopeInitialForm18 x*degreeElevationCoefficient 33 (18-5) A +
  (4/5)^(19-5)*slopeInitialForm19 x*degreeElevationCoefficient 33 (19-5) A +
  (4/5)^(20-5)*slopeInitialForm20 x*degreeElevationCoefficient 33 (20-5) A +
  (4/5)^(21-5)*slopeInitialForm21 x*degreeElevationCoefficient 33 (21-5) A +
  (4/5)^(22-5)*slopeInitialForm22 x*degreeElevationCoefficient 33 (22-5) A +
  (4/5)^(23-5)*slopeInitialForm23 x*degreeElevationCoefficient 33 (23-5) A +
  (4/5)^(24-5)*slopeInitialForm24 x*degreeElevationCoefficient 33 (24-5) A +
  (4/5)^(25-5)*slopeInitialForm25 x*degreeElevationCoefficient 33 (25-5) A +
  (4/5)^(26-5)*slopeInitialForm26 x*degreeElevationCoefficient 33 (26-5) A +
  (4/5)^(27-5)*slopeInitialForm27 x*degreeElevationCoefficient 33 (27-5) A +
  (4/5)^(28-5)*slopeInitialForm28 x*degreeElevationCoefficient 33 (28-5) A +
  (4/5)^(29-5)*slopeInitialForm29 x*degreeElevationCoefficient 33 (29-5) A +
  (4/5)^(30-5)*slopeInitialForm30 x*degreeElevationCoefficient 33 (30-5) A +
  (4/5)^(31-5)*slopeInitialForm31 x*degreeElevationCoefficient 33 (31-5) A +
  (4/5)^(32-5)*slopeInitialForm32 x*degreeElevationCoefficient 33 (32-5) A +
  (4/5)^(33-5)*slopeInitialForm33 x*degreeElevationCoefficient 33 (33-5) A +
  (4/5)^(34-5)*slopeInitialForm34 x*degreeElevationCoefficient 33 (34-5) A +
  (4/5)^(35-5)*slopeInitialForm35 x*degreeElevationCoefficient 33 (35-5) A +
  (4/5)^(36-5)*slopeInitialForm36 x*degreeElevationCoefficient 33 (36-5) A +
  (4/5)^(37-5)*slopeInitialForm37 x*degreeElevationCoefficient 33 (37-5) A +
  (4/5)^(38-5)*slopeInitialForm38 x*degreeElevationCoefficient 33 (38-5) A

def slopeInitialTensorCoefficient (A B : ℕ) : ℝ :=
  slopeInitialClockForm A (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)

end
end HTGeometry.ThetaRatioKineticContraction

