import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstSourceDefect
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectForm4 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 6844157203887991842733489140006912)*x 0

def firstControlDefectForm5 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 99240279456375881719635592530100224)*x 0

def firstControlDefectForm6 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 452664952846036349376345490065457152)*x 0 +
  ((Int.negOfNat 12642679279404207153938250772512768).rawCast)*x 1 +
  ((Int.negOfNat 47528869471444387796760341250048).rawCast)*x 2

def firstControlDefectForm7 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 1833632098295343518273816125199351808)*x 0 +
  ((Int.negOfNat 91271272341663706032378775313842176).rawCast)*x 1

def firstControlDefectForm8 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 6574832224535303805706046846294556672)*x 0 +
  ((Int.negOfNat 361105866794795563440086332685156352).rawCast)*x 1 +
  (Nat.rawCast 5853972423232900430300982030630912)*x 2 +
  (Nat.rawCast 31685912980962925197840227500032)*x 3

def firstControlDefectForm9 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 17404266650154668670158191859985285120)*x 0 +
  ((Int.negOfNat 1226574453874692166697711003284537344).rawCast)*x 1 +
  (Nat.rawCast 29730188018637935759240200124891136)*x 2 +
  ((Int.negOfNat 10341929931286510307628407586816).rawCast)*x 3

def firstControlDefectForm10 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 33026959250019175387225824774095634432)*x 0 +
  ((Int.negOfNat 3619882534589966705674186875205582848).rawCast)*x 1 +
  (Nat.rawCast 110096665391478303965545600477298688)*x 2 +
  ((Int.negOfNat 1002066998022952509381697194688512).rawCast)*x 3 +
  ((Int.negOfNat 8948336536290455727167842025472).rawCast)*x 4

def firstControlDefectForm11 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 45247103285818223259615379135647449088)*x 0 +
  ((Int.negOfNat 8159172994225738929084518571712708608).rawCast)*x 1 +
  (Nat.rawCast 328458765555396236667224584580235264)*x 2 +
  ((Int.negOfNat 3434382564681395297991600352788480).rawCast)*x 3 +
  ((Int.negOfNat 17609397241156286168012672729088).rawCast)*x 4

def firstControlDefectForm12 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 44142845697774667431701180780579389440)*x 0 +
  ((Int.negOfNat 13135044006086548484523653598743101440).rawCast)*x 1 +
  (Nat.rawCast 819272426863941446797132054149464064)*x 2 +
  ((Int.negOfNat 22695307167816788701149687925702656).rawCast)*x 3 +
  (Nat.rawCast 148180337458136771359074127183872)*x 4 +
  (Nat.rawCast 1385443726019469465954948218880)*x 5

def firstControlDefectForm13 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 28766196399035179879133836240327016448)*x 0 +
  ((Int.negOfNat 14608133123338375249029661060409327616).rawCast)*x 1 +
  (Nat.rawCast 1580735345948107647989793481090400256)*x 2 +
  ((Int.negOfNat 58837634193274680745100130190884864).rawCast)*x 3 +
  ((Int.negOfNat 306789534649976960913836580274176).rawCast)*x 4 +
  (Nat.rawCast 10368755925001102976209398005760)*x 5

def firstControlDefectForm14 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 9639698230414223706647814607944548352)*x 0 +
  ((Int.negOfNat 10557953730691463377216444427912871936).rawCast)*x 1 +
  (Nat.rawCast 2101437317105299357244096155433828352)*x 2 +
  ((Int.negOfNat 96670963794494169690867399602995200).rawCast)*x 3 +
  (Nat.rawCast 4209003422470314893292353309638656)*x 4 +
  ((Int.negOfNat 50073575311921365547269545263104).rawCast)*x 5 +
  ((Int.negOfNat 126772628524657336754047549440).rawCast)*x 6

def firstControlDefectForm15 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 2106563042060527708767209188686299136).rawCast)*x 0 +
  ((Int.negOfNat 3895017059954659748007075834601930752).rawCast)*x 1 +
  (Nat.rawCast 1741675685131585800982869594234421248)*x 2 +
  ((Int.negOfNat 135666430225726515768278150195183616).rawCast)*x 3 +
  (Nat.rawCast 7851943321723891749690091040145408)*x 4 +
  (Nat.rawCast 181914571638497054341152594984960)*x 5 +
  ((Int.negOfNat 2150607091043294105649020928000).rawCast)*x 6

def firstControlDefectForm16 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 4592195889645740272853513628844818432).rawCast)*x 0 +
  (Nat.rawCast 726370637560292854784656799585796096)*x 1 +
  (Nat.rawCast 704279258615599125636841670373801984)*x 2 +
  ((Int.negOfNat 136929313148079949378070104567185408).rawCast)*x 3 +
  (Nat.rawCast 2767047105253265007800774421381120)*x 4 +
  ((Int.negOfNat 669763123822753340129810596233216).rawCast)*x 5 +
  (Nat.rawCast 11135830940772521655108492066816)*x 6 +
  (Nat.rawCast 6841697412441824523234312192)*x 7

def firstControlDefectForm17 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 2761000127680334405566091648884015104).rawCast)*x 0 +
  (Nat.rawCast 1802088961792474771155220640613531648)*x 1 +
  ((Int.negOfNat 130812952477209158991530691900997632).rawCast)*x 2 +
  ((Int.negOfNat 66421213787479284866494827967021056).rawCast)*x 3 +
  ((Int.negOfNat 702921817894205532282540609503232).rawCast)*x 4 +
  ((Int.negOfNat 565768060641421697031540855275520).rawCast)*x 5 +
  ((Int.negOfNat 34200352065990468596265104965632).rawCast)*x 6 +
  (Nat.rawCast 214012654966394082053377228800)*x 7

def firstControlDefectForm18 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 928470393140571061766402570780147712).rawCast)*x 0 +
  (Nat.rawCast 1047705403928376849607957129564520448)*x 1 +
  ((Int.negOfNat 329663082219577886270896708924735488).rawCast)*x 2 +
  (Nat.rawCast 13105788371585660936354393015451648)*x 3 +
  (Nat.rawCast 300987463644630408820775800799232)*x 4 +
  (Nat.rawCast 922955601067491977730990092058624)*x 5 +
  (Nat.rawCast 83012002421670112131081635364864)*x 6 +
  ((Int.negOfNat 1211777661849792413833573171200).rawCast)*x 7 +
  ((Int.negOfNat 201226394483583074212773888).rawCast)*x 8

def firstControlDefectForm19 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 169067586418226575633587492945395712).rawCast)*x 0 +
  (Nat.rawCast 291592261315377451358018078332944384)*x 1 +
  ((Int.negOfNat 176558541669050516868901027920740352).rawCast)*x 2 +
  (Nat.rawCast 34344020592059868534381882655113216)*x 3 +
  ((Int.negOfNat 587659586845971540629754627489792).rawCast)*x 4 +
  (Nat.rawCast 876664043783261427340254986108928)*x 5 +
  ((Int.negOfNat 12520946669515739777211354316800).rawCast)*x 6 +
  (Nat.rawCast 3501248301648957187581869555712)*x 7 +
  ((Int.negOfNat 10328689979812433073134370816).rawCast)*x 8

def firstControlDefectForm20 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 6037748877176762047908028109291520).rawCast)*x 0 +
  (Nat.rawCast 12626743043300638412607595581800448)*x 1 +
  ((Int.negOfNat 36917443749314585490809271751802880).rawCast)*x 2 +
  (Nat.rawCast 16597762583378767181251971970498560)*x 3 +
  ((Int.negOfNat 1647160332819868932117840084860928).rawCast)*x 4 +
  (Nat.rawCast 22689887765805112325623089463296)*x 5 +
  ((Int.negOfNat 124136466782335137552240035758080).rawCast)*x 6 +
  ((Int.negOfNat 7346009003715564611040190660608).rawCast)*x 7 +
  (Nat.rawCast 63101554071369647267373907968)*x 8 +
  (Nat.rawCast 2484276475105963879170048)*x 9

def firstControlDefectForm21 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 4288875204817921973461372939272192)*x 0 +
  ((Int.negOfNat 19170961324466691477313617370546176).rawCast)*x 1 +
  (Nat.rawCast 4253425526648566003054345287892992)*x 2 +
  (Nat.rawCast 2222045921595566758522702188773376)*x 3 +
  ((Int.negOfNat 795325968105455929454881753006080).rawCast)*x 4 +
  ((Int.negOfNat 123789066898933350519532966379520).rawCast)*x 5 +
  ((Int.negOfNat 16164524781475705956632170070016).rawCast)*x 6 +
  (Nat.rawCast 6338891536934490668419774414848)*x 7 +
  ((Int.negOfNat 186454106991469548745959407616).rawCast)*x 8 +
  (Nat.rawCast 192893717139998487034724352)*x 9

def firstControlDefectForm22 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 925885107793092624711959609081856)*x 0 +
  ((Int.negOfNat 6460086279748392535765807458680832).rawCast)*x 1 +
  (Nat.rawCast 4007103848266254446235626716004352)*x 2 +
  ((Int.negOfNat 704874006705456082565076527087616).rawCast)*x 3 +
  ((Int.negOfNat 14278667220482802023721697542144).rawCast)*x 4 +
  ((Int.negOfNat 11206536409744154836180477673472).rawCast)*x 5 +
  (Nat.rawCast 33634789181379218214007244587008)*x 6 +
  (Nat.rawCast 4022530825072657585731916529664)*x 7 +
  (Nat.rawCast 391663329452457058462599217152)*x 8 +
  ((Int.negOfNat 1266321116365341556721319936).rawCast)*x 9

def firstControlDefectForm23 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 71652993396973192331265249902592)*x 0 +
  ((Int.negOfNat 715997782626613863914459658977280).rawCast)*x 1 +
  (Nat.rawCast 821836424114297251741150614650880)*x 2 +
  ((Int.negOfNat 254106394523306782594695822311424).rawCast)*x 3 +
  (Nat.rawCast 45675022175516653650194945015808)*x 4 +
  (Nat.rawCast 5245213847045331428857960464384)*x 5 +
  (Nat.rawCast 4968631858146423090594982133760)*x 6 +
  ((Int.negOfNat 3445204718035128774690789654528).rawCast)*x 7 +
  ((Int.negOfNat 506913094971820426014788419584).rawCast)*x 8 +
  (Nat.rawCast 3985433421661177766656081920)*x 9

def firstControlDefectForm24 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 1327389282474316987658642915328)*x 0 +
  (Nat.rawCast 69562514246234485905727313412096)*x 1 +
  (Nat.rawCast 84800759608586752217788044017664)*x 2 +
  ((Int.negOfNat 32741405112031815828565829615616).rawCast)*x 3 +
  ((Int.negOfNat 1721856978024000056967630422016).rawCast)*x 4 +
  (Nat.rawCast 2772924796948008673349235376128)*x 5 +
  ((Int.negOfNat 3772982169876740838128414097408).rawCast)*x 6 +
  ((Int.negOfNat 502165794909407394671408185344).rawCast)*x 7 +
  (Nat.rawCast 217946181235820485899485970432)*x 8 +
  ((Int.negOfNat 8988069261962837074227757056).rawCast)*x 9

def firstControlDefectForm25 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 27124956396591230717748263780352)*x 1 +
  (Nat.rawCast 13823165672257739832102846726144)*x 2 +
  ((Int.negOfNat 12540083981948556683400506769408).rawCast)*x 3 +
  (Nat.rawCast 800322807516379125723829370880)*x 4 +
  (Nat.rawCast 1368106935510856070140753084416)*x 5 +
  ((Int.negOfNat 669982326665174732331125047296).rawCast)*x 6 +
  (Nat.rawCast 629314699087041044777590063104)*x 7 +
  (Nat.rawCast 38326243222300795852453576704)*x 8 +
  (Nat.rawCast 14268808377082412896968769536)*x 9

def firstControlDefectForm26 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 2201730367441141015212673990656)*x 1 +
  (Nat.rawCast 459213638400093679759506014208)*x 2 +
  ((Int.negOfNat 3234297147007249694198656401408).rawCast)*x 3 +
  (Nat.rawCast 1495805387726664399742247632896)*x 4 +
  ((Int.negOfNat 429883699588965669574331596800).rawCast)*x 5 +
  (Nat.rawCast 145435951372546819717123276800)*x 6 +
  ((Int.negOfNat 11533994441829175637179367424).rawCast)*x 7 +
  ((Int.negOfNat 53248129361474090460833120256).rawCast)*x 8 +
  ((Int.negOfNat 13589913994292416089144950784).rawCast)*x 9

def firstControlDefectForm27 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 941464317308262061180540944384).rawCast)*x 2 +
  (Nat.rawCast 40127082886973905971663863808)*x 3 +
  (Nat.rawCast 75893776774236131729174691840)*x 4 +
  ((Int.negOfNat 180417994146251691129764315136).rawCast)*x 5 +
  (Nat.rawCast 77271323811611086006813458432)*x 6 +
  ((Int.negOfNat 48081614897878601790501421056).rawCast)*x 7 +
  (Nat.rawCast 8164921096935432341472411648)*x 8 +
  (Nat.rawCast 8028718843332987520750190592)*x 9

def firstControlDefectForm28 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 147218663140615591239729807360).rawCast)*x 2 +
  (Nat.rawCast 54454873503048092335617343488)*x 3 +
  ((Int.negOfNat 11672417252953617477113217024).rawCast)*x 4 +
  (Nat.rawCast 37820311125297990784153288704)*x 5 +
  ((Int.negOfNat 5476517783764711254496641024).rawCast)*x 6 +
  (Nat.rawCast 5249926560140394609128767488)*x 7 +
  (Nat.rawCast 4702291039692959453169057792)*x 8 +
  ((Int.negOfNat 3119195605086650297695076352).rawCast)*x 9

def firstControlDefectForm29 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 7110964870469884906775248896)*x 3 +
  (Nat.rawCast 6337239637252892619033280512)*x 4 +
  (Nat.rawCast 2245816634882798766130200576)*x 5 +
  ((Int.negOfNat 5192221511640964976458334208).rawCast)*x 6 +
  (Nat.rawCast 1930571804575234928658087936)*x 7 +
  ((Int.negOfNat 2626540209630869801800826880).rawCast)*x 8 +
  (Nat.rawCast 839793239101565538253406208)*x 9

def firstControlDefectForm30 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 2665337157926557449040429056)*x 3 +
  ((Int.negOfNat 957575086376597352012054528).rawCast)*x 4 +
  ((Int.negOfNat 1874519269138752174947303424).rawCast)*x 5 +
  (Nat.rawCast 959941739463083761361485824)*x 6 +
  ((Int.negOfNat 602910435930010692945444864).rawCast)*x 7 +
  (Nat.rawCast 662719215027835149691650048)*x 8 +
  ((Int.negOfNat 162882277681715682874490880).rawCast)*x 9

def firstControlDefectForm31 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 179431623407588832662519808).rawCast)*x 4 +
  (Nat.rawCast 204765320452249233804754944)*x 5 +
  (Nat.rawCast 19637788533169818842431488)*x 6 +
  (Nat.rawCast 80111494971304267172806656)*x 7 +
  ((Int.negOfNat 107880580979130037740503040).rawCast)*x 8 +
  (Nat.rawCast 23310957984301767211352064)*x 9

def firstControlDefectForm32 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 8788182855032918230695936).rawCast)*x 4 +
  ((Int.negOfNat 3095860036221671848280064).rawCast)*x 5 +
  ((Int.negOfNat 17657466047887678503911424).rawCast)*x 6 +
  ((Int.negOfNat 7594737897450596953227264).rawCast)*x 7 +
  (Nat.rawCast 12515811467377633526808576)*x 8 +
  ((Int.negOfNat 2484713602444454409535488).rawCast)*x 9

def firstControlDefectForm33 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 1424906763160005289967616)*x 5 +
  (Nat.rawCast 1888130362720560800071680)*x 6 +
  (Nat.rawCast 635944815421842366922752)*x 7 +
  ((Int.negOfNat 1065197412815977096151040).rawCast)*x 8 +
  (Nat.rawCast 195683968256846120091648)*x 9

def firstControlDefectForm34 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 35971081410618285096960).rawCast)*x 5 +
  ((Int.negOfNat 155578159151672174051328).rawCast)*x 6 +
  ((Int.negOfNat 47632262178620150120448).rawCast)*x 7 +
  (Nat.rawCast 65858092060474160971776)*x 8 +
  ((Int.negOfNat 10977845186746619265024).rawCast)*x 9

def firstControlDefectForm35 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 4133519004202627497984)*x 6 +
  (Nat.rawCast 3608721611546494500864)*x 7 +
  ((Int.negOfNat 2740570564064559759360).rawCast)*x 8 +
  (Nat.rawCast 395029566027536007168)*x 9

def firstControlDefectForm36 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 105178600615842938880).rawCast)*x 7 +
  (Nat.rawCast 52613647206212173824)*x 8 +
  ((Int.negOfNat 6579749263062859776).rawCast)*x 9

def firstControlDefectClockForm (A : ℕ) (x : ℕ → ℝ) : ℝ :=
  (4/5)^(4-4)*firstControlDefectForm4 x*degreeElevationCoefficient 32 (4-4) A +
  (4/5)^(5-4)*firstControlDefectForm5 x*degreeElevationCoefficient 32 (5-4) A +
  (4/5)^(6-4)*firstControlDefectForm6 x*degreeElevationCoefficient 32 (6-4) A +
  (4/5)^(7-4)*firstControlDefectForm7 x*degreeElevationCoefficient 32 (7-4) A +
  (4/5)^(8-4)*firstControlDefectForm8 x*degreeElevationCoefficient 32 (8-4) A +
  (4/5)^(9-4)*firstControlDefectForm9 x*degreeElevationCoefficient 32 (9-4) A +
  (4/5)^(10-4)*firstControlDefectForm10 x*degreeElevationCoefficient 32 (10-4) A +
  (4/5)^(11-4)*firstControlDefectForm11 x*degreeElevationCoefficient 32 (11-4) A +
  (4/5)^(12-4)*firstControlDefectForm12 x*degreeElevationCoefficient 32 (12-4) A +
  (4/5)^(13-4)*firstControlDefectForm13 x*degreeElevationCoefficient 32 (13-4) A +
  (4/5)^(14-4)*firstControlDefectForm14 x*degreeElevationCoefficient 32 (14-4) A +
  (4/5)^(15-4)*firstControlDefectForm15 x*degreeElevationCoefficient 32 (15-4) A +
  (4/5)^(16-4)*firstControlDefectForm16 x*degreeElevationCoefficient 32 (16-4) A +
  (4/5)^(17-4)*firstControlDefectForm17 x*degreeElevationCoefficient 32 (17-4) A +
  (4/5)^(18-4)*firstControlDefectForm18 x*degreeElevationCoefficient 32 (18-4) A +
  (4/5)^(19-4)*firstControlDefectForm19 x*degreeElevationCoefficient 32 (19-4) A +
  (4/5)^(20-4)*firstControlDefectForm20 x*degreeElevationCoefficient 32 (20-4) A +
  (4/5)^(21-4)*firstControlDefectForm21 x*degreeElevationCoefficient 32 (21-4) A +
  (4/5)^(22-4)*firstControlDefectForm22 x*degreeElevationCoefficient 32 (22-4) A +
  (4/5)^(23-4)*firstControlDefectForm23 x*degreeElevationCoefficient 32 (23-4) A +
  (4/5)^(24-4)*firstControlDefectForm24 x*degreeElevationCoefficient 32 (24-4) A +
  (4/5)^(25-4)*firstControlDefectForm25 x*degreeElevationCoefficient 32 (25-4) A +
  (4/5)^(26-4)*firstControlDefectForm26 x*degreeElevationCoefficient 32 (26-4) A +
  (4/5)^(27-4)*firstControlDefectForm27 x*degreeElevationCoefficient 32 (27-4) A +
  (4/5)^(28-4)*firstControlDefectForm28 x*degreeElevationCoefficient 32 (28-4) A +
  (4/5)^(29-4)*firstControlDefectForm29 x*degreeElevationCoefficient 32 (29-4) A +
  (4/5)^(30-4)*firstControlDefectForm30 x*degreeElevationCoefficient 32 (30-4) A +
  (4/5)^(31-4)*firstControlDefectForm31 x*degreeElevationCoefficient 32 (31-4) A +
  (4/5)^(32-4)*firstControlDefectForm32 x*degreeElevationCoefficient 32 (32-4) A +
  (4/5)^(33-4)*firstControlDefectForm33 x*degreeElevationCoefficient 32 (33-4) A +
  (4/5)^(34-4)*firstControlDefectForm34 x*degreeElevationCoefficient 32 (34-4) A +
  (4/5)^(35-4)*firstControlDefectForm35 x*degreeElevationCoefficient 32 (35-4) A +
  (4/5)^(36-4)*firstControlDefectForm36 x*degreeElevationCoefficient 32 (36-4) A

def firstControlDefectTensorCoefficient (A B : ℕ) : ℝ :=
  firstControlDefectClockForm A (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)

end
end HTGeometry.ThetaRatioKineticContraction
