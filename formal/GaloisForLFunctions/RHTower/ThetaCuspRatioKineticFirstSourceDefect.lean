import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstSourceReal
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

theorem reducedKineticControl_zero (h v Z : ℝ) :
    reducedKineticControl h v Z 0=reducedKineticCoefficient h v 0 := by
  simp [reducedKineticControl,kineticControl,degreeElevationCoefficient]

def reducedKineticDefectCoefficient0Norm (h r : ℝ) :
    {c : ℝ // reducedKineticCoefficient h (9-r*h^2) 0=c} := by
  have he := (reducedKineticFullCoefficient0RealNorm h (9-r*h^2)).property
  conv at he =>
    rhs
    dsimp only [reducedKineticFullCoefficient0RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem reducedKineticControl_zero_defect (h r Z : ℝ) :
    reducedKineticControl h (9-r*h^2) Z 0=(reducedKineticDefectCoefficient0Norm h r).val := by
  rw [reducedKineticControl_zero]
  exact (reducedKineticDefectCoefficient0Norm h r).property

def firstControlDefectRow4 (_r : ℝ) : ℝ :=
  Nat.rawCast 6844157203887991842733489140006912

def firstControlDefectRow5 (_r : ℝ) : ℝ :=
  Nat.rawCast 99240279456375881719635592530100224

def firstControlDefectRow6 (r : ℝ) : ℝ :=
  Nat.rawCast 452664952846036349376345490065457152 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 12642679279404207153938250772512768).rawCast) +
  (r ^ Nat.rawCast 2 * (Int.negOfNat 47528869471444387796760341250048).rawCast)

def firstControlDefectRow7 (r : ℝ) : ℝ :=
  Nat.rawCast 1833632098295343518273816125199351808 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 91271272341663706032378775313842176).rawCast)

def firstControlDefectRow8 (r : ℝ) : ℝ :=
  Nat.rawCast 6574832224535303805706046846294556672 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 361105866794795563440086332685156352).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 5853972423232900430300982030630912) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 31685912980962925197840227500032)

def firstControlDefectRow9 (r : ℝ) : ℝ :=
  Nat.rawCast 17404266650154668670158191859985285120 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 1226574453874692166697711003284537344).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 29730188018637935759240200124891136) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 10341929931286510307628407586816).rawCast)

def firstControlDefectRow10 (r : ℝ) : ℝ :=
  Nat.rawCast 33026959250019175387225824774095634432 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 3619882534589966705674186875205582848).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 110096665391478303965545600477298688) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 1002066998022952509381697194688512).rawCast) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 8948336536290455727167842025472).rawCast)

def firstControlDefectRow11 (r : ℝ) : ℝ :=
  Nat.rawCast 45247103285818223259615379135647449088 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 8159172994225738929084518571712708608).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 328458765555396236667224584580235264) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 3434382564681395297991600352788480).rawCast) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 17609397241156286168012672729088).rawCast)

def firstControlDefectRow12 (r : ℝ) : ℝ :=
  Nat.rawCast 44142845697774667431701180780579389440 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 13135044006086548484523653598743101440).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 819272426863941446797132054149464064) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 22695307167816788701149687925702656).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 148180337458136771359074127183872) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 1385443726019469465954948218880)

def firstControlDefectRow13 (r : ℝ) : ℝ :=
  Nat.rawCast 28766196399035179879133836240327016448 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 14608133123338375249029661060409327616).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 1580735345948107647989793481090400256) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 58837634193274680745100130190884864).rawCast) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 306789534649976960913836580274176).rawCast) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 10368755925001102976209398005760)

def firstControlDefectRow14 (r : ℝ) : ℝ :=
  Nat.rawCast 9639698230414223706647814607944548352 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 10557953730691463377216444427912871936).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 2101437317105299357244096155433828352) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 96670963794494169690867399602995200).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 4209003422470314893292353309638656) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 50073575311921365547269545263104).rawCast) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 126772628524657336754047549440).rawCast)

def firstControlDefectRow15 (r : ℝ) : ℝ :=
  (Int.negOfNat 2106563042060527708767209188686299136).rawCast +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 3895017059954659748007075834601930752).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 1741675685131585800982869594234421248) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 135666430225726515768278150195183616).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 7851943321723891749690091040145408) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 181914571638497054341152594984960) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 2150607091043294105649020928000).rawCast)

def firstControlDefectRow16 (r : ℝ) : ℝ :=
  (Int.negOfNat 4592195889645740272853513628844818432).rawCast +
  (r ^ Nat.rawCast 1 * Nat.rawCast 726370637560292854784656799585796096) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 704279258615599125636841670373801984) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 136929313148079949378070104567185408).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 2767047105253265007800774421381120) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 669763123822753340129810596233216).rawCast) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 11135830940772521655108492066816) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 6841697412441824523234312192)

def firstControlDefectRow17 (r : ℝ) : ℝ :=
  (Int.negOfNat 2761000127680334405566091648884015104).rawCast +
  (r ^ Nat.rawCast 1 * Nat.rawCast 1802088961792474771155220640613531648) +
  (r ^ Nat.rawCast 2 * (Int.negOfNat 130812952477209158991530691900997632).rawCast) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 66421213787479284866494827967021056).rawCast) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 702921817894205532282540609503232).rawCast) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 565768060641421697031540855275520).rawCast) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 34200352065990468596265104965632).rawCast) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 214012654966394082053377228800)

def firstControlDefectRow18 (r : ℝ) : ℝ :=
  (Int.negOfNat 928470393140571061766402570780147712).rawCast +
  (r ^ Nat.rawCast 1 * Nat.rawCast 1047705403928376849607957129564520448) +
  (r ^ Nat.rawCast 2 * (Int.negOfNat 329663082219577886270896708924735488).rawCast) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 13105788371585660936354393015451648) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 300987463644630408820775800799232) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 922955601067491977730990092058624) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 83012002421670112131081635364864) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 1211777661849792413833573171200).rawCast) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 201226394483583074212773888).rawCast)

def firstControlDefectRow19 (r : ℝ) : ℝ :=
  (Int.negOfNat 169067586418226575633587492945395712).rawCast +
  (r ^ Nat.rawCast 1 * Nat.rawCast 291592261315377451358018078332944384) +
  (r ^ Nat.rawCast 2 * (Int.negOfNat 176558541669050516868901027920740352).rawCast) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 34344020592059868534381882655113216) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 587659586845971540629754627489792).rawCast) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 876664043783261427340254986108928) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 12520946669515739777211354316800).rawCast) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 3501248301648957187581869555712) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 10328689979812433073134370816).rawCast)

def firstControlDefectRow20 (r : ℝ) : ℝ :=
  (Int.negOfNat 6037748877176762047908028109291520).rawCast +
  (r ^ Nat.rawCast 1 * Nat.rawCast 12626743043300638412607595581800448) +
  (r ^ Nat.rawCast 2 * (Int.negOfNat 36917443749314585490809271751802880).rawCast) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 16597762583378767181251971970498560) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 1647160332819868932117840084860928).rawCast) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 22689887765805112325623089463296) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 124136466782335137552240035758080).rawCast) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 7346009003715564611040190660608).rawCast) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 63101554071369647267373907968) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 2484276475105963879170048)

def firstControlDefectRow21 (r : ℝ) : ℝ :=
  Nat.rawCast 4288875204817921973461372939272192 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 19170961324466691477313617370546176).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 4253425526648566003054345287892992) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 2222045921595566758522702188773376) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 795325968105455929454881753006080).rawCast) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 123789066898933350519532966379520).rawCast) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 16164524781475705956632170070016).rawCast) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 6338891536934490668419774414848) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 186454106991469548745959407616).rawCast) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 192893717139998487034724352)

def firstControlDefectRow22 (r : ℝ) : ℝ :=
  Nat.rawCast 925885107793092624711959609081856 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 6460086279748392535765807458680832).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 4007103848266254446235626716004352) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 704874006705456082565076527087616).rawCast) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 14278667220482802023721697542144).rawCast) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 11206536409744154836180477673472).rawCast) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 33634789181379218214007244587008) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 4022530825072657585731916529664) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 391663329452457058462599217152) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 1266321116365341556721319936).rawCast)

def firstControlDefectRow23 (r : ℝ) : ℝ :=
  Nat.rawCast 71652993396973192331265249902592 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 715997782626613863914459658977280).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 821836424114297251741150614650880) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 254106394523306782594695822311424).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 45675022175516653650194945015808) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 5245213847045331428857960464384) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 4968631858146423090594982133760) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 3445204718035128774690789654528).rawCast) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 506913094971820426014788419584).rawCast) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 3985433421661177766656081920)

def firstControlDefectRow24 (r : ℝ) : ℝ :=
  Nat.rawCast 1327389282474316987658642915328 +
  (r ^ Nat.rawCast 1 * Nat.rawCast 69562514246234485905727313412096) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 84800759608586752217788044017664) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 32741405112031815828565829615616).rawCast) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 1721856978024000056967630422016).rawCast) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 2772924796948008673349235376128) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 3772982169876740838128414097408).rawCast) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 502165794909407394671408185344).rawCast) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 217946181235820485899485970432) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 8988069261962837074227757056).rawCast)

def firstControlDefectRow25 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 1 * Nat.rawCast 27124956396591230717748263780352) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 13823165672257739832102846726144) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 12540083981948556683400506769408).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 800322807516379125723829370880) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 1368106935510856070140753084416) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 669982326665174732331125047296).rawCast) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 629314699087041044777590063104) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 38326243222300795852453576704) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 14268808377082412896968769536)

def firstControlDefectRow26 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 1 * Nat.rawCast 2201730367441141015212673990656) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 459213638400093679759506014208) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 3234297147007249694198656401408).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 1495805387726664399742247632896) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 429883699588965669574331596800).rawCast) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 145435951372546819717123276800) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 11533994441829175637179367424).rawCast) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 53248129361474090460833120256).rawCast) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 13589913994292416089144950784).rawCast)

def firstControlDefectRow27 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 2 * (Int.negOfNat 941464317308262061180540944384).rawCast) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 40127082886973905971663863808) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 75893776774236131729174691840) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 180417994146251691129764315136).rawCast) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 77271323811611086006813458432) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 48081614897878601790501421056).rawCast) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 8164921096935432341472411648) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 8028718843332987520750190592)

def firstControlDefectRow28 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 2 * (Int.negOfNat 147218663140615591239729807360).rawCast) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 54454873503048092335617343488) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 11672417252953617477113217024).rawCast) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 37820311125297990784153288704) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 5476517783764711254496641024).rawCast) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 5249926560140394609128767488) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 4702291039692959453169057792) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 3119195605086650297695076352).rawCast)

def firstControlDefectRow29 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 3 * Nat.rawCast 7110964870469884906775248896) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 6337239637252892619033280512) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 2245816634882798766130200576) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 5192221511640964976458334208).rawCast) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 1930571804575234928658087936) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 2626540209630869801800826880).rawCast) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 839793239101565538253406208)

def firstControlDefectRow30 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 3 * Nat.rawCast 2665337157926557449040429056) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 957575086376597352012054528).rawCast) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 1874519269138752174947303424).rawCast) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 959941739463083761361485824) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 602910435930010692945444864).rawCast) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 662719215027835149691650048) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 162882277681715682874490880).rawCast)

def firstControlDefectRow31 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 4 * (Int.negOfNat 179431623407588832662519808).rawCast) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 204765320452249233804754944) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 19637788533169818842431488) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 80111494971304267172806656) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 107880580979130037740503040).rawCast) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 23310957984301767211352064)

def firstControlDefectRow32 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 4 * (Int.negOfNat 8788182855032918230695936).rawCast) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 3095860036221671848280064).rawCast) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 17657466047887678503911424).rawCast) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 7594737897450596953227264).rawCast) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 12515811467377633526808576) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 2484713602444454409535488).rawCast)

def firstControlDefectRow33 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 5 * Nat.rawCast 1424906763160005289967616) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 1888130362720560800071680) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 635944815421842366922752) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 1065197412815977096151040).rawCast) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 195683968256846120091648)

def firstControlDefectRow34 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 5 * (Int.negOfNat 35971081410618285096960).rawCast) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 155578159151672174051328).rawCast) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 47632262178620150120448).rawCast) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 65858092060474160971776) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 10977845186746619265024).rawCast)

def firstControlDefectRow35 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 6 * Nat.rawCast 4133519004202627497984) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 3608721611546494500864) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 2740570564064559759360).rawCast) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 395029566027536007168)

def firstControlDefectRow36 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 7 * (Int.negOfNat 105178600615842938880).rawCast) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 52613647206212173824) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 6579749263062859776).rawCast)

def firstControlDefectQuotient (h r : ℝ) : ℝ :=
  h^(4-4)*firstControlDefectRow4 r +
  h^(5-4)*firstControlDefectRow5 r +
  h^(6-4)*firstControlDefectRow6 r +
  h^(7-4)*firstControlDefectRow7 r +
  h^(8-4)*firstControlDefectRow8 r +
  h^(9-4)*firstControlDefectRow9 r +
  h^(10-4)*firstControlDefectRow10 r +
  h^(11-4)*firstControlDefectRow11 r +
  h^(12-4)*firstControlDefectRow12 r +
  h^(13-4)*firstControlDefectRow13 r +
  h^(14-4)*firstControlDefectRow14 r +
  h^(15-4)*firstControlDefectRow15 r +
  h^(16-4)*firstControlDefectRow16 r +
  h^(17-4)*firstControlDefectRow17 r +
  h^(18-4)*firstControlDefectRow18 r +
  h^(19-4)*firstControlDefectRow19 r +
  h^(20-4)*firstControlDefectRow20 r +
  h^(21-4)*firstControlDefectRow21 r +
  h^(22-4)*firstControlDefectRow22 r +
  h^(23-4)*firstControlDefectRow23 r +
  h^(24-4)*firstControlDefectRow24 r +
  h^(25-4)*firstControlDefectRow25 r +
  h^(26-4)*firstControlDefectRow26 r +
  h^(27-4)*firstControlDefectRow27 r +
  h^(28-4)*firstControlDefectRow28 r +
  h^(29-4)*firstControlDefectRow29 r +
  h^(30-4)*firstControlDefectRow30 r +
  h^(31-4)*firstControlDefectRow31 r +
  h^(32-4)*firstControlDefectRow32 r +
  h^(33-4)*firstControlDefectRow33 r +
  h^(34-4)*firstControlDefectRow34 r +
  h^(35-4)*firstControlDefectRow35 r +
  h^(36-4)*firstControlDefectRow36 r

theorem firstControl_defect_factor (h r : ℝ) :
    reducedKineticCoefficient h (9-r*h^2) 0 = h^4*firstControlDefectQuotient h r := by
  rw [(reducedKineticDefectCoefficient0Norm h r).property]
  dsimp only [reducedKineticDefectCoefficient0Norm,firstControlDefectQuotient,
    firstControlDefectRow4,firstControlDefectRow5,firstControlDefectRow6,firstControlDefectRow7,firstControlDefectRow8,firstControlDefectRow9,firstControlDefectRow10,firstControlDefectRow11,firstControlDefectRow12,firstControlDefectRow13,firstControlDefectRow14,firstControlDefectRow15,firstControlDefectRow16,firstControlDefectRow17,firstControlDefectRow18,firstControlDefectRow19,firstControlDefectRow20,firstControlDefectRow21,firstControlDefectRow22,firstControlDefectRow23,firstControlDefectRow24,firstControlDefectRow25,firstControlDefectRow26,firstControlDefectRow27,firstControlDefectRow28,firstControlDefectRow29,firstControlDefectRow30,firstControlDefectRow31,firstControlDefectRow32,firstControlDefectRow33,firstControlDefectRow34,firstControlDefectRow35,firstControlDefectRow36]
  norm_num [Nat.rawCast,Int.rawCast]
  ring_nf (config := {mode := .raw})

end
end HTGeometry.ThetaRatioKineticContraction
