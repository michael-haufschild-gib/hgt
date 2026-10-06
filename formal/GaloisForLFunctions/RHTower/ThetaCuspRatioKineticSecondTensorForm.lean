import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSecondDefect
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def secondControlDefectForm4 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 130038986873871845011936293660131328)*x 0

def secondControlDefectForm5 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 1758948401399213903582506708981776384)*x 0 +
  ((Int.negOfNat 1140692867314665307122248190001152).rawCast)*x 1

def secondControlDefectForm6 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 7774392237183101400691682538952851456)*x 0 +
  ((Int.negOfNat 240781252742337268578387888772743168).rawCast)*x 1 +
  ((Int.negOfNat 903048519957443368138446483750912).rawCast)*x 2

def secondControlDefectForm7 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 31505746879753170005165307966466818048)*x 0 +
  ((Int.negOfNat 1621447382018325289686479041745387520).rawCast)*x 1 +
  (Nat.rawCast 1093163997843220919325487848751104)*x 2

def secondControlDefectForm8 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 113757006216082650602937504637988634624)*x 0 +
  ((Int.negOfNat 6277246051296345252979230889671131136).rawCast)*x 1 +
  (Nat.rawCast 111431434475801367189504620060737536)*x 2 +
  (Nat.rawCast 602032346638295578758964322500608)*x 3

def secondControlDefectForm9 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 298854329732553137170085449981929455616)*x 0 +
  ((Int.negOfNat 21030745355671234859225820794217037824).rawCast)*x 1 +
  (Nat.rawCast 524290078975253570593696717656293376)*x 2 +
  ((Int.negOfNat 634818464931097494415062891233280).rawCast)*x 3

def secondControlDefectForm10 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 556019912005571066712098557037220200448)*x 0 +
  ((Int.negOfNat 61795527411901378600365401305258131456).rawCast)*x 1 +
  (Nat.rawCast 1925638087744253302134219820788350976)*x 2 +
  ((Int.negOfNat 19263861540092830263798049422704640).rawCast)*x 3 +
  ((Int.negOfNat 170018394189518658816188998483968).rawCast)*x 4

def secondControlDefectForm11 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 740766601262710799648456057839215968256)*x 0 +
  ((Int.negOfNat 137332454125650468710931074096578953216).rawCast)*x 1 +
  (Nat.rawCast 5582847043458912139532302270473437184)*x 2 +
  ((Int.negOfNat 56905020843243434963621939263832064).rawCast)*x 3 +
  ((Int.negOfNat 237613786098559744804405641216000).rawCast)*x 4

def secondControlDefectForm12 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 697300433842904519914784531766589784064)*x 0 +
  ((Int.negOfNat 213987599101750670863476911326428659712).rawCast)*x 1 +
  (Nat.rawCast 13723568135814364389896331954210471936)*x 2 +
  ((Int.negOfNat 411992616869529519991834731092115456).rawCast)*x 3 +
  (Nat.rawCast 3021441893763693765409909216641024)*x 4 +
  (Nat.rawCast 26323430794369919853144016158720)*x 5

def secondControlDefectForm13 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 431310342166199892156995189819352023040)*x 0 +
  ((Int.negOfNat 225675733622508087903148528488060813312).rawCast)*x 1 +
  (Nat.rawCast 25899572298520979585902342916416733184)*x 2 +
  ((Int.negOfNat 993514261869199596555244935365787648).rawCast)*x 3 +
  ((Int.negOfNat 7573623886895904710738165442281472).rawCast)*x 4 +
  (Nat.rawCast 183994057775740057054009538641920)*x 5

def secondControlDefectForm14 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 125976772546417790886434057824229130240)*x 0 +
  ((Int.negOfNat 149233659778975568528206631094844391424).rawCast)*x 1 +
  (Nat.rawCast 32511657677779654709701009873135730688)*x 2 +
  ((Int.negOfNat 1534487740012921561093606451397525504).rawCast)*x 3 +
  (Nat.rawCast 81528279835329247933514214430212096)*x 4 +
  ((Int.negOfNat 1024075433771376129388945128554496).rawCast)*x 5 +
  ((Int.negOfNat 2408679941968489398326903439360).rawCast)*x 6

def secondControlDefectForm15 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 47555885604180354397471738393251545088).rawCast)*x 0 +
  ((Int.negOfNat 42309424806338251042220564060842229760).rawCast)*x 1 +
  (Nat.rawCast 23916235431426869918385703455408783360)*x 2 +
  ((Int.negOfNat 2078214157684190457407956321849835520).rawCast)*x 3 +
  (Nat.rawCast 128829954641365702639625645020151808)*x 4 +
  (Nat.rawCast 3873345204101231032533380493213696)*x 5 +
  ((Int.negOfNat 39773704841244337908137141993472).rawCast)*x 6

def secondControlDefectForm16 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 74879144169679892487631294031430942720).rawCast)*x 0 +
  (Nat.rawCast 22195038221108659472732856727564713984)*x 1 +
  (Nat.rawCast 6462843486921081218441171492696752128)*x 2 +
  ((Int.negOfNat 1864000409211075198255861105829085184).rawCast)*x 3 +
  (Nat.rawCast 17832864333023922520738622726995968)*x 4 +
  ((Int.negOfNat 13718087601780172480876211783860224).rawCast)*x 5 +
  (Nat.rawCast 224051642753002109784092351397888)*x 6 +
  (Nat.rawCast 129992250836394665941451931648)*x 7

def secondControlDefectForm17 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 41407944616253997022514133059776806912).rawCast)*x 0 +
  (Nat.rawCast 30224172755946174179656278856081342464)*x 1 +
  ((Int.negOfNat 4899031413805804042710238804737785856).rawCast)*x 2 +
  ((Int.negOfNat 526632153968963046067473979306672128).rawCast)*x 3 +
  ((Int.negOfNat 31713427617382815989613712474374144).rawCast)*x 4 +
  ((Int.negOfNat 7682275973922908365368417614561280).rawCast)*x 5 +
  ((Int.negOfNat 719160607008685125285427160285184).rawCast)*x 6 +
  (Nat.rawCast 4010836110413674352580916936704)*x 7

def secondControlDefectForm18 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 12785955266103779312845148150921428992).rawCast)*x 0 +
  (Nat.rawCast 14663793953148218571190990422820257792)*x 1 +
  ((Int.negOfNat 5656533253485481724790020857518882816).rawCast)*x 2 +
  (Nat.rawCast 589036684151265248851807839537070080)*x 3 +
  ((Int.negOfNat 11412812561022304613703459123757056).rawCast)*x 4 +
  (Nat.rawCast 19668795557165321987655302759055360)*x 5 +
  (Nat.rawCast 1757863117437459201155720678473728)*x 6 +
  ((Int.negOfNat 24152943513735509812736050593792).rawCast)*x 7 +
  ((Int.negOfNat 3823301495188078410042703872).rawCast)*x 8

def secondControlDefectForm19 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 1944341569687167939430596150275604480).rawCast)*x 0 +
  (Nat.rawCast 2974475643225247733318670398269685760)*x 1 +
  ((Int.negOfNat 2224614610843551186209738915668033536).rawCast)*x 2 +
  (Nat.rawCast 599866757440443400834120835250782208)*x 3 +
  ((Int.negOfNat 28052692530766247998195393294761984).rawCast)*x 4 +
  (Nat.rawCast 13115104523096484713009273691439104)*x 5 +
  ((Int.negOfNat 616154241637531455438292179222528).rawCast)*x 6 +
  (Nat.rawCast 73048616791786345302717735370752)*x 7 +
  ((Int.negOfNat 194672562607694153254038405120).rawCast)*x 8

def secondControlDefectForm20 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 65368467961443531002179820250464256)*x 0 +
  ((Int.negOfNat 425011822391234504310781653270134784).rawCast)*x 1 +
  ((Int.negOfNat 124493224812060157287252735264030720).rawCast)*x 2 +
  (Nat.rawCast 169014405356255340317350041848119296)*x 3 +
  ((Int.negOfNat 29554352669431875173651694558904320).rawCast)*x 4 +
  ((Int.negOfNat 2197012478022996624451855177482240).rawCast)*x 5 +
  ((Int.negOfNat 2277225773537599928043317879635968).rawCast)*x 6 +
  ((Int.negOfNat 157036466174389318167253336719360).rawCast)*x 7 +
  (Nat.rawCast 1250813020469492577205600911360)*x 8 +
  (Nat.rawCast 47201253027013313704230912)*x 9

def secondControlDefectForm21 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 86274454164870973220846149469995008)*x 0 +
  ((Int.negOfNat 423378819581003840023201482169909248).rawCast)*x 1 +
  (Nat.rawCast 218780675433811539708274613994651648)*x 2 +
  ((Int.negOfNat 31170300746220232537320360763195392).rawCast)*x 3 +
  ((Int.negOfNat 4134678516793906521576130914287616).rawCast)*x 4 +
  ((Int.negOfNat 2479011786424502027512678937788416).rawCast)*x 5 +
  (Nat.rawCast 213700378028323091562527012683776)*x 6 +
  (Nat.rawCast 153254877239551852070817547419648)*x 7 +
  ((Int.negOfNat 3858049785121819118510782021632).rawCast)*x 8 +
  (Nat.rawCast 3645934506017492197252792320)*x 9

def secondControlDefectForm22 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 14922986513431215699346573806796800)*x 0 +
  ((Int.negOfNat 104583987148319550985434799571730432).rawCast)*x 1 +
  (Nat.rawCast 77173119217332430649920719962505216)*x 2 +
  ((Int.negOfNat 27703390079101738614996189906468864).rawCast)*x 3 +
  (Nat.rawCast 5151920973137809357406211221225472)*x 4 +
  ((Int.negOfNat 278267181577235940909552651730944).rawCast)*x 5 +
  (Nat.rawCast 740521640956597448889924788944896)*x 6 +
  (Nat.rawCast 49250618132944441862780023209984)*x 7 +
  (Nat.rawCast 8324195026726294256406044344320)*x 8 +
  ((Int.negOfNat 25010285206909622720573472768).rawCast)*x 9

def secondControlDefectForm23 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 959756591526204365441714595299328)*x 0 +
  ((Int.negOfNat 6596335689289921690181520058220544).rawCast)*x 1 +
  (Nat.rawCast 5609553025378871292062572021284864)*x 2 +
  ((Int.negOfNat 3522183362246853034089255555563520).rawCast)*x 3 +
  (Nat.rawCast 1429248272986372608929556131217408)*x 4 +
  ((Int.negOfNat 36099477035295225478259983515648).rawCast)*x 5 +
  (Nat.rawCast 3594196897497916462304071778304)*x 6 +
  ((Int.negOfNat 86184930067049957682954928914432).rawCast)*x 7 +
  ((Int.negOfNat 11314062853041211777903541354496).rawCast)*x 8 +
  (Nat.rawCast 81829132286813731755663556608)*x 9

def secondControlDefectForm24 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 6795916552156973029272946999296)*x 0 +
  (Nat.rawCast 2327353156348602421319077397004288)*x 1 +
  ((Int.negOfNat 1676177330014822204356096140771328).rawCast)*x 2 +
  (Nat.rawCast 691841233421231172330908729475072)*x 3 +
  ((Int.negOfNat 241519490193777894555853252460544).rawCast)*x 4 +
  (Nat.rawCast 69257840620812448924182069116928)*x 5 +
  ((Int.negOfNat 94787079601426462229662248468480).rawCast)*x 6 +
  (Nat.rawCast 590477410196635761249764769792)*x 7 +
  (Nat.rawCast 6156801582352647000536402362368)*x 8 +
  ((Int.negOfNat 188968370912602062218065870848).rawCast)*x 9

def secondControlDefectForm25 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 574809545898386061849102177533952)*x 1 +
  ((Int.negOfNat 228671290473248662455652781654016).rawCast)*x 2 +
  (Nat.rawCast 52061093266491446004422912507904)*x 3 +
  ((Int.negOfNat 30299633425119274820496248537088).rawCast)*x 4 +
  (Nat.rawCast 36306103075664442162658834120704)*x 5 +
  ((Int.negOfNat 9912500505628324507980643958784).rawCast)*x 6 +
  (Nat.rawCast 16017731338841368856694727114752)*x 7 +
  (Nat.rawCast 260608927420034913404121513984)*x 8 +
  (Nat.rawCast 308285679951131256515891036160)*x 9

def secondControlDefectForm26 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 42194574795616972925771288936448)*x 1 +
  ((Int.negOfNat 1971876127594541595148469403648).rawCast)*x 2 +
  ((Int.negOfNat 19739450930493407236542934548480).rawCast)*x 3 +
  (Nat.rawCast 22465613102293409239429539692544)*x 4 +
  ((Int.negOfNat 14277665925941857950984138915840).rawCast)*x 5 +
  (Nat.rawCast 4941784138679517076012979453952)*x 6 +
  ((Int.negOfNat 1503481358166785462967472226304).rawCast)*x 7 +
  ((Int.negOfNat 1362032223451667916348658286592).rawCast)*x 8 +
  ((Int.negOfNat 311869851546400395890685640704).rawCast)*x 9

def secondControlDefectForm27 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 9570107894256176615850088857600).rawCast)*x 2 +
  (Nat.rawCast 11170511944468942139996837511168)*x 3 +
  ((Int.negOfNat 3281522017713021480966738149376).rawCast)*x 4 +
  ((Int.negOfNat 3446227125949393793047968350208).rawCast)*x 5 +
  (Nat.rawCast 2347515265517259101889770815488)*x 6 +
  ((Int.negOfNat 1295125425300541787618395815936).rawCast)*x 7 +
  (Nat.rawCast 287739652484487637423727050752)*x 8 +
  (Nat.rawCast 192452914012049866022744752128)*x 9

def secondControlDefectForm28 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 1828162379186636120525025312768).rawCast)*x 2 +
  (Nat.rawCast 2561866127556382276138869719040)*x 3 +
  ((Int.negOfNat 1417103141566315086035099320320).rawCast)*x 4 +
  (Nat.rawCast 1469588259992600167462308151296)*x 5 +
  ((Int.negOfNat 290974872376545380798973345792).rawCast)*x 6 +
  (Nat.rawCast 130584668398555714759308607488)*x 7 +
  (Nat.rawCast 120024604305425917737519022080)*x 8 +
  ((Int.negOfNat 73386807631389179512495276032).rawCast)*x 9

def secondControlDefectForm29 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 127602760846804194470601424896).rawCast)*x 3 +
  (Nat.rawCast 91964427621609992678163873792)*x 4 +
  (Nat.rawCast 38851416574713583290279788544)*x 5 +
  ((Int.negOfNat 209024258819998370772446871552).rawCast)*x 6 +
  (Nat.rawCast 76205860977618501057556512768)*x 7 +
  ((Int.negOfNat 68462024096603944640575438848).rawCast)*x 8 +
  (Nat.rawCast 16968276590556510654899945472)*x 9

def secondControlDefectForm30 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 17087795070468652094246092800).rawCast)*x 3 +
  ((Int.negOfNat 20195402382003431184386752512).rawCast)*x 4 +
  ((Int.negOfNat 50131847146884290308737073152).rawCast)*x 5 +
  (Nat.rawCast 38909869530863513805187448832)*x 6 +
  ((Int.negOfNat 12934528726124886478402093056).rawCast)*x 7 +
  (Nat.rawCast 13451326048919029615240937472)*x 8 +
  ((Int.negOfNat 2020804132935978947281158144).rawCast)*x 9

def secondControlDefectForm31 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 3695761219658585741979549696).rawCast)*x 4 +
  (Nat.rawCast 8097660080582555123985678336)*x 5 +
  (Nat.rawCast 3289375808105849191296663552)*x 6 +
  ((Int.negOfNat 1128564865997045369778733056).rawCast)*x 7 +
  ((Int.negOfNat 1091212558811625801627205632).rawCast)*x 8 +
  ((Int.negOfNat 45432066427528369127030784).rawCast)*x 9

def secondControlDefectForm32 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 1131475056681805103165865984)*x 4 +
  ((Int.negOfNat 97257365147095100119056384).rawCast)*x 5 +
  ((Int.negOfNat 1490809047777911895855464448).rawCast)*x 6 +
  (Nat.rawCast 353131554049282318647951360)*x 7 +
  ((Int.negOfNat 35382666224745135124512768).rawCast)*x 8 +
  (Nat.rawCast 66013353765144659830505472)*x 9

def secondControlDefectForm33 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 35844430312610662906331136).rawCast)*x 5 +
  (Nat.rawCast 133792840604298452303609856)*x 6 +
  ((Int.negOfNat 4322568329405116578791424).rawCast)*x 7 +
  (Nat.rawCast 19527342904183692346785792)*x 8 +
  ((Int.negOfNat 13682779164759008168902656).rawCast)*x 9

def secondControlDefectForm34 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 5385204815531382291824640).rawCast)*x 5 +
  ((Int.negOfNat 5990018870765515318493184).rawCast)*x 6 +
  ((Int.negOfNat 4415278685841354714513408).rawCast)*x 7 +
  ((Int.negOfNat 2778767694274031077294080).rawCast)*x 8 +
  (Nat.rawCast 1707807548332507542847488)*x 9

def secondControlDefectForm35 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 574136802026240945946624)*x 6 +
  (Nat.rawCast 578185668936263905837056)*x 7 +
  (Nat.rawCast 264915799668144860037120)*x 8 +
  ((Int.negOfNat 147169212256053413019648).rawCast)*x 9

def secondControlDefectForm36 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 8682493480837834604544).rawCast)*x 6 +
  ((Int.negOfNat 42986372337203555598336).rawCast)*x 7 +
  ((Int.negOfNat 19302750369011856310272).rawCast)*x 8 +
  (Nat.rawCast 8855460475470719483904)*x 9

def secondControlDefectForm37 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 953619312250309312512)*x 7 +
  (Nat.rawCast 1049481166453576040448)*x 8 +
  ((Int.negOfNat 339883883668011220992).rawCast)*x 9

def secondControlDefectForm38 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 23373022359076208640).rawCast)*x 8 +
  (Nat.rawCast 5845960800690241536)*x 9

def secondControlDefectClockForm (A : ℕ) (x : ℕ → ℝ) : ℝ :=
  (4/5)^(4-4)*secondControlDefectForm4 x*degreeElevationCoefficient 34 (4-4) A +
  (4/5)^(5-4)*secondControlDefectForm5 x*degreeElevationCoefficient 34 (5-4) A +
  (4/5)^(6-4)*secondControlDefectForm6 x*degreeElevationCoefficient 34 (6-4) A +
  (4/5)^(7-4)*secondControlDefectForm7 x*degreeElevationCoefficient 34 (7-4) A +
  (4/5)^(8-4)*secondControlDefectForm8 x*degreeElevationCoefficient 34 (8-4) A +
  (4/5)^(9-4)*secondControlDefectForm9 x*degreeElevationCoefficient 34 (9-4) A +
  (4/5)^(10-4)*secondControlDefectForm10 x*degreeElevationCoefficient 34 (10-4) A +
  (4/5)^(11-4)*secondControlDefectForm11 x*degreeElevationCoefficient 34 (11-4) A +
  (4/5)^(12-4)*secondControlDefectForm12 x*degreeElevationCoefficient 34 (12-4) A +
  (4/5)^(13-4)*secondControlDefectForm13 x*degreeElevationCoefficient 34 (13-4) A +
  (4/5)^(14-4)*secondControlDefectForm14 x*degreeElevationCoefficient 34 (14-4) A +
  (4/5)^(15-4)*secondControlDefectForm15 x*degreeElevationCoefficient 34 (15-4) A +
  (4/5)^(16-4)*secondControlDefectForm16 x*degreeElevationCoefficient 34 (16-4) A +
  (4/5)^(17-4)*secondControlDefectForm17 x*degreeElevationCoefficient 34 (17-4) A +
  (4/5)^(18-4)*secondControlDefectForm18 x*degreeElevationCoefficient 34 (18-4) A +
  (4/5)^(19-4)*secondControlDefectForm19 x*degreeElevationCoefficient 34 (19-4) A +
  (4/5)^(20-4)*secondControlDefectForm20 x*degreeElevationCoefficient 34 (20-4) A +
  (4/5)^(21-4)*secondControlDefectForm21 x*degreeElevationCoefficient 34 (21-4) A +
  (4/5)^(22-4)*secondControlDefectForm22 x*degreeElevationCoefficient 34 (22-4) A +
  (4/5)^(23-4)*secondControlDefectForm23 x*degreeElevationCoefficient 34 (23-4) A +
  (4/5)^(24-4)*secondControlDefectForm24 x*degreeElevationCoefficient 34 (24-4) A +
  (4/5)^(25-4)*secondControlDefectForm25 x*degreeElevationCoefficient 34 (25-4) A +
  (4/5)^(26-4)*secondControlDefectForm26 x*degreeElevationCoefficient 34 (26-4) A +
  (4/5)^(27-4)*secondControlDefectForm27 x*degreeElevationCoefficient 34 (27-4) A +
  (4/5)^(28-4)*secondControlDefectForm28 x*degreeElevationCoefficient 34 (28-4) A +
  (4/5)^(29-4)*secondControlDefectForm29 x*degreeElevationCoefficient 34 (29-4) A +
  (4/5)^(30-4)*secondControlDefectForm30 x*degreeElevationCoefficient 34 (30-4) A +
  (4/5)^(31-4)*secondControlDefectForm31 x*degreeElevationCoefficient 34 (31-4) A +
  (4/5)^(32-4)*secondControlDefectForm32 x*degreeElevationCoefficient 34 (32-4) A +
  (4/5)^(33-4)*secondControlDefectForm33 x*degreeElevationCoefficient 34 (33-4) A +
  (4/5)^(34-4)*secondControlDefectForm34 x*degreeElevationCoefficient 34 (34-4) A +
  (4/5)^(35-4)*secondControlDefectForm35 x*degreeElevationCoefficient 34 (35-4) A +
  (4/5)^(36-4)*secondControlDefectForm36 x*degreeElevationCoefficient 34 (36-4) A +
  (4/5)^(37-4)*secondControlDefectForm37 x*degreeElevationCoefficient 34 (37-4) A +
  (4/5)^(38-4)*secondControlDefectForm38 x*degreeElevationCoefficient 34 (38-4) A

def secondControlDefectTensorCoefficient (A B : ℕ) : ℝ :=
  secondControlDefectClockForm A (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)

end
end HTGeometry.ThetaRatioKineticContraction
