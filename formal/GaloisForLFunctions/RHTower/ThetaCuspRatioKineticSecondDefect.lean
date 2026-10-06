import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSecondSource
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstControlPositive
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticControlSubdivision
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def secondControlDefectRow4 (_r : ℝ) : ℝ :=
  Nat.rawCast 130038986873871845011936293660131328

def secondControlDefectRow5 (r : ℝ) : ℝ :=
  Nat.rawCast 1758948401399213903582506708981776384 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 1140692867314665307122248190001152).rawCast)

def secondControlDefectRow6 (r : ℝ) : ℝ :=
  Nat.rawCast 7774392237183101400691682538952851456 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 240781252742337268578387888772743168).rawCast) +
  (r ^ Nat.rawCast 2 * (Int.negOfNat 903048519957443368138446483750912).rawCast)

def secondControlDefectRow7 (r : ℝ) : ℝ :=
  Nat.rawCast 31505746879753170005165307966466818048 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 1621447382018325289686479041745387520).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 1093163997843220919325487848751104)

def secondControlDefectRow8 (r : ℝ) : ℝ :=
  Nat.rawCast 113757006216082650602937504637988634624 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 6277246051296345252979230889671131136).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 111431434475801367189504620060737536) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 602032346638295578758964322500608)

def secondControlDefectRow9 (r : ℝ) : ℝ :=
  Nat.rawCast 298854329732553137170085449981929455616 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 21030745355671234859225820794217037824).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 524290078975253570593696717656293376) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 634818464931097494415062891233280).rawCast)

def secondControlDefectRow10 (r : ℝ) : ℝ :=
  Nat.rawCast 556019912005571066712098557037220200448 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 61795527411901378600365401305258131456).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 1925638087744253302134219820788350976) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 19263861540092830263798049422704640).rawCast) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 170018394189518658816188998483968).rawCast)

def secondControlDefectRow11 (r : ℝ) : ℝ :=
  Nat.rawCast 740766601262710799648456057839215968256 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 137332454125650468710931074096578953216).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 5582847043458912139532302270473437184) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 56905020843243434963621939263832064).rawCast) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 237613786098559744804405641216000).rawCast)

def secondControlDefectRow12 (r : ℝ) : ℝ :=
  Nat.rawCast 697300433842904519914784531766589784064 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 213987599101750670863476911326428659712).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 13723568135814364389896331954210471936) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 411992616869529519991834731092115456).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 3021441893763693765409909216641024) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 26323430794369919853144016158720)

def secondControlDefectRow13 (r : ℝ) : ℝ :=
  Nat.rawCast 431310342166199892156995189819352023040 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 225675733622508087903148528488060813312).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 25899572298520979585902342916416733184) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 993514261869199596555244935365787648).rawCast) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 7573623886895904710738165442281472).rawCast) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 183994057775740057054009538641920)

def secondControlDefectRow14 (r : ℝ) : ℝ :=
  Nat.rawCast 125976772546417790886434057824229130240 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 149233659778975568528206631094844391424).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 32511657677779654709701009873135730688) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 1534487740012921561093606451397525504).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 81528279835329247933514214430212096) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 1024075433771376129388945128554496).rawCast) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 2408679941968489398326903439360).rawCast)

def secondControlDefectRow15 (r : ℝ) : ℝ :=
  (Int.negOfNat 47555885604180354397471738393251545088).rawCast +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 42309424806338251042220564060842229760).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 23916235431426869918385703455408783360) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 2078214157684190457407956321849835520).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 128829954641365702639625645020151808) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 3873345204101231032533380493213696) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 39773704841244337908137141993472).rawCast)

def secondControlDefectRow16 (r : ℝ) : ℝ :=
  (Int.negOfNat 74879144169679892487631294031430942720).rawCast +
  (r ^ Nat.rawCast 1 * Nat.rawCast 22195038221108659472732856727564713984) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 6462843486921081218441171492696752128) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 1864000409211075198255861105829085184).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 17832864333023922520738622726995968) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 13718087601780172480876211783860224).rawCast) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 224051642753002109784092351397888) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 129992250836394665941451931648)

def secondControlDefectRow17 (r : ℝ) : ℝ :=
  (Int.negOfNat 41407944616253997022514133059776806912).rawCast +
  (r ^ Nat.rawCast 1 * Nat.rawCast 30224172755946174179656278856081342464) +
  (r ^ Nat.rawCast 2 * (Int.negOfNat 4899031413805804042710238804737785856).rawCast) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 526632153968963046067473979306672128).rawCast) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 31713427617382815989613712474374144).rawCast) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 7682275973922908365368417614561280).rawCast) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 719160607008685125285427160285184).rawCast) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 4010836110413674352580916936704)

def secondControlDefectRow18 (r : ℝ) : ℝ :=
  (Int.negOfNat 12785955266103779312845148150921428992).rawCast +
  (r ^ Nat.rawCast 1 * Nat.rawCast 14663793953148218571190990422820257792) +
  (r ^ Nat.rawCast 2 * (Int.negOfNat 5656533253485481724790020857518882816).rawCast) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 589036684151265248851807839537070080) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 11412812561022304613703459123757056).rawCast) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 19668795557165321987655302759055360) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 1757863117437459201155720678473728) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 24152943513735509812736050593792).rawCast) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 3823301495188078410042703872).rawCast)

def secondControlDefectRow19 (r : ℝ) : ℝ :=
  (Int.negOfNat 1944341569687167939430596150275604480).rawCast +
  (r ^ Nat.rawCast 1 * Nat.rawCast 2974475643225247733318670398269685760) +
  (r ^ Nat.rawCast 2 * (Int.negOfNat 2224614610843551186209738915668033536).rawCast) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 599866757440443400834120835250782208) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 28052692530766247998195393294761984).rawCast) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 13115104523096484713009273691439104) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 616154241637531455438292179222528).rawCast) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 73048616791786345302717735370752) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 194672562607694153254038405120).rawCast)

def secondControlDefectRow20 (r : ℝ) : ℝ :=
  Nat.rawCast 65368467961443531002179820250464256 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 425011822391234504310781653270134784).rawCast) +
  (r ^ Nat.rawCast 2 * (Int.negOfNat 124493224812060157287252735264030720).rawCast) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 169014405356255340317350041848119296) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 29554352669431875173651694558904320).rawCast) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 2197012478022996624451855177482240).rawCast) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 2277225773537599928043317879635968).rawCast) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 157036466174389318167253336719360).rawCast) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 1250813020469492577205600911360) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 47201253027013313704230912)

def secondControlDefectRow21 (r : ℝ) : ℝ :=
  Nat.rawCast 86274454164870973220846149469995008 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 423378819581003840023201482169909248).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 218780675433811539708274613994651648) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 31170300746220232537320360763195392).rawCast) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 4134678516793906521576130914287616).rawCast) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 2479011786424502027512678937788416).rawCast) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 213700378028323091562527012683776) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 153254877239551852070817547419648) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 3858049785121819118510782021632).rawCast) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 3645934506017492197252792320)

def secondControlDefectRow22 (r : ℝ) : ℝ :=
  Nat.rawCast 14922986513431215699346573806796800 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 104583987148319550985434799571730432).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 77173119217332430649920719962505216) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 27703390079101738614996189906468864).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 5151920973137809357406211221225472) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 278267181577235940909552651730944).rawCast) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 740521640956597448889924788944896) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 49250618132944441862780023209984) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 8324195026726294256406044344320) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 25010285206909622720573472768).rawCast)

def secondControlDefectRow23 (r : ℝ) : ℝ :=
  Nat.rawCast 959756591526204365441714595299328 +
  (r ^ Nat.rawCast 1 * (Int.negOfNat 6596335689289921690181520058220544).rawCast) +
  (r ^ Nat.rawCast 2 * Nat.rawCast 5609553025378871292062572021284864) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 3522183362246853034089255555563520).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 1429248272986372608929556131217408) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 36099477035295225478259983515648).rawCast) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 3594196897497916462304071778304) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 86184930067049957682954928914432).rawCast) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 11314062853041211777903541354496).rawCast) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 81829132286813731755663556608)

def secondControlDefectRow24 (r : ℝ) : ℝ :=
  Nat.rawCast 6795916552156973029272946999296 +
  (r ^ Nat.rawCast 1 * Nat.rawCast 2327353156348602421319077397004288) +
  (r ^ Nat.rawCast 2 * (Int.negOfNat 1676177330014822204356096140771328).rawCast) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 691841233421231172330908729475072) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 241519490193777894555853252460544).rawCast) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 69257840620812448924182069116928) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 94787079601426462229662248468480).rawCast) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 590477410196635761249764769792) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 6156801582352647000536402362368) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 188968370912602062218065870848).rawCast)

def secondControlDefectRow25 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 1 * Nat.rawCast 574809545898386061849102177533952) +
  (r ^ Nat.rawCast 2 * (Int.negOfNat 228671290473248662455652781654016).rawCast) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 52061093266491446004422912507904) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 30299633425119274820496248537088).rawCast) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 36306103075664442162658834120704) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 9912500505628324507980643958784).rawCast) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 16017731338841368856694727114752) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 260608927420034913404121513984) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 308285679951131256515891036160)

def secondControlDefectRow26 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 1 * Nat.rawCast 42194574795616972925771288936448) +
  (r ^ Nat.rawCast 2 * (Int.negOfNat 1971876127594541595148469403648).rawCast) +
  (r ^ Nat.rawCast 3 * (Int.negOfNat 19739450930493407236542934548480).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 22465613102293409239429539692544) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 14277665925941857950984138915840).rawCast) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 4941784138679517076012979453952) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 1503481358166785462967472226304).rawCast) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 1362032223451667916348658286592).rawCast) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 311869851546400395890685640704).rawCast)

def secondControlDefectRow27 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 2 * (Int.negOfNat 9570107894256176615850088857600).rawCast) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 11170511944468942139996837511168) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 3281522017713021480966738149376).rawCast) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 3446227125949393793047968350208).rawCast) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 2347515265517259101889770815488) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 1295125425300541787618395815936).rawCast) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 287739652484487637423727050752) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 192452914012049866022744752128)

def secondControlDefectRow28 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 2 * (Int.negOfNat 1828162379186636120525025312768).rawCast) +
  (r ^ Nat.rawCast 3 * Nat.rawCast 2561866127556382276138869719040) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 1417103141566315086035099320320).rawCast) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 1469588259992600167462308151296) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 290974872376545380798973345792).rawCast) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 130584668398555714759308607488) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 120024604305425917737519022080) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 73386807631389179512495276032).rawCast)

def secondControlDefectRow29 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 3 * (Int.negOfNat 127602760846804194470601424896).rawCast) +
  (r ^ Nat.rawCast 4 * Nat.rawCast 91964427621609992678163873792) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 38851416574713583290279788544) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 209024258819998370772446871552).rawCast) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 76205860977618501057556512768) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 68462024096603944640575438848).rawCast) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 16968276590556510654899945472)

def secondControlDefectRow30 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 3 * (Int.negOfNat 17087795070468652094246092800).rawCast) +
  (r ^ Nat.rawCast 4 * (Int.negOfNat 20195402382003431184386752512).rawCast) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 50131847146884290308737073152).rawCast) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 38909869530863513805187448832) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 12934528726124886478402093056).rawCast) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 13451326048919029615240937472) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 2020804132935978947281158144).rawCast)

def secondControlDefectRow31 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 4 * (Int.negOfNat 3695761219658585741979549696).rawCast) +
  (r ^ Nat.rawCast 5 * Nat.rawCast 8097660080582555123985678336) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 3289375808105849191296663552) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 1128564865997045369778733056).rawCast) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 1091212558811625801627205632).rawCast) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 45432066427528369127030784).rawCast)

def secondControlDefectRow32 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 4 * Nat.rawCast 1131475056681805103165865984) +
  (r ^ Nat.rawCast 5 * (Int.negOfNat 97257365147095100119056384).rawCast) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 1490809047777911895855464448).rawCast) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 353131554049282318647951360) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 35382666224745135124512768).rawCast) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 66013353765144659830505472)

def secondControlDefectRow33 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 5 * (Int.negOfNat 35844430312610662906331136).rawCast) +
  (r ^ Nat.rawCast 6 * Nat.rawCast 133792840604298452303609856) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 4322568329405116578791424).rawCast) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 19527342904183692346785792) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 13682779164759008168902656).rawCast)

def secondControlDefectRow34 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 5 * (Int.negOfNat 5385204815531382291824640).rawCast) +
  (r ^ Nat.rawCast 6 * (Int.negOfNat 5990018870765515318493184).rawCast) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 4415278685841354714513408).rawCast) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 2778767694274031077294080).rawCast) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 1707807548332507542847488)

def secondControlDefectRow35 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 6 * Nat.rawCast 574136802026240945946624) +
  (r ^ Nat.rawCast 7 * Nat.rawCast 578185668936263905837056) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 264915799668144860037120) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 147169212256053413019648).rawCast)

def secondControlDefectRow36 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 6 * (Int.negOfNat 8682493480837834604544).rawCast) +
  (r ^ Nat.rawCast 7 * (Int.negOfNat 42986372337203555598336).rawCast) +
  (r ^ Nat.rawCast 8 * (Int.negOfNat 19302750369011856310272).rawCast) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 8855460475470719483904)

def secondControlDefectRow37 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 7 * Nat.rawCast 953619312250309312512) +
  (r ^ Nat.rawCast 8 * Nat.rawCast 1049481166453576040448) +
  (r ^ Nat.rawCast 9 * (Int.negOfNat 339883883668011220992).rawCast)

def secondControlDefectRow38 (r : ℝ) : ℝ :=
  (r ^ Nat.rawCast 8 * (Int.negOfNat 23373022359076208640).rawCast) +
  (r ^ Nat.rawCast 9 * Nat.rawCast 5845960800690241536)

def secondControlDefectQuotient (h r : ℝ) : ℝ :=
  h^(4-4)*secondControlDefectRow4 r +
  h^(5-4)*secondControlDefectRow5 r +
  h^(6-4)*secondControlDefectRow6 r +
  h^(7-4)*secondControlDefectRow7 r +
  h^(8-4)*secondControlDefectRow8 r +
  h^(9-4)*secondControlDefectRow9 r +
  h^(10-4)*secondControlDefectRow10 r +
  h^(11-4)*secondControlDefectRow11 r +
  h^(12-4)*secondControlDefectRow12 r +
  h^(13-4)*secondControlDefectRow13 r +
  h^(14-4)*secondControlDefectRow14 r +
  h^(15-4)*secondControlDefectRow15 r +
  h^(16-4)*secondControlDefectRow16 r +
  h^(17-4)*secondControlDefectRow17 r +
  h^(18-4)*secondControlDefectRow18 r +
  h^(19-4)*secondControlDefectRow19 r +
  h^(20-4)*secondControlDefectRow20 r +
  h^(21-4)*secondControlDefectRow21 r +
  h^(22-4)*secondControlDefectRow22 r +
  h^(23-4)*secondControlDefectRow23 r +
  h^(24-4)*secondControlDefectRow24 r +
  h^(25-4)*secondControlDefectRow25 r +
  h^(26-4)*secondControlDefectRow26 r +
  h^(27-4)*secondControlDefectRow27 r +
  h^(28-4)*secondControlDefectRow28 r +
  h^(29-4)*secondControlDefectRow29 r +
  h^(30-4)*secondControlDefectRow30 r +
  h^(31-4)*secondControlDefectRow31 r +
  h^(32-4)*secondControlDefectRow32 r +
  h^(33-4)*secondControlDefectRow33 r +
  h^(34-4)*secondControlDefectRow34 r +
  h^(35-4)*secondControlDefectRow35 r +
  h^(36-4)*secondControlDefectRow36 r +
  h^(37-4)*secondControlDefectRow37 r +
  h^(38-4)*secondControlDefectRow38 r

theorem secondControl_defect_factor (h r : ℝ) :
    reducedKineticControl h (9-r*h^2) (1/3) 1=h^4*secondControlDefectQuotient h r := by
  rw [(reducedKineticDefectControl1Norm h r).property]
  dsimp only [reducedKineticDefectControl1Norm,secondControlDefectQuotient,
    secondControlDefectRow4,secondControlDefectRow5,secondControlDefectRow6,secondControlDefectRow7,secondControlDefectRow8,secondControlDefectRow9,secondControlDefectRow10,secondControlDefectRow11,secondControlDefectRow12,secondControlDefectRow13,secondControlDefectRow14,secondControlDefectRow15,secondControlDefectRow16,secondControlDefectRow17,secondControlDefectRow18,secondControlDefectRow19,secondControlDefectRow20,secondControlDefectRow21,secondControlDefectRow22,secondControlDefectRow23,secondControlDefectRow24,secondControlDefectRow25,secondControlDefectRow26,secondControlDefectRow27,secondControlDefectRow28,secondControlDefectRow29,secondControlDefectRow30,secondControlDefectRow31,secondControlDefectRow32,secondControlDefectRow33,secondControlDefectRow34,secondControlDefectRow35,secondControlDefectRow36,secondControlDefectRow37,secondControlDefectRow38]
  norm_num [Nat.rawCast,Int.rawCast]
  ring_nf (config := {mode := .raw})

end
end HTGeometry.ThetaRatioKineticContraction
