import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeTerminalSource
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSecondControlPositive
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeTerminalRow4 (r : ℝ) : ℝ :=
  (Nat.rawCast 41064943223327951056400934840041472)*r^0

def slopeTerminalRow5 (r : ℝ) : ℝ :=
  (Nat.rawCast 112928593864151865405102570810114048)*r^0 +
  (Nat.rawCast 3422078601943995921366744570003456)*r^1

def slopeTerminalRow6 (r : ℝ) : ℝ :=
  (Nat.rawCast 602285833942143282160547044320608256)*r^0 +
  ((Int.negOfNat 66730532737907920466651519115067392).rawCast)*r^1

def slopeTerminalRow7 (r : ℝ) : ℝ :=
  (Nat.rawCast 2414371511410432011299831814819938304)*r^0 +
  ((Int.negOfNat 4467713730315772452895472077504512).rawCast)*r^1 +
  ((Int.negOfNat 3279491993529662757976463546253312).rawCast)*r^2

def slopeTerminalRow8 (r : ℝ) : ℝ :=
  ((Int.negOfNat 902224686219938332083302637835911168).rawCast)*r^0 +
  ((Int.negOfNat 551160613347359602353831837249306624).rawCast)*r^1 +
  (Nat.rawCast 41270901657704210070186896318791680)*r^2

def slopeTerminalRow9 (r : ℝ) : ℝ :=
  (Nat.rawCast 26753987423012303822910896989557227520)*r^0 +
  ((Int.negOfNat 1949335850038078053210829535934676992).rawCast)*r^1 +
  ((Int.negOfNat 59128554115225231996269684534018048).rawCast)*r^2 +
  (Nat.rawCast 1314965388709961395710369441251328)*r^3

def slopeTerminalRow10 (r : ℝ) : ℝ :=
  (Nat.rawCast 17881754875328541057849945348278059008)*r^0 +
  (Nat.rawCast 3180064679170274247878924035713662976)*r^1 +
  (Nat.rawCast 255407162116862439932382625451212800)*r^2 +
  ((Int.negOfNat 12831474510915777916575382128033792).rawCast)*r^3

def slopeTerminalRow11 (r : ℝ) : ℝ :=
  (Nat.rawCast 15663782994504048543436634891910905856)*r^0 +
  ((Int.negOfNat 17592519480447502810499401853278617600).rawCast)*r^1 +
  (Nat.rawCast 596952845407576538345246662141673472)*r^2 +
  (Nat.rawCast 24658424898612162911745623432626176)*r^3 +
  ((Int.negOfNat 290894284450229077163505421910016).rawCast)*r^4

def slopeTerminalRow12 (r : ℝ) : ℝ :=
  (Nat.rawCast 15646675388681118555938962090192011264)*r^0 +
  (Nat.rawCast 4107601336693064032961521268526415872)*r^1 +
  ((Int.negOfNat 1954497347125787760607866838780477440).rawCast)*r^2 +
  ((Int.negOfNat 26125047477307396703291025999790080).rawCast)*r^3 +
  (Nat.rawCast 1999659827777759790899810468364288)*r^4

def slopeTerminalRow13 (r : ℝ) : ℝ :=
  (Nat.rawCast 2987420717586497305405827856509960192)*r^0 +
  (Nat.rawCast 796138142870244011268833854082777088)*r^1 +
  (Nat.rawCast 6122455637538917699875089493870510080)*r^2 +
  ((Int.negOfNat 281991276372786387843217823543328768).rawCast)*r^3 +
  ((Int.negOfNat 1100392754225451915891970431516672).rawCast)*r^4 +
  (Nat.rawCast 39036914397842698481907070402560)*r^5

def slopeTerminalRow14 (r : ℝ) : ℝ :=
  ((Int.negOfNat 2152146561701933483426884376076484608).rawCast)*r^0 +
  ((Int.negOfNat 1950208337978512383781664792852299776).rawCast)*r^1 +
  ((Int.negOfNat 6026911948945799714655165328404774912).rawCast)*r^2 +
  (Nat.rawCast 830694786256156182400578047019319296)*r^3 +
  ((Int.negOfNat 22745629166545187291420029744054272).rawCast)*r^4 +
  ((Int.negOfNat 103814218688688790083368782921728).rawCast)*r^5

def slopeTerminalRow15 (r : ℝ) : ℝ :=
  ((Int.negOfNat 1084721745789669872271756670160338944).rawCast)*r^0 +
  (Nat.rawCast 3917055475241392409465500168649441280)*r^1 +
  (Nat.rawCast 887913065631881990829529745307205632)*r^2 +
  ((Int.negOfNat 1561984921024069575142870954392158208).rawCast)*r^3 +
  (Nat.rawCast 136717830815721056783802576503046144)*r^4 +
  ((Int.negOfNat 1210288437008223553644197666881536).rawCast)*r^5 +
  ((Int.negOfNat 3263489665734750297582766915584).rawCast)*r^6

def slopeTerminalRow16 (r : ℝ) : ℝ :=
  ((Int.negOfNat 438639841294219316818949422341685248).rawCast)*r^0 +
  (Nat.rawCast 979875119187197895023076387997089792)*r^1 +
  (Nat.rawCast 1007865063910372024375557752126177280)*r^2 +
  (Nat.rawCast 2027351994731580688662154345495658496)*r^3 +
  ((Int.negOfNat 310263503774236487196768321587380224).rawCast)*r^4 +
  (Nat.rawCast 9837932579715253806158428413886464)*r^5 +
  ((Int.negOfNat 12070112513710142644736262930432).rawCast)*r^6

def slopeTerminalRow17 (r : ℝ) : ℝ :=
  ((Int.negOfNat 54414853593689737217299697570414592).rawCast)*r^0 +
  ((Int.negOfNat 970351031578133869326348678089146368).rawCast)*r^1 +
  ((Int.negOfNat 1293217907031718272800569693550149632).rawCast)*r^2 +
  ((Int.negOfNat 1115816009696517367536049355866767360).rawCast)*r^3 +
  (Nat.rawCast 396869160167817402528566229294120960)*r^4 +
  ((Int.negOfNat 37984300424480030512217586822807552).rawCast)*r^5 +
  (Nat.rawCast 299093052667068185939230681202688)*r^6 +
  (Nat.rawCast 166213001843439619299751231488)*r^7

def slopeTerminalRow18 (r : ℝ) : ℝ :=
  (Nat.rawCast 134025126535966014041680101595152384)*r^0 +
  ((Int.negOfNat 250134436167007691987089353143746560).rawCast)*r^1 +
  (Nat.rawCast 570576967300077687401009623773216768)*r^2 +
  ((Int.negOfNat 60893584659012878494438050383265792).rawCast)*r^3 +
  ((Int.negOfNat 405270442954402646509792139503730688).rawCast)*r^4 +
  (Nat.rawCast 79804058529549001955637699463348224)*r^5 +
  ((Int.negOfNat 1768844099951432984926244139171840).rawCast)*r^6 +
  (Nat.rawCast 2148217527608801556642744238080)*r^7

def slopeTerminalRow19 (r : ℝ) : ℝ :=
  (Nat.rawCast 64323922241718032650590332211167232)*r^0 +
  ((Int.negOfNat 50495808725336543774245442813952000).rawCast)*r^1 +
  (Nat.rawCast 340140535375533599250490636546080768)*r^2 +
  (Nat.rawCast 365392638960886352243295626899488768)*r^3 +
  (Nat.rawCast 311676350290914713418662354104614912)*r^4 +
  ((Int.negOfNat 95323805880704026246882653244489728).rawCast)*r^5 +
  (Nat.rawCast 5983589357541736274033800837595136)*r^6 +
  ((Int.negOfNat 30913435595461829212240393273344).rawCast)*r^7 +
  ((Int.negOfNat 4717641026226225406543921152).rawCast)*r^8

def slopeTerminalRow20 (r : ℝ) : ℝ :=
  ((Int.negOfNat 1469386110204629941718266241089536).rawCast)*r^0 +
  ((Int.negOfNat 53830214345482205314363432737177600).rawCast)*r^1 +
  ((Int.negOfNat 172431301824030981110693860183375872).rawCast)*r^2 +
  ((Int.negOfNat 237643769561089161142349792695812096).rawCast)*r^3 +
  ((Int.negOfNat 99588691696285535863475164793536512).rawCast)*r^4 +
  (Nat.rawCast 72781475388588674431742762199023616)*r^5 +
  ((Int.negOfNat 12525120985906891915906423222960128).rawCast)*r^6 +
  (Nat.rawCast 166428963253181351825903739469824)*r^7 +
  ((Int.negOfNat 121382369642796171627218337792).rawCast)*r^8

def slopeTerminalRow21 (r : ℝ) : ℝ :=
  ((Int.negOfNat 7725767041418665994191631781199872).rawCast)*r^0 +
  (Nat.rawCast 4544941781595885955468204047335424)*r^1 +
  ((Int.negOfNat 39057938318123467301929111523426304).rawCast)*r^2 +
  (Nat.rawCast 26909203653341260531393993566584832)*r^3 +
  ((Int.negOfNat 45481258803554656963422991461384192).rawCast)*r^4 +
  ((Int.negOfNat 45165057216846646736312355426140160).rawCast)*r^5 +
  (Nat.rawCast 16043064919086393131698216545288192)*r^6 +
  ((Int.negOfNat 539158952625704421372844063064064).rawCast)*r^7 +
  (Nat.rawCast 1528664749085803389552980656128)*r^8 +
  (Nat.rawCast 57138358927437169220911104)*r^9

def slopeTerminalRow22 (r : ℝ) : ℝ :=
  ((Int.negOfNat 2191728377994939060580612527095808).rawCast)*r^0 +
  (Nat.rawCast 12848011642674518570692230858670080)*r^1 +
  (Nat.rawCast 7687823324913306650816452711415808)*r^2 +
  (Nat.rawCast 59156626235013668285734363657666560)*r^3 +
  (Nat.rawCast 56030129944722341038182195114541056)*r^4 +
  (Nat.rawCast 23211768040337614525861441094811648)*r^5 +
  ((Int.negOfNat 12233993707153354952658196975583232).rawCast)*r^6 +
  (Nat.rawCast 1151714623736823987355476880785408)*r^7 +
  ((Int.negOfNat 8031556742875716151109738299392).rawCast)*r^8 +
  (Nat.rawCast 2441474461670284043168514048)*r^9

def slopeTerminalRow23 (r : ℝ) : ℝ :=
  ((Int.negOfNat 260941345461925785202495894585344).rawCast)*r^0 +
  (Nat.rawCast 2659264531613155960285558248308736)*r^1 +
  ((Int.negOfNat 5996039460442971571361466808270848).rawCast)*r^2 +
  ((Int.negOfNat 16651566768485604877036589345144832).rawCast)*r^3 +
  ((Int.negOfNat 21303521104475948836643810876325888).rawCast)*r^4 +
  ((Int.negOfNat 3296821366543655126367418649149440).rawCast)*r^5 +
  (Nat.rawCast 5516261678667665376714531979395072)*r^6 +
  ((Int.negOfNat 1616119156586205391927376779149312).rawCast)*r^7 +
  (Nat.rawCast 25976899179781843108116899561472)*r^8 +
  ((Int.negOfNat 29605070998077873507155312640).rawCast)*r^9

def slopeTerminalRow24 (r : ℝ) : ℝ :=
  ((Int.negOfNat 11871721621789613617388502122496).rawCast)*r^0 +
  ((Int.negOfNat 186754230882629623295310122975232).rawCast)*r^1 +
  ((Int.negOfNat 1194872435622790537517945428377600).rawCast)*r^2 +
  ((Int.negOfNat 5224834169163104714275129512689664).rawCast)*r^3 +
  ((Int.negOfNat 2698002297370840567812889937707008).rawCast)*r^4 +
  ((Int.negOfNat 5905022463319590010032473700827136).rawCast)*r^5 +
  ((Int.negOfNat 1884737564376156573523595029905408).rawCast)*r^6 +
  (Nat.rawCast 1411566462412734680798217935781888)*r^7 +
  ((Int.negOfNat 57285127480731937618587360952320).rawCast)*r^8 +
  (Nat.rawCast 156866300672590163741107027968)*r^9

def slopeTerminalRow25 (r : ℝ) : ℝ :=
  ((Int.negOfNat 104219970303532257529594021675008).rawCast)*r^1 +
  (Nat.rawCast 1204337908540694542186763652169728)*r^2 +
  (Nat.rawCast 1774695891681606095711936748453888)*r^3 +
  (Nat.rawCast 5561802017478845713620279685545984)*r^4 +
  (Nat.rawCast 4479816152612742592657139838222336)*r^5 +
  (Nat.rawCast 807076289820122884066746801586176)*r^6 +
  ((Int.negOfNat 667493284966771552916966895255552).rawCast)*r^7 +
  (Nat.rawCast 87382242024127973383197752819712)*r^8 +
  ((Int.negOfNat 519040973585337511676315959296).rawCast)*r^9

def slopeTerminalRow26 (r : ℝ) : ℝ :=
  ((Int.negOfNat 8320351190529349756453228904448).rawCast)*r^1 +
  (Nat.rawCast 429325417533007926134358826549248)*r^2 +
  ((Int.negOfNat 104216817117166259321286911066112).rawCast)*r^3 +
  ((Int.negOfNat 822630654385316750066890196385792).rawCast)*r^4 +
  ((Int.negOfNat 1052656398641826838373436550545408).rawCast)*r^5 +
  ((Int.negOfNat 71620440815148525403626660691968).rawCast)*r^6 +
  (Nat.rawCast 96177055429131564762505968353280)*r^7 +
  ((Int.negOfNat 88315529924825631599224021843968).rawCast)*r^8 +
  (Nat.rawCast 1192451162612540550272249757696)*r^9

def slopeTerminalRow27 (r : ℝ) : ℝ :=
  (Nat.rawCast 48252978874142568931698898108416)*r^2 +
  ((Int.negOfNat 155018103363487243886088872263680).rawCast)*r^3 +
  ((Int.negOfNat 437884334125340653969119620628480).rawCast)*r^4 +
  ((Int.negOfNat 382425911115776238354326202875904).rawCast)*r^5 +
  ((Int.negOfNat 320453666900766006408709517869056).rawCast)*r^6 +
  (Nat.rawCast 15141677359297399356550136463360)*r^7 +
  (Nat.rawCast 51790120027038285669492578058240)*r^8 +
  ((Int.negOfNat 1957675047831482449277642342400).rawCast)*r^9

def slopeTerminalRow28 (r : ℝ) : ℝ :=
  (Nat.rawCast 1653882063716736924077619412992)*r^2 +
  (Nat.rawCast 26425122840615367997178783989760)*r^3 +
  (Nat.rawCast 118109514121143015060406901145600)*r^4 +
  (Nat.rawCast 306345030362284058673252025761792)*r^5 +
  (Nat.rawCast 224708673835629895432328731164672)*r^6 +
  (Nat.rawCast 29747594719173165762951549812736)*r^7 +
  ((Int.negOfNat 9290713662159305831540525629440).rawCast)*r^8 +
  (Nat.rawCast 2241620056816066875693081821184)*r^9

def slopeTerminalRow29 (r : ℝ) : ℝ :=
  (Nat.rawCast 12765823822786524868129188741120)*r^3 +
  (Nat.rawCast 5062737930013550621803004559360)*r^4 +
  ((Int.negOfNat 24189237852706881642083074965504).rawCast)*r^5 +
  ((Int.negOfNat 43020082651271091033375246385152).rawCast)*r^6 +
  ((Int.negOfNat 17305113830059554718088108703744).rawCast)*r^7 +
  ((Int.negOfNat 6615805084875801803167786598400).rawCast)*r^8 +
  ((Int.negOfNat 1618562882674405705904038084608).rawCast)*r^9

def slopeTerminalRow30 (r : ℝ) : ℝ :=
  (Nat.rawCast 1019375458091169223416131616768)*r^3 +
  ((Int.negOfNat 10742745752611324407147902533632).rawCast)*r^4 +
  ((Int.negOfNat 21126238874669944995186191892480).rawCast)*r^5 +
  ((Int.negOfNat 19334112949283487816917673050112).rawCast)*r^6 +
  ((Int.negOfNat 9585193106640775418285956005888).rawCast)*r^7 +
  (Nat.rawCast 1703989788696192134489145606144)*r^8 +
  (Nat.rawCast 493489397766383210618463191040)*r^9

def slopeTerminalRow31 (r : ℝ) : ℝ :=
  ((Int.negOfNat 1320481067540645675052828721152).rawCast)*r^4 +
  (Nat.rawCast 3637870601990124518630580289536)*r^5 +
  (Nat.rawCast 12162212277054309745355976081408)*r^6 +
  (Nat.rawCast 9785222807308042859719019200512)*r^7 +
  (Nat.rawCast 2498739402746942548257036828672)*r^8 +
  (Nat.rawCast 207157547302251363223581229056)*r^9

def slopeTerminalRow32 (r : ℝ) : ℝ :=
  ((Int.negOfNat 20724061466426599763620134912).rawCast)*r^4 +
  ((Int.negOfNat 46863687557319424293539414016).rawCast)*r^5 +
  ((Int.negOfNat 970679047395872004415464407040).rawCast)*r^6 +
  ((Int.negOfNat 1877704730850026003524315250688).rawCast)*r^7 +
  ((Int.negOfNat 1110572684514070610122308059136).rawCast)*r^8 +
  ((Int.negOfNat 187262359788088041518300921856).rawCast)*r^9

def slopeTerminalRow33 (r : ℝ) : ℝ :=
  ((Int.negOfNat 312950812753258274617949159424).rawCast)*r^5 +
  ((Int.negOfNat 772733045509961632577847558144).rawCast)*r^6 +
  ((Int.negOfNat 739982270891543217449012822016).rawCast)*r^7 +
  ((Int.negOfNat 407719894807828382402010415104).rawCast)*r^8 +
  ((Int.negOfNat 37741348585486266370803892224).rawCast)*r^9

def slopeTerminalRow34 (r : ℝ) : ℝ :=
  ((Int.negOfNat 24799058952111668177236131840).rawCast)*r^5 +
  (Nat.rawCast 105765408693268384045414219776)*r^6 +
  (Nat.rawCast 386503730990799623334383321088)*r^7 +
  (Nat.rawCast 364766670772953074535713734656)*r^8 +
  (Nat.rawCast 74088049820451168951554015232)*r^9

def slopeTerminalRow35 (r : ℝ) : ℝ :=
  (Nat.rawCast 12203063558667225414890422272)*r^6 +
  ((Int.negOfNat 32386100537571609416130625536).rawCast)*r^7 +
  ((Int.negOfNat 40155681659450268210809536512).rawCast)*r^8 +
  ((Int.negOfNat 9387850670010248739378167808).rawCast)*r^9

def slopeTerminalRow36 (r : ℝ) : ℝ :=
  ((Int.negOfNat 1155811476564567674767540224).rawCast)*r^6 +
  ((Int.negOfNat 16756566733722812797144793088).rawCast)*r^7 +
  ((Int.negOfNat 31428247798190619611218575360).rawCast)*r^8 +
  ((Int.negOfNat 13925101421023528964692377600).rawCast)*r^9

def slopeTerminalRow37 (r : ℝ) : ℝ :=
  (Nat.rawCast 3607769141811159463939276800)*r^7 +
  (Nat.rawCast 9397829924667977237142700032)*r^8 +
  (Nat.rawCast 4828461550150972394566582272)*r^9

def slopeTerminalRow38 (r : ℝ) : ℝ :=
  (Nat.rawCast 222751525790116780261244928)*r^7 +
  (Nat.rawCast 369423759347673207435952128)*r^8 +
  (Nat.rawCast 661712576478041952743325696)*r^9

def slopeTerminalRow39 (r : ℝ) : ℝ :=
  ((Int.negOfNat 376848028872791602250121216).rawCast)*r^8 +
  ((Int.negOfNat 503453381600997417953525760).rawCast)*r^9

def slopeTerminalRow40 (r : ℝ) : ℝ :=
  (Nat.rawCast 23452266002932235520442368)*r^8 +
  (Nat.rawCast 29125230075179002239123456)*r^9

def slopeTerminalRow41 (r : ℝ) : ℝ :=
  (Nat.rawCast 14913489313416408968724480)*r^9

def slopeTerminalRow42 (r : ℝ) : ℝ :=
  ((Int.negOfNat 1851372572417958975897600).rawCast)*r^9

def slopeTerminalQuotient (h r : ℝ) : ℝ :=
  h^(4-4)*slopeTerminalRow4 r +
  h^(5-4)*slopeTerminalRow5 r +
  h^(6-4)*slopeTerminalRow6 r +
  h^(7-4)*slopeTerminalRow7 r +
  h^(8-4)*slopeTerminalRow8 r +
  h^(9-4)*slopeTerminalRow9 r +
  h^(10-4)*slopeTerminalRow10 r +
  h^(11-4)*slopeTerminalRow11 r +
  h^(12-4)*slopeTerminalRow12 r +
  h^(13-4)*slopeTerminalRow13 r +
  h^(14-4)*slopeTerminalRow14 r +
  h^(15-4)*slopeTerminalRow15 r +
  h^(16-4)*slopeTerminalRow16 r +
  h^(17-4)*slopeTerminalRow17 r +
  h^(18-4)*slopeTerminalRow18 r +
  h^(19-4)*slopeTerminalRow19 r +
  h^(20-4)*slopeTerminalRow20 r +
  h^(21-4)*slopeTerminalRow21 r +
  h^(22-4)*slopeTerminalRow22 r +
  h^(23-4)*slopeTerminalRow23 r +
  h^(24-4)*slopeTerminalRow24 r +
  h^(25-4)*slopeTerminalRow25 r +
  h^(26-4)*slopeTerminalRow26 r +
  h^(27-4)*slopeTerminalRow27 r +
  h^(28-4)*slopeTerminalRow28 r +
  h^(29-4)*slopeTerminalRow29 r +
  h^(30-4)*slopeTerminalRow30 r +
  h^(31-4)*slopeTerminalRow31 r +
  h^(32-4)*slopeTerminalRow32 r +
  h^(33-4)*slopeTerminalRow33 r +
  h^(34-4)*slopeTerminalRow34 r +
  h^(35-4)*slopeTerminalRow35 r +
  h^(36-4)*slopeTerminalRow36 r +
  h^(37-4)*slopeTerminalRow37 r +
  h^(38-4)*slopeTerminalRow38 r +
  h^(39-4)*slopeTerminalRow39 r +
  h^(40-4)*slopeTerminalRow40 r +
  h^(41-4)*slopeTerminalRow41 r +
  h^(42-4)*slopeTerminalRow42 r

theorem slopeTerminal_factor (h r : ℝ) :
    negKineticSlopeControl h (9-r*h^2) (1/3) 18=h^4*slopeTerminalQuotient h r := by
  rw [(negKineticSlopeDefectControl18Norm h r).property]
  dsimp only [negKineticSlopeDefectControl18Norm,slopeTerminalQuotient,
    slopeTerminalRow4,slopeTerminalRow5,slopeTerminalRow6,slopeTerminalRow7,slopeTerminalRow8,slopeTerminalRow9,slopeTerminalRow10,slopeTerminalRow11,slopeTerminalRow12,slopeTerminalRow13,slopeTerminalRow14,slopeTerminalRow15,slopeTerminalRow16,slopeTerminalRow17,slopeTerminalRow18,slopeTerminalRow19,slopeTerminalRow20,slopeTerminalRow21,slopeTerminalRow22,slopeTerminalRow23,slopeTerminalRow24,slopeTerminalRow25,slopeTerminalRow26,slopeTerminalRow27,slopeTerminalRow28,slopeTerminalRow29,slopeTerminalRow30,slopeTerminalRow31,slopeTerminalRow32,slopeTerminalRow33,slopeTerminalRow34,slopeTerminalRow35,slopeTerminalRow36,slopeTerminalRow37,slopeTerminalRow38,slopeTerminalRow39,slopeTerminalRow40,slopeTerminalRow41,slopeTerminalRow42]
  norm_num [Nat.rawCast,Int.rawCast]
  ring_nf (config := {mode := .raw})

end
end HTGeometry.ThetaRatioKineticContraction

