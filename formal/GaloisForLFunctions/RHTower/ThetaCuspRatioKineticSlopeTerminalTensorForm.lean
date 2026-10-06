import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeTerminalDefect
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeTerminalForm4 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 41064943223327951056400934840041472)*x 0

def slopeTerminalForm5 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 112928593864151865405102570810114048)*x 0 +
  (Nat.rawCast 3422078601943995921366744570003456)*x 1

def slopeTerminalForm6 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 602285833942143282160547044320608256)*x 0 +
  ((Int.negOfNat 66730532737907920466651519115067392).rawCast)*x 1

def slopeTerminalForm7 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 2414371511410432011299831814819938304)*x 0 +
  ((Int.negOfNat 4467713730315772452895472077504512).rawCast)*x 1 +
  ((Int.negOfNat 3279491993529662757976463546253312).rawCast)*x 2

def slopeTerminalForm8 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 902224686219938332083302637835911168).rawCast)*x 0 +
  ((Int.negOfNat 551160613347359602353831837249306624).rawCast)*x 1 +
  (Nat.rawCast 41270901657704210070186896318791680)*x 2

def slopeTerminalForm9 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 26753987423012303822910896989557227520)*x 0 +
  ((Int.negOfNat 1949335850038078053210829535934676992).rawCast)*x 1 +
  ((Int.negOfNat 59128554115225231996269684534018048).rawCast)*x 2 +
  (Nat.rawCast 1314965388709961395710369441251328)*x 3

def slopeTerminalForm10 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 17881754875328541057849945348278059008)*x 0 +
  (Nat.rawCast 3180064679170274247878924035713662976)*x 1 +
  (Nat.rawCast 255407162116862439932382625451212800)*x 2 +
  ((Int.negOfNat 12831474510915777916575382128033792).rawCast)*x 3

def slopeTerminalForm11 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 15663782994504048543436634891910905856)*x 0 +
  ((Int.negOfNat 17592519480447502810499401853278617600).rawCast)*x 1 +
  (Nat.rawCast 596952845407576538345246662141673472)*x 2 +
  (Nat.rawCast 24658424898612162911745623432626176)*x 3 +
  ((Int.negOfNat 290894284450229077163505421910016).rawCast)*x 4

def slopeTerminalForm12 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 15646675388681118555938962090192011264)*x 0 +
  (Nat.rawCast 4107601336693064032961521268526415872)*x 1 +
  ((Int.negOfNat 1954497347125787760607866838780477440).rawCast)*x 2 +
  ((Int.negOfNat 26125047477307396703291025999790080).rawCast)*x 3 +
  (Nat.rawCast 1999659827777759790899810468364288)*x 4

def slopeTerminalForm13 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 2987420717586497305405827856509960192)*x 0 +
  (Nat.rawCast 796138142870244011268833854082777088)*x 1 +
  (Nat.rawCast 6122455637538917699875089493870510080)*x 2 +
  ((Int.negOfNat 281991276372786387843217823543328768).rawCast)*x 3 +
  ((Int.negOfNat 1100392754225451915891970431516672).rawCast)*x 4 +
  (Nat.rawCast 39036914397842698481907070402560)*x 5

def slopeTerminalForm14 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 2152146561701933483426884376076484608).rawCast)*x 0 +
  ((Int.negOfNat 1950208337978512383781664792852299776).rawCast)*x 1 +
  ((Int.negOfNat 6026911948945799714655165328404774912).rawCast)*x 2 +
  (Nat.rawCast 830694786256156182400578047019319296)*x 3 +
  ((Int.negOfNat 22745629166545187291420029744054272).rawCast)*x 4 +
  ((Int.negOfNat 103814218688688790083368782921728).rawCast)*x 5

def slopeTerminalForm15 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 1084721745789669872271756670160338944).rawCast)*x 0 +
  (Nat.rawCast 3917055475241392409465500168649441280)*x 1 +
  (Nat.rawCast 887913065631881990829529745307205632)*x 2 +
  ((Int.negOfNat 1561984921024069575142870954392158208).rawCast)*x 3 +
  (Nat.rawCast 136717830815721056783802576503046144)*x 4 +
  ((Int.negOfNat 1210288437008223553644197666881536).rawCast)*x 5 +
  ((Int.negOfNat 3263489665734750297582766915584).rawCast)*x 6

def slopeTerminalForm16 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 438639841294219316818949422341685248).rawCast)*x 0 +
  (Nat.rawCast 979875119187197895023076387997089792)*x 1 +
  (Nat.rawCast 1007865063910372024375557752126177280)*x 2 +
  (Nat.rawCast 2027351994731580688662154345495658496)*x 3 +
  ((Int.negOfNat 310263503774236487196768321587380224).rawCast)*x 4 +
  (Nat.rawCast 9837932579715253806158428413886464)*x 5 +
  ((Int.negOfNat 12070112513710142644736262930432).rawCast)*x 6

def slopeTerminalForm17 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 54414853593689737217299697570414592).rawCast)*x 0 +
  ((Int.negOfNat 970351031578133869326348678089146368).rawCast)*x 1 +
  ((Int.negOfNat 1293217907031718272800569693550149632).rawCast)*x 2 +
  ((Int.negOfNat 1115816009696517367536049355866767360).rawCast)*x 3 +
  (Nat.rawCast 396869160167817402528566229294120960)*x 4 +
  ((Int.negOfNat 37984300424480030512217586822807552).rawCast)*x 5 +
  (Nat.rawCast 299093052667068185939230681202688)*x 6 +
  (Nat.rawCast 166213001843439619299751231488)*x 7

def slopeTerminalForm18 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 134025126535966014041680101595152384)*x 0 +
  ((Int.negOfNat 250134436167007691987089353143746560).rawCast)*x 1 +
  (Nat.rawCast 570576967300077687401009623773216768)*x 2 +
  ((Int.negOfNat 60893584659012878494438050383265792).rawCast)*x 3 +
  ((Int.negOfNat 405270442954402646509792139503730688).rawCast)*x 4 +
  (Nat.rawCast 79804058529549001955637699463348224)*x 5 +
  ((Int.negOfNat 1768844099951432984926244139171840).rawCast)*x 6 +
  (Nat.rawCast 2148217527608801556642744238080)*x 7

def slopeTerminalForm19 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 64323922241718032650590332211167232)*x 0 +
  ((Int.negOfNat 50495808725336543774245442813952000).rawCast)*x 1 +
  (Nat.rawCast 340140535375533599250490636546080768)*x 2 +
  (Nat.rawCast 365392638960886352243295626899488768)*x 3 +
  (Nat.rawCast 311676350290914713418662354104614912)*x 4 +
  ((Int.negOfNat 95323805880704026246882653244489728).rawCast)*x 5 +
  (Nat.rawCast 5983589357541736274033800837595136)*x 6 +
  ((Int.negOfNat 30913435595461829212240393273344).rawCast)*x 7 +
  ((Int.negOfNat 4717641026226225406543921152).rawCast)*x 8

def slopeTerminalForm20 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 1469386110204629941718266241089536).rawCast)*x 0 +
  ((Int.negOfNat 53830214345482205314363432737177600).rawCast)*x 1 +
  ((Int.negOfNat 172431301824030981110693860183375872).rawCast)*x 2 +
  ((Int.negOfNat 237643769561089161142349792695812096).rawCast)*x 3 +
  ((Int.negOfNat 99588691696285535863475164793536512).rawCast)*x 4 +
  (Nat.rawCast 72781475388588674431742762199023616)*x 5 +
  ((Int.negOfNat 12525120985906891915906423222960128).rawCast)*x 6 +
  (Nat.rawCast 166428963253181351825903739469824)*x 7 +
  ((Int.negOfNat 121382369642796171627218337792).rawCast)*x 8

def slopeTerminalForm21 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 7725767041418665994191631781199872).rawCast)*x 0 +
  (Nat.rawCast 4544941781595885955468204047335424)*x 1 +
  ((Int.negOfNat 39057938318123467301929111523426304).rawCast)*x 2 +
  (Nat.rawCast 26909203653341260531393993566584832)*x 3 +
  ((Int.negOfNat 45481258803554656963422991461384192).rawCast)*x 4 +
  ((Int.negOfNat 45165057216846646736312355426140160).rawCast)*x 5 +
  (Nat.rawCast 16043064919086393131698216545288192)*x 6 +
  ((Int.negOfNat 539158952625704421372844063064064).rawCast)*x 7 +
  (Nat.rawCast 1528664749085803389552980656128)*x 8 +
  (Nat.rawCast 57138358927437169220911104)*x 9

def slopeTerminalForm22 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 2191728377994939060580612527095808).rawCast)*x 0 +
  (Nat.rawCast 12848011642674518570692230858670080)*x 1 +
  (Nat.rawCast 7687823324913306650816452711415808)*x 2 +
  (Nat.rawCast 59156626235013668285734363657666560)*x 3 +
  (Nat.rawCast 56030129944722341038182195114541056)*x 4 +
  (Nat.rawCast 23211768040337614525861441094811648)*x 5 +
  ((Int.negOfNat 12233993707153354952658196975583232).rawCast)*x 6 +
  (Nat.rawCast 1151714623736823987355476880785408)*x 7 +
  ((Int.negOfNat 8031556742875716151109738299392).rawCast)*x 8 +
  (Nat.rawCast 2441474461670284043168514048)*x 9

def slopeTerminalForm23 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 260941345461925785202495894585344).rawCast)*x 0 +
  (Nat.rawCast 2659264531613155960285558248308736)*x 1 +
  ((Int.negOfNat 5996039460442971571361466808270848).rawCast)*x 2 +
  ((Int.negOfNat 16651566768485604877036589345144832).rawCast)*x 3 +
  ((Int.negOfNat 21303521104475948836643810876325888).rawCast)*x 4 +
  ((Int.negOfNat 3296821366543655126367418649149440).rawCast)*x 5 +
  (Nat.rawCast 5516261678667665376714531979395072)*x 6 +
  ((Int.negOfNat 1616119156586205391927376779149312).rawCast)*x 7 +
  (Nat.rawCast 25976899179781843108116899561472)*x 8 +
  ((Int.negOfNat 29605070998077873507155312640).rawCast)*x 9

def slopeTerminalForm24 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 11871721621789613617388502122496).rawCast)*x 0 +
  ((Int.negOfNat 186754230882629623295310122975232).rawCast)*x 1 +
  ((Int.negOfNat 1194872435622790537517945428377600).rawCast)*x 2 +
  ((Int.negOfNat 5224834169163104714275129512689664).rawCast)*x 3 +
  ((Int.negOfNat 2698002297370840567812889937707008).rawCast)*x 4 +
  ((Int.negOfNat 5905022463319590010032473700827136).rawCast)*x 5 +
  ((Int.negOfNat 1884737564376156573523595029905408).rawCast)*x 6 +
  (Nat.rawCast 1411566462412734680798217935781888)*x 7 +
  ((Int.negOfNat 57285127480731937618587360952320).rawCast)*x 8 +
  (Nat.rawCast 156866300672590163741107027968)*x 9

def slopeTerminalForm25 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 104219970303532257529594021675008).rawCast)*x 1 +
  (Nat.rawCast 1204337908540694542186763652169728)*x 2 +
  (Nat.rawCast 1774695891681606095711936748453888)*x 3 +
  (Nat.rawCast 5561802017478845713620279685545984)*x 4 +
  (Nat.rawCast 4479816152612742592657139838222336)*x 5 +
  (Nat.rawCast 807076289820122884066746801586176)*x 6 +
  ((Int.negOfNat 667493284966771552916966895255552).rawCast)*x 7 +
  (Nat.rawCast 87382242024127973383197752819712)*x 8 +
  ((Int.negOfNat 519040973585337511676315959296).rawCast)*x 9

def slopeTerminalForm26 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 8320351190529349756453228904448).rawCast)*x 1 +
  (Nat.rawCast 429325417533007926134358826549248)*x 2 +
  ((Int.negOfNat 104216817117166259321286911066112).rawCast)*x 3 +
  ((Int.negOfNat 822630654385316750066890196385792).rawCast)*x 4 +
  ((Int.negOfNat 1052656398641826838373436550545408).rawCast)*x 5 +
  ((Int.negOfNat 71620440815148525403626660691968).rawCast)*x 6 +
  (Nat.rawCast 96177055429131564762505968353280)*x 7 +
  ((Int.negOfNat 88315529924825631599224021843968).rawCast)*x 8 +
  (Nat.rawCast 1192451162612540550272249757696)*x 9

def slopeTerminalForm27 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 48252978874142568931698898108416)*x 2 +
  ((Int.negOfNat 155018103363487243886088872263680).rawCast)*x 3 +
  ((Int.negOfNat 437884334125340653969119620628480).rawCast)*x 4 +
  ((Int.negOfNat 382425911115776238354326202875904).rawCast)*x 5 +
  ((Int.negOfNat 320453666900766006408709517869056).rawCast)*x 6 +
  (Nat.rawCast 15141677359297399356550136463360)*x 7 +
  (Nat.rawCast 51790120027038285669492578058240)*x 8 +
  ((Int.negOfNat 1957675047831482449277642342400).rawCast)*x 9

def slopeTerminalForm28 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 1653882063716736924077619412992)*x 2 +
  (Nat.rawCast 26425122840615367997178783989760)*x 3 +
  (Nat.rawCast 118109514121143015060406901145600)*x 4 +
  (Nat.rawCast 306345030362284058673252025761792)*x 5 +
  (Nat.rawCast 224708673835629895432328731164672)*x 6 +
  (Nat.rawCast 29747594719173165762951549812736)*x 7 +
  ((Int.negOfNat 9290713662159305831540525629440).rawCast)*x 8 +
  (Nat.rawCast 2241620056816066875693081821184)*x 9

def slopeTerminalForm29 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 12765823822786524868129188741120)*x 3 +
  (Nat.rawCast 5062737930013550621803004559360)*x 4 +
  ((Int.negOfNat 24189237852706881642083074965504).rawCast)*x 5 +
  ((Int.negOfNat 43020082651271091033375246385152).rawCast)*x 6 +
  ((Int.negOfNat 17305113830059554718088108703744).rawCast)*x 7 +
  ((Int.negOfNat 6615805084875801803167786598400).rawCast)*x 8 +
  ((Int.negOfNat 1618562882674405705904038084608).rawCast)*x 9

def slopeTerminalForm30 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 1019375458091169223416131616768)*x 3 +
  ((Int.negOfNat 10742745752611324407147902533632).rawCast)*x 4 +
  ((Int.negOfNat 21126238874669944995186191892480).rawCast)*x 5 +
  ((Int.negOfNat 19334112949283487816917673050112).rawCast)*x 6 +
  ((Int.negOfNat 9585193106640775418285956005888).rawCast)*x 7 +
  (Nat.rawCast 1703989788696192134489145606144)*x 8 +
  (Nat.rawCast 493489397766383210618463191040)*x 9

def slopeTerminalForm31 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 1320481067540645675052828721152).rawCast)*x 4 +
  (Nat.rawCast 3637870601990124518630580289536)*x 5 +
  (Nat.rawCast 12162212277054309745355976081408)*x 6 +
  (Nat.rawCast 9785222807308042859719019200512)*x 7 +
  (Nat.rawCast 2498739402746942548257036828672)*x 8 +
  (Nat.rawCast 207157547302251363223581229056)*x 9

def slopeTerminalForm32 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 20724061466426599763620134912).rawCast)*x 4 +
  ((Int.negOfNat 46863687557319424293539414016).rawCast)*x 5 +
  ((Int.negOfNat 970679047395872004415464407040).rawCast)*x 6 +
  ((Int.negOfNat 1877704730850026003524315250688).rawCast)*x 7 +
  ((Int.negOfNat 1110572684514070610122308059136).rawCast)*x 8 +
  ((Int.negOfNat 187262359788088041518300921856).rawCast)*x 9

def slopeTerminalForm33 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 312950812753258274617949159424).rawCast)*x 5 +
  ((Int.negOfNat 772733045509961632577847558144).rawCast)*x 6 +
  ((Int.negOfNat 739982270891543217449012822016).rawCast)*x 7 +
  ((Int.negOfNat 407719894807828382402010415104).rawCast)*x 8 +
  ((Int.negOfNat 37741348585486266370803892224).rawCast)*x 9

def slopeTerminalForm34 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 24799058952111668177236131840).rawCast)*x 5 +
  (Nat.rawCast 105765408693268384045414219776)*x 6 +
  (Nat.rawCast 386503730990799623334383321088)*x 7 +
  (Nat.rawCast 364766670772953074535713734656)*x 8 +
  (Nat.rawCast 74088049820451168951554015232)*x 9

def slopeTerminalForm35 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 12203063558667225414890422272)*x 6 +
  ((Int.negOfNat 32386100537571609416130625536).rawCast)*x 7 +
  ((Int.negOfNat 40155681659450268210809536512).rawCast)*x 8 +
  ((Int.negOfNat 9387850670010248739378167808).rawCast)*x 9

def slopeTerminalForm36 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 1155811476564567674767540224).rawCast)*x 6 +
  ((Int.negOfNat 16756566733722812797144793088).rawCast)*x 7 +
  ((Int.negOfNat 31428247798190619611218575360).rawCast)*x 8 +
  ((Int.negOfNat 13925101421023528964692377600).rawCast)*x 9

def slopeTerminalForm37 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 3607769141811159463939276800)*x 7 +
  (Nat.rawCast 9397829924667977237142700032)*x 8 +
  (Nat.rawCast 4828461550150972394566582272)*x 9

def slopeTerminalForm38 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 222751525790116780261244928)*x 7 +
  (Nat.rawCast 369423759347673207435952128)*x 8 +
  (Nat.rawCast 661712576478041952743325696)*x 9

def slopeTerminalForm39 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 376848028872791602250121216).rawCast)*x 8 +
  ((Int.negOfNat 503453381600997417953525760).rawCast)*x 9

def slopeTerminalForm40 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 23452266002932235520442368)*x 8 +
  (Nat.rawCast 29125230075179002239123456)*x 9

def slopeTerminalForm41 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 14913489313416408968724480)*x 9

def slopeTerminalForm42 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 1851372572417958975897600).rawCast)*x 9

def slopeTerminalClockForm (A : ℕ) (x : ℕ → ℝ) : ℝ :=
  (4/5)^(4-4)*slopeTerminalForm4 x*degreeElevationCoefficient 38 (4-4) A +
  (4/5)^(5-4)*slopeTerminalForm5 x*degreeElevationCoefficient 38 (5-4) A +
  (4/5)^(6-4)*slopeTerminalForm6 x*degreeElevationCoefficient 38 (6-4) A +
  (4/5)^(7-4)*slopeTerminalForm7 x*degreeElevationCoefficient 38 (7-4) A +
  (4/5)^(8-4)*slopeTerminalForm8 x*degreeElevationCoefficient 38 (8-4) A +
  (4/5)^(9-4)*slopeTerminalForm9 x*degreeElevationCoefficient 38 (9-4) A +
  (4/5)^(10-4)*slopeTerminalForm10 x*degreeElevationCoefficient 38 (10-4) A +
  (4/5)^(11-4)*slopeTerminalForm11 x*degreeElevationCoefficient 38 (11-4) A +
  (4/5)^(12-4)*slopeTerminalForm12 x*degreeElevationCoefficient 38 (12-4) A +
  (4/5)^(13-4)*slopeTerminalForm13 x*degreeElevationCoefficient 38 (13-4) A +
  (4/5)^(14-4)*slopeTerminalForm14 x*degreeElevationCoefficient 38 (14-4) A +
  (4/5)^(15-4)*slopeTerminalForm15 x*degreeElevationCoefficient 38 (15-4) A +
  (4/5)^(16-4)*slopeTerminalForm16 x*degreeElevationCoefficient 38 (16-4) A +
  (4/5)^(17-4)*slopeTerminalForm17 x*degreeElevationCoefficient 38 (17-4) A +
  (4/5)^(18-4)*slopeTerminalForm18 x*degreeElevationCoefficient 38 (18-4) A +
  (4/5)^(19-4)*slopeTerminalForm19 x*degreeElevationCoefficient 38 (19-4) A +
  (4/5)^(20-4)*slopeTerminalForm20 x*degreeElevationCoefficient 38 (20-4) A +
  (4/5)^(21-4)*slopeTerminalForm21 x*degreeElevationCoefficient 38 (21-4) A +
  (4/5)^(22-4)*slopeTerminalForm22 x*degreeElevationCoefficient 38 (22-4) A +
  (4/5)^(23-4)*slopeTerminalForm23 x*degreeElevationCoefficient 38 (23-4) A +
  (4/5)^(24-4)*slopeTerminalForm24 x*degreeElevationCoefficient 38 (24-4) A +
  (4/5)^(25-4)*slopeTerminalForm25 x*degreeElevationCoefficient 38 (25-4) A +
  (4/5)^(26-4)*slopeTerminalForm26 x*degreeElevationCoefficient 38 (26-4) A +
  (4/5)^(27-4)*slopeTerminalForm27 x*degreeElevationCoefficient 38 (27-4) A +
  (4/5)^(28-4)*slopeTerminalForm28 x*degreeElevationCoefficient 38 (28-4) A +
  (4/5)^(29-4)*slopeTerminalForm29 x*degreeElevationCoefficient 38 (29-4) A +
  (4/5)^(30-4)*slopeTerminalForm30 x*degreeElevationCoefficient 38 (30-4) A +
  (4/5)^(31-4)*slopeTerminalForm31 x*degreeElevationCoefficient 38 (31-4) A +
  (4/5)^(32-4)*slopeTerminalForm32 x*degreeElevationCoefficient 38 (32-4) A +
  (4/5)^(33-4)*slopeTerminalForm33 x*degreeElevationCoefficient 38 (33-4) A +
  (4/5)^(34-4)*slopeTerminalForm34 x*degreeElevationCoefficient 38 (34-4) A +
  (4/5)^(35-4)*slopeTerminalForm35 x*degreeElevationCoefficient 38 (35-4) A +
  (4/5)^(36-4)*slopeTerminalForm36 x*degreeElevationCoefficient 38 (36-4) A +
  (4/5)^(37-4)*slopeTerminalForm37 x*degreeElevationCoefficient 38 (37-4) A +
  (4/5)^(38-4)*slopeTerminalForm38 x*degreeElevationCoefficient 38 (38-4) A +
  (4/5)^(39-4)*slopeTerminalForm39 x*degreeElevationCoefficient 38 (39-4) A +
  (4/5)^(40-4)*slopeTerminalForm40 x*degreeElevationCoefficient 38 (40-4) A +
  (4/5)^(41-4)*slopeTerminalForm41 x*degreeElevationCoefficient 38 (41-4) A +
  (4/5)^(42-4)*slopeTerminalForm42 x*degreeElevationCoefficient 38 (42-4) A

def slopeTerminalTensorCoefficient (A B : ℕ) : ℝ :=
  slopeTerminalClockForm A (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)

end
end HTGeometry.ThetaRatioKineticContraction

