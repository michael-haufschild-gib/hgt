import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticThirdInitialSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondControlPositive
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def thirdInitialRow5 (r : ℝ) : ℝ :=
  (Nat.rawCast 615974148349919265846014022600622080)*r^0

def thirdInitialRow6 (r : ℝ) : ℝ :=
  (Nat.rawCast 684415720388799184273348914000691200)*r^0

def thirdInitialRow7 (r : ℝ) : ℝ :=
  ((Int.negOfNat 11189056335489551997562132495721299968).rawCast)*r^0 +
  ((Int.negOfNat 691259877592687176116082403140698112).rawCast)*r^1

def thirdInitialRow8 (r : ℝ) : ℝ :=
  ((Int.negOfNat 45919922182097052381064410178051375104).rawCast)*r^0 +
  ((Int.negOfNat 548673269178354012725801379390554112).rawCast)*r^1

def thirdInitialRow9 (r : ℝ) : ℝ :=
  ((Int.negOfNat 210302794847339897571061758822054887424).rawCast)*r^0 +
  (Nat.rawCast 6917383348786997162865697905759485952)*r^1 +
  (Nat.rawCast 315655065116352660820884346355318784)*r^2

def thirdInitialRow10 (r : ℝ) : ℝ :=
  ((Int.negOfNat 627633043403090536098409729989713854464).rawCast)*r^0 +
  (Nat.rawCast 22699999298981712697900724582539591680)*r^1 +
  (Nat.rawCast 148490750199785921785478586140983296)*r^2

def thirdInitialRow11 (r : ℝ) : ℝ :=
  ((Int.negOfNat 1401062160466191720809197353766376964096).rawCast)*r^0 +
  (Nat.rawCast 120654269890290985779494940605958586368)*r^1 +
  ((Int.negOfNat 1748148786058202373244242831442182144).rawCast)*r^2 +
  ((Int.negOfNat 78228998492999577544001095005634560).rawCast)*r^3

def thirdInitialRow12 (r : ℝ) : ℝ :=
  ((Int.negOfNat 2538030210377463627518705806676129218560).rawCast)*r^0 +
  (Nat.rawCast 336954521536812577560461901288840364032)*r^1 +
  ((Int.negOfNat 4221496876556784257325043578593869824).rawCast)*r^2 +
  ((Int.negOfNat 41522041856886656958792000344162304).rawCast)*r^3

def thirdInitialRow13 (r : ℝ) : ℝ :=
  ((Int.negOfNat 3390731624274751834148800599282853871616).rawCast)*r^0 +
  (Nat.rawCast 690938917508700184351559201690883194880)*r^1 +
  ((Int.negOfNat 30698370502282760164402960656664363008).rawCast)*r^2 +
  (Nat.rawCast 357934072676791472970301602319564800)*r^3 +
  (Nat.rawCast 11638216278702138620891902079139840)*r^4

def thirdInitialRow14 (r : ℝ) : ℝ :=
  ((Int.negOfNat 3054027227064584434189250447806411309056).rawCast)*r^0 +
  (Nat.rawCast 1165196843256388240688163507019796447232)*r^1 +
  ((Int.negOfNat 76422874567326737053431448006519947264).rawCast)*r^2 +
  (Nat.rawCast 57971182950349985252311690452664320)*r^3 +
  (Nat.rawCast 15147504488364571852583257830850560)*r^4

def thirdInitialRow15 (r : ℝ) : ℝ :=
  ((Int.negOfNat 1697820099178996557425376889132340477952).rawCast)*r^0 +
  (Nat.rawCast 1376943072404156148413330398992182280192)*r^1 +
  ((Int.negOfNat 142455576978428939125959008138689511424).rawCast)*r^2 +
  (Nat.rawCast 4988689926373554252930071501897465856)*r^3 +
  ((Int.negOfNat 95710296520625573353842972473425920).rawCast)*r^4 +
  ((Int.negOfNat 1071192490282347450618343493468160).rawCast)*r^5

def thirdInitialRow16 (r : ℝ) : ℝ :=
  ((Int.negOfNat 413810243891780468390179014525686120448).rawCast)*r^0 +
  (Nat.rawCast 1004018637761319539279787604481245446144)*r^1 +
  ((Int.negOfNat 222876232269436227613205894838563635200).rawCast)*r^2 +
  (Nat.rawCast 9773058791568853821317678350479654912)*r^3 +
  (Nat.rawCast 165784838559275680225516591805104128)*r^4 +
  ((Int.negOfNat 3327568701860088700692768164413440).rawCast)*r^5

def thirdInitialRow17 (r : ℝ) : ℝ :=
  (Nat.rawCast 150655457972450415247099566058408771584)*r^0 +
  (Nat.rawCast 374093376568727679433540855582647386112)*r^1 +
  ((Int.negOfNat 220394527368994623873519307291826847744).rawCast)*r^2 +
  (Nat.rawCast 14175716407589439500286940765099130880)*r^3 +
  ((Int.negOfNat 663361604803011897701544718139129856).rawCast)*r^4 +
  (Nat.rawCast 19596791062525306048145000799141888)*r^5 +
  (Nat.rawCast 59795630479163612000771037462528)*r^6

def thirdInitialRow18 (r : ℝ) : ℝ :=
  (Nat.rawCast 184221963894081893836135322277227003904)*r^0 +
  ((Int.negOfNat 17546186946261683307708904316709371904).rawCast)*r^1 +
  ((Int.negOfNat 110728526691036604315752314887194279936).rawCast)*r^2 +
  (Nat.rawCast 20109217183148480156944152728149426176)*r^3 +
  ((Int.negOfNat 695582093782998503134253988811112448).rawCast)*r^4 +
  ((Int.negOfNat 42949549850939939802594835244777472).rawCast)*r^5 +
  (Nat.rawCast 376311166220212145879955001049088)*r^6

def thirdInitialRow19 (r : ℝ) : ℝ :=
  (Nat.rawCast 82980578817735772581291397672278687744)*r^0 +
  ((Int.negOfNat 96912524138830186722530750953401876480).rawCast)*r^1 +
  ((Int.negOfNat 7806947722983836154861516357422284800).rawCast)*r^2 +
  (Nat.rawCast 15091591161976282741596731802988314624)*r^3 +
  ((Int.negOfNat 232687677639146587173311748948099072).rawCast)*r^4 +
  (Nat.rawCast 81347652080806147013517103991881728)*r^5 +
  ((Int.negOfNat 2226502560274363681008200869478400).rawCast)*r^6 +
  ((Int.negOfNat 1855039055279324500142824882176).rawCast)*r^7

def thirdInitialRow20 (r : ℝ) : ℝ :=
  (Nat.rawCast 21723228299027799598142647766127476736)*r^0 +
  ((Int.negOfNat 53357738239807651702047220366105903104).rawCast)*r^1 +
  (Nat.rawCast 22887826307910673686693919183601664000)*r^2 +
  (Nat.rawCast 2420639211748090201574371430737379328)*r^3 +
  ((Int.negOfNat 491031100695819079803500839569457152).rawCast)*r^4 +
  (Nat.rawCast 1015787037624079843049851072806912)*r^5 +
  (Nat.rawCast 5207437963542948209629873494294528)*r^6 +
  ((Int.negOfNat 20858222533393045349062183747584).rawCast)*r^7

def thirdInitialRow21 (r : ℝ) : ℝ :=
  (Nat.rawCast 3391200156644855846549271014742687744)*r^0 +
  ((Int.negOfNat 15366368753981866452384304297685286912).rawCast)*r^1 +
  (Nat.rawCast 14162952195238126093125535598578237440)*r^2 +
  ((Int.negOfNat 3343136591411960481590176105749282816).rawCast)*r^3 +
  ((Int.negOfNat 202266736953696837105496382332993536).rawCast)*r^4 +
  ((Int.negOfNat 96474829913655219018772882101633024).rawCast)*r^5 +
  ((Int.negOfNat 7975221637983741292731969998684160).rawCast)*r^6 +
  (Nat.rawCast 126587833755849223301422576041984)*r^7 +
  (Nat.rawCast 24519808809295863487408373760)*r^8

def thirdInitialRow22 (r : ℝ) : ℝ :=
  (Nat.rawCast 279874966922035164987910705951801344)*r^0 +
  ((Int.negOfNat 2291572903474613292925770715398930432).rawCast)*r^1 +
  (Nat.rawCast 4027767163655420961238306556706029568)*r^2 +
  ((Int.negOfNat 2191932689777649392780779618931048448).rawCast)*r^3 +
  (Nat.rawCast 278139854758985221110366518378496000)*r^4 +
  ((Int.negOfNat 36397700318843068491190549610496000).rawCast)*r^5 +
  (Nat.rawCast 5458847855250653430215594628612096)*r^6 +
  ((Int.negOfNat 313746029139153144666118686769152).rawCast)*r^7 +
  (Nat.rawCast 450193129989277456291558588416)*r^8

def thirdInitialRow23 (r : ℝ) : ℝ :=
  (Nat.rawCast 6996971793854297435264516112777216)*r^0 +
  ((Int.negOfNat 42780793163387928675880013150552064).rawCast)*r^1 +
  (Nat.rawCast 450665995859381896705189171100123136)*r^2 +
  ((Int.negOfNat 520986394801279041497842923205558272).rawCast)*r^3 +
  (Nat.rawCast 208311996086797120483950438018711552)*r^4 +
  ((Int.negOfNat 8108742513558627459779082445651968).rawCast)*r^5 +
  (Nat.rawCast 8842583990449969401768843688280064)*r^6 +
  (Nat.rawCast 479039411845546872909868679823360)*r^7 +
  ((Int.negOfNat 2830131442302067997682060754944).rawCast)*r^8

def thirdInitialRow24 (r : ℝ) : ℝ :=
  ((Int.negOfNat 280270250985642952118377711140864).rawCast)*r^0 +
  (Nat.rawCast 44236125233136526102155693964394496)*r^1 +
  ((Int.negOfNat 86139295050152219820597886435983360).rawCast)*r^2 +
  ((Int.negOfNat 19899274108784745436062528112164864).rawCast)*r^3 +
  (Nat.rawCast 28939109796304986066791495022673920)*r^4 +
  ((Int.negOfNat 6574987268341909227659011037331456).rawCast)*r^5 +
  (Nat.rawCast 533356744902531215489532740763648)*r^6 +
  ((Int.negOfNat 501464831674585909853933575077888).rawCast)*r^7 +
  (Nat.rawCast 7501275624332432401873552539648)*r^8

def thirdInitialRow25 (r : ℝ) : ℝ :=
  (Nat.rawCast 6776090823741174125747290905772032)*r^1 +
  ((Int.negOfNat 44427353136421116010173260755894272).rawCast)*r^2 +
  (Nat.rawCast 21414031069671444257551824929685504)*r^3 +
  ((Int.negOfNat 7435971490121335837021290614489088).rawCast)*r^4 +
  (Nat.rawCast 1112238091307167538893818660126720)*r^5 +
  ((Int.negOfNat 1065502151759265434707079083327488).rawCast)*r^6 +
  ((Int.negOfNat 193079308542538179865221670109184).rawCast)*r^7 +
  ((Int.negOfNat 12308880596750867169237553643520).rawCast)*r^8

def thirdInitialRow26 (r : ℝ) : ℝ :=
  (Nat.rawCast 322402438831105707623866957824000)*r^1 +
  ((Int.negOfNat 8381478004691044210456036173152256).rawCast)*r^2 +
  (Nat.rawCast 7342684249960854131280622255079424)*r^3 +
  ((Int.negOfNat 1306074768982181708229073818353664).rawCast)*r^4 +
  (Nat.rawCast 1362447817850186751173952194740224)*r^5 +
  ((Int.negOfNat 341408045233400655144717568180224).rawCast)*r^6 +
  (Nat.rawCast 135488413072225444097219786440704)*r^7 +
  (Nat.rawCast 15378573393707579442680555372544)*r^8

def thirdInitialRow27 (r : ℝ) : ℝ :=
  ((Int.negOfNat 862204950065927469316743647723520).rawCast)*r^2 +
  (Nat.rawCast 1272446158030366316374313467379712)*r^3 +
  (Nat.rawCast 82645821037493517397827073867776)*r^4 +
  ((Int.negOfNat 193101327916041365894676558643200).rawCast)*r^5 +
  ((Int.negOfNat 38976248525114026234278976684032).rawCast)*r^6 +
  (Nat.rawCast 33848349343706352146148206051328)*r^7 +
  ((Int.negOfNat 3819560422084104591322487193600).rawCast)*r^8

def thirdInitialRow28 (r : ℝ) : ℝ :=
  ((Int.negOfNat 42712459506334977655632373481472).rawCast)*r^2 +
  (Nat.rawCast 137677799999460391954936649220096)*r^3 +
  ((Int.negOfNat 57455916725041863685775560802304).rawCast)*r^4 +
  ((Int.negOfNat 108307901720763868902159103819776).rawCast)*r^5 +
  (Nat.rawCast 55571164052220531633693061545984)*r^6 +
  ((Int.negOfNat 9829893097489785233244602499072).rawCast)*r^7 +
  ((Int.negOfNat 2693968725824089698364400074752).rawCast)*r^8

def thirdInitialRow29 (r : ℝ) : ℝ :=
  (Nat.rawCast 16991470422970658184887858626560)*r^3 +
  ((Int.negOfNat 31486370119149283889831542259712).rawCast)*r^4 +
  (Nat.rawCast 22586799691445213912027533148160)*r^5 +
  (Nat.rawCast 12213608072824909993204682588160)*r^6 +
  ((Int.negOfNat 5257620033635657481763845832704).rawCast)*r^7 +
  (Nat.rawCast 1255184855677360744795195047936)*r^8

def thirdInitialRow30 (r : ℝ) : ℝ :=
  (Nat.rawCast 1837216644362987324490563715072)*r^3 +
  ((Int.negOfNat 5514811211383417203605360345088).rawCast)*r^4 +
  (Nat.rawCast 4716182210481847590477927284736)*r^5 +
  ((Int.negOfNat 5512270055270522514518650650624).rawCast)*r^6 +
  (Nat.rawCast 442869101684987842633616326656)*r^7 +
  (Nat.rawCast 46506039816854625941264007168)*r^8

def thirdInitialRow31 (r : ℝ) : ℝ :=
  ((Int.negOfNat 19789445284385380474332119040).rawCast)*r^4 +
  ((Int.negOfNat 934554928676556505338316062720).rawCast)*r^5 +
  ((Int.negOfNat 435156718169363387949376339968).rawCast)*r^6 +
  (Nat.rawCast 490230400586942981834400595968)*r^7 +
  ((Int.negOfNat 94550998673361459303206092800).rawCast)*r^8

def thirdInitialRow32 (r : ℝ) : ℝ :=
  (Nat.rawCast 73991044703600860137944776704)*r^4 +
  (Nat.rawCast 26044890032366785945921388544)*r^5 +
  (Nat.rawCast 254277208876134360512288784384)*r^6 +
  ((Int.negOfNat 68035791217059060452991959040).rawCast)*r^7 +
  (Nat.rawCast 11100175659406054852292247552)*r^8

def thirdInitialRow33 (r : ℝ) : ℝ :=
  (Nat.rawCast 29667845179089607600751247360)*r^5 +
  ((Int.negOfNat 14458243979033715484963897344).rawCast)*r^6 +
  ((Int.negOfNat 13017848396939942439879180288).rawCast)*r^7 +
  (Nat.rawCast 1807503322456513621839052800)*r^8

def thirdInitialRow34 (r : ℝ) : ℝ :=
  ((Int.negOfNat 3602833776883342762139713536).rawCast)*r^5 +
  ((Int.negOfNat 2318040679633098869072461824).rawCast)*r^6 +
  (Nat.rawCast 3627380369162142140646555648)*r^7 +
  ((Int.negOfNat 542359470848769954165030912).rawCast)*r^8

def thirdInitialRow35 (r : ℝ) : ℝ :=
  (Nat.rawCast 149289327178168807609860096)*r^6 +
  ((Int.negOfNat 296650870424058112235274240).rawCast)*r^7 +
  (Nat.rawCast 50041392783306775993516032)*r^8

def thirdInitialRow36 (r : ℝ) : ℝ :=
  (Nat.rawCast 11195676924810034063343616)*r^6 +
  (Nat.rawCast 12490143134096873339486208)*r^7 +
  ((Int.negOfNat 1701297352217756971302912).rawCast)*r^8

def thirdInitialRow37 (r : ℝ) : ℝ :=
  ((Int.negOfNat 552613955248796517531648).rawCast)*r^7 +
  ((Int.negOfNat 54936918781139204702208).rawCast)*r^8

def thirdInitialRow38 (r : ℝ) : ℝ :=
  (Nat.rawCast 1483018268683385438208)*r^7 +
  (Nat.rawCast 7233585216659726008320)*r^8

def thirdInitialRow39 (r : ℝ) : ℝ :=
  ((Int.negOfNat 70119067077228625920).rawCast)*r^8

def thirdInitialQuotient (h r : ℝ) : ℝ :=
  h^(5-5)*thirdInitialRow5 r +
  h^(6-5)*thirdInitialRow6 r +
  h^(7-5)*thirdInitialRow7 r +
  h^(8-5)*thirdInitialRow8 r +
  h^(9-5)*thirdInitialRow9 r +
  h^(10-5)*thirdInitialRow10 r +
  h^(11-5)*thirdInitialRow11 r +
  h^(12-5)*thirdInitialRow12 r +
  h^(13-5)*thirdInitialRow13 r +
  h^(14-5)*thirdInitialRow14 r +
  h^(15-5)*thirdInitialRow15 r +
  h^(16-5)*thirdInitialRow16 r +
  h^(17-5)*thirdInitialRow17 r +
  h^(18-5)*thirdInitialRow18 r +
  h^(19-5)*thirdInitialRow19 r +
  h^(20-5)*thirdInitialRow20 r +
  h^(21-5)*thirdInitialRow21 r +
  h^(22-5)*thirdInitialRow22 r +
  h^(23-5)*thirdInitialRow23 r +
  h^(24-5)*thirdInitialRow24 r +
  h^(25-5)*thirdInitialRow25 r +
  h^(26-5)*thirdInitialRow26 r +
  h^(27-5)*thirdInitialRow27 r +
  h^(28-5)*thirdInitialRow28 r +
  h^(29-5)*thirdInitialRow29 r +
  h^(30-5)*thirdInitialRow30 r +
  h^(31-5)*thirdInitialRow31 r +
  h^(32-5)*thirdInitialRow32 r +
  h^(33-5)*thirdInitialRow33 r +
  h^(34-5)*thirdInitialRow34 r +
  h^(35-5)*thirdInitialRow35 r +
  h^(36-5)*thirdInitialRow36 r +
  h^(37-5)*thirdInitialRow37 r +
  h^(38-5)*thirdInitialRow38 r +
  h^(39-5)*thirdInitialRow39 r

theorem thirdInitial_factor (h r : ℝ) :
    kineticThirdControl h (9-r*h^2) (1/3) 0=h^5*thirdInitialQuotient h r := by
  rw [(kineticThirdInitialNorm h r).property]
  dsimp only [kineticThirdInitialNorm,thirdInitialQuotient,
    thirdInitialRow5,thirdInitialRow6,thirdInitialRow7,thirdInitialRow8,thirdInitialRow9,thirdInitialRow10,thirdInitialRow11,thirdInitialRow12,thirdInitialRow13,thirdInitialRow14,thirdInitialRow15,thirdInitialRow16,thirdInitialRow17,thirdInitialRow18,thirdInitialRow19,thirdInitialRow20,thirdInitialRow21,thirdInitialRow22,thirdInitialRow23,thirdInitialRow24,thirdInitialRow25,thirdInitialRow26,thirdInitialRow27,thirdInitialRow28,thirdInitialRow29,thirdInitialRow30,thirdInitialRow31,thirdInitialRow32,thirdInitialRow33,thirdInitialRow34,thirdInitialRow35,thirdInitialRow36,thirdInitialRow37,thirdInitialRow38,thirdInitialRow39]
  norm_num [Nat.rawCast,Int.rawCast]
  ring_nf (config := {mode := .raw})

end
end HTGeometry.ThetaRatioKineticContraction

