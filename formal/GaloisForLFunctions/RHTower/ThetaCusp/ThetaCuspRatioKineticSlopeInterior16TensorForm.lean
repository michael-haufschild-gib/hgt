import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior16Defect
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior16Form4 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 5584832278372601343670527138245640192)*x 0

def slopeInterior16Form5 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 26743544274192328125481108814577008640)*x 0 +
  (Nat.rawCast 523578026097431375969111919210528768)*x 1

def slopeInterior16Form6 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 99820892125839046360960816858810810368)*x 0 +
  ((Int.negOfNat 9046264784238953218132989270804135936).rawCast)*x 1

def slopeInterior16Form7 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 450386323785836362536593205785247350784)*x 0 +
  ((Int.negOfNat 12433267080513023181305724708965056512).rawCast)*x 1 +
  ((Int.negOfNat 501762275010038401970398922576756736).rawCast)*x 2

def slopeInterior16Form8 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 238159053327684700740715422905750519808)*x 0 +
  ((Int.negOfNat 77163642404454149476306178383206678528).rawCast)*x 1 +
  (Nat.rawCast 5602338745294583359842333863939407872)*x 2

def slopeInterior16Form9 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 4003367081761682282028473934186257842176)*x 0 +
  ((Int.negOfNat 364938914328595396914846164825854181376).rawCast)*x 1 +
  ((Int.negOfNat 2832031451890749569063863313554735104).rawCast)*x 2 +
  (Nat.rawCast 201189704472624093543686524511453184)*x 3

def slopeInterior16Form10 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 4655073444742204432274400780618741841920)*x 0 +
  (Nat.rawCast 213907768499749134117036086915216965632)*x 1 +
  (Nat.rawCast 29418235144395921301311355096783650816)*x 2 +
  ((Int.negOfNat 1733626516024052434791416030507827200).rawCast)*x 3

def slopeInterior16Form11 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 3610173707903530135874849105756018442240)*x 0 +
  ((Int.negOfNat 2371932094086670122849887897321937567744).rawCast)*x 1 +
  (Nat.rawCast 120319967738732357226461157836275580928)*x 2 +
  (Nat.rawCast 2021370875992976087639912546190753792)*x 3 +
  ((Int.negOfNat 44506825520885048806016329552232448).rawCast)*x 4

def slopeInterior16Form12 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 2975988103145255686340451608117133705216)*x 0 +
  ((Int.negOfNat 728566379365738924804076821009498374144).rawCast)*x 1 +
  ((Int.negOfNat 216360611519860568548889933706858332160).rawCast)*x 2 +
  ((Int.negOfNat 801317461246588266165016315652210688).rawCast)*x 3 +
  (Nat.rawCast 261446946992761480973411682890022912)*x 4

def slopeInterior16Form13 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 1003413608804489282121416082427836628992)*x 0 +
  (Nat.rawCast 304724298570543348160691492900868980736)*x 1 +
  (Nat.rawCast 742382548488147093236312218649449463808)*x 2 +
  ((Int.negOfNat 47407764648832456125961447529854795776).rawCast)*x 3 +
  (Nat.rawCast 101964962360152071344855891444760576)*x 4 +
  (Nat.rawCast 5972647902869932867731781771591680)*x 5

def slopeInterior16Form14 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 395024777100762527083404131766575824896).rawCast)*x 0 +
  ((Int.negOfNat 85942156245914499445776640550375522304).rawCast)*x 1 +
  ((Int.negOfNat 420190388763497514520654089541537234944).rawCast)*x 2 +
  (Nat.rawCast 101987638133582059881110710481118560256)*x 3 +
  ((Int.negOfNat 3732871881689567457925080540298346496).rawCast)*x 4 +
  ((Int.negOfNat 10412181096573296067806142281023488).rawCast)*x 5

def slopeInterior16Form15 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 410807202403939835812503280868948705280).rawCast)*x 0 +
  (Nat.rawCast 444983206602786304137566838838731472896)*x 1 +
  ((Int.negOfNat 261655491298908742555335038462953783296).rawCast)*x 2 +
  ((Int.negOfNat 169108530416743010771874629392407724032).rawCast)*x 3 +
  (Nat.rawCast 19612822962544863491079671767992631296)*x 4 +
  ((Int.negOfNat 204779233983460443121753750883008512).rawCast)*x 5 +
  ((Int.negOfNat 499313918857416795530163338084352).rawCast)*x 6

def slopeInterior16Form16 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 146663329402488720968213436627897286656).rawCast)*x 0 +
  (Nat.rawCast 329879504743607076338254895128403509248)*x 1 +
  (Nat.rawCast 141306616290580839252833402382018674688)*x 2 +
  (Nat.rawCast 183483962106795086307889352314976206848)*x 3 +
  ((Int.negOfNat 38209615975563432191967888008540061696).rawCast)*x 4 +
  (Nat.rawCast 1429056844677502598115216710166380544)*x 5 +
  ((Int.negOfNat 2277548900659113514872712867086336).rawCast)*x 6

def slopeInterior16Form17 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 20795694288319620786663051934851661824).rawCast)*x 0 +
  ((Int.negOfNat 79894868379674305403225759453640916992).rawCast)*x 1 +
  ((Int.negOfNat 88805427245945834478113849799434305536).rawCast)*x 2 +
  ((Int.negOfNat 26199023476119557903613761410289369088).rawCast)*x 3 +
  (Nat.rawCast 39917628813852902267452886650774880256)*x 4 +
  ((Int.negOfNat 5151608779909240525543505435440447488).rawCast)*x 5 +
  (Nat.rawCast 45644241114525957237400411400306688)*x 6 +
  (Nat.rawCast 25430589282046261752861938417664)*x 7

def slopeInterior16Form18 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 17891921346173459467207458026623598592)*x 0 +
  ((Int.negOfNat 94992530944313329047647526583900569600).rawCast)*x 1 +
  (Nat.rawCast 11748014371956346088805773860650614784)*x 2 +
  ((Int.negOfNat 65820330702432557117891662718793940992).rawCast)*x 3 +
  ((Int.negOfNat 34963335669286736752704507524312727552).rawCast)*x 4 +
  (Nat.rawCast 9811457781479482770225901394492129280)*x 5 +
  ((Int.negOfNat 249737000978886043206842038987259904).rawCast)*x 6 +
  (Nat.rawCast 349745148622859163148219393769472)*x 7

def slopeInterior16Form19 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 13195474171125353876993569869149503488)*x 0 +
  ((Int.negOfNat 24971104153646581545761203803226374144).rawCast)*x 1 +
  (Nat.rawCast 65751955093010603493429567269866831872)*x 2 +
  (Nat.rawCast 34112020645908981824476586048923631616)*x 3 +
  (Nat.rawCast 19419751796095007668114290309209260032)*x 4 +
  ((Int.negOfNat 9866080854392839470353780440156864512).rawCast)*x 5 +
  (Nat.rawCast 796439600107408939442901650730123264)*x 6 +
  ((Int.negOfNat 4604989077045341786316072133066752).rawCast)*x 7 +
  ((Int.negOfNat 721799077012612487201219936256).rawCast)*x 8

def slopeInterior16Form20 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 2495352288405163624656034713179258880)*x 0 +
  ((Int.negOfNat 7098758100106681923646167425004601344).rawCast)*x 1 +
  ((Int.negOfNat 1857507630871712527643408429488275456).rawCast)*x 2 +
  ((Int.negOfNat 8684920151234323211778176627836452864).rawCast)*x 3 +
  (Nat.rawCast 3766404711414463215799525436804825088)*x 4 +
  (Nat.rawCast 5829664183051187291180226986133946368)*x 5 +
  ((Int.negOfNat 1547916493834091982018801732478304256).rawCast)*x 6 +
  (Nat.rawCast 23299935404071826682883706770685952)*x 7 +
  ((Int.negOfNat 19154060420207212576702023598080).rawCast)*x 8

def slopeInterior16Form21 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 526689514487225531081779586613116928).rawCast)*x 0 +
  ((Int.negOfNat 582755024666259901928213223510638592).rawCast)*x 1 +
  ((Int.negOfNat 11665582010365785903462378336864436224).rawCast)*x 2 +
  ((Int.negOfNat 6312609518855605655889756528335388672).rawCast)*x 3 +
  ((Int.negOfNat 9695911039374209306568494287442411520).rawCast)*x 4 +
  ((Int.negOfNat 2788798988545128690386740834348302336).rawCast)*x 5 +
  (Nat.rawCast 1753124668108145306810414241706672128)*x 6 +
  ((Int.negOfNat 71449753906461581051768077295812608).rawCast)*x 7 +
  (Nat.rawCast 225829997317315143085335697686528)*x 8 +
  (Nat.rawCast 8742168915897886890799398912)*x 9

def slopeInterior16Form22 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 301610169819732851932051214790819840).rawCast)*x 0 +
  (Nat.rawCast 1533122886762747270715211990849028096)*x 1 +
  ((Int.negOfNat 1606958694090554534929104702994907136).rawCast)*x 2 +
  (Nat.rawCast 6783818584942080970258087831796711424)*x 3 +
  (Nat.rawCast 3694966850600342734406584081909284864)*x 4 +
  (Nat.rawCast 785217269760791858526655694581530624)*x 5 +
  ((Int.negOfNat 1069232610654417335656721736888483840).rawCast)*x 6 +
  (Nat.rawCast 143579380712144456618224489026551808)*x 7 +
  ((Int.negOfNat 1122564568895001658670610439471104).rawCast)*x 8 +
  (Nat.rawCast 380499910581533420157206003712)*x 9

def slopeInterior16Form23 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 47783430065400537451876218065387520).rawCast)*x 0 +
  (Nat.rawCast 665593677969909521021796893098770432)*x 1 +
  ((Int.negOfNat 322757055034338210126954389733113856).rawCast)*x 2 +
  (Nat.rawCast 714672539430450384091864534439952384)*x 3 +
  (Nat.rawCast 66940116095217841251935492014866432)*x 4 +
  (Nat.rawCast 724969391528801939519892202601840640)*x 5 +
  (Nat.rawCast 300749454139677355614409729480065024)*x 6 +
  ((Int.negOfNat 184457672816636694925121828092379136).rawCast)*x 7 +
  (Nat.rawCast 3449196443667028487399237436309504)*x 8 +
  ((Int.negOfNat 4359485802384672850388805746688).rawCast)*x 9

def slopeInterior16Form24 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 2674198095513344450484178627067904).rawCast)*x 0 +
  (Nat.rawCast 88764291490489939318842402873016320)*x 1 +
  ((Int.negOfNat 191661446755896543248300896275136512).rawCast)*x 2 +
  ((Int.negOfNat 969363569039659921041756242281758720).rawCast)*x 3 +
  ((Int.negOfNat 939428352241407165514403462862864384).rawCast)*x 4 +
  ((Int.negOfNat 783249156623558686235342766845460480).rawCast)*x 5 +
  ((Int.negOfNat 40525742292902729853283740288024576).rawCast)*x 6 +
  (Nat.rawCast 138630382515667592064625389537853440)*x 7 +
  ((Int.negOfNat 7215141997201538584695647168888832).rawCast)*x 8 +
  (Nat.rawCast 21948417564773953606020130406400)*x 9

def slopeInterior16Form25 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 133077687873737380738675249250304).rawCast)*x 1 +
  (Nat.rawCast 77822593933920368800933587242188800)*x 2 +
  ((Int.negOfNat 45311377958909219805120174344896512).rawCast)*x 3 +
  (Nat.rawCast 390520598417451970928670691534307328)*x 4 +
  (Nat.rawCast 211167522758319111046347492660609024)*x 5 +
  (Nat.rawCast 3315312082799101668799077729435648)*x 6 +
  ((Int.negOfNat 46232182143609853132788231454064640).rawCast)*x 7 +
  (Nat.rawCast 10299774456804801261591290752008192)*x 8 +
  ((Int.negOfNat 69251046188826395041238221848576).rawCast)*x 9

def slopeInterior16Form26 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 584408772211471541712144461463552).rawCast)*x 1 +
  (Nat.rawCast 54574033050875188772035310622081024)*x 2 +
  (Nat.rawCast 30386602496258069411492825923584000)*x 3 +
  (Nat.rawCast 96429824944896510701486795674091520)*x 4 +
  (Nat.rawCast 54443437592642508254753015734468608)*x 5 +
  (Nat.rawCast 37420886132839363152321664813891584)*x 6 +
  ((Int.negOfNat 4919596165357933829186750540414976).rawCast)*x 7 +
  ((Int.negOfNat 9415438743456326409949061364842496).rawCast)*x 8 +
  (Nat.rawCast 151840761363973869215564093718528)*x 9

def slopeInterior16Form27 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 9500697664695339935078004679507968)*x 2 +
  ((Int.negOfNat 13344888136275984627308604533243904).rawCast)*x 3 +
  ((Int.negOfNat 51823226975323112687437931788369920).rawCast)*x 4 +
  ((Int.negOfNat 60896748811842161566392088201789440).rawCast)*x 5 +
  ((Int.negOfNat 36190876135273163974147417244172288).rawCast)*x 6 +
  (Nat.rawCast 5072802204192583523648425804431360)*x 7 +
  (Nat.rawCast 4541207387757284189124275623428096)*x 8 +
  ((Int.negOfNat 236536300729944226239603447693312).rawCast)*x 9

def slopeInterior16Form28 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 532537471390668280380495300132864)*x 2 +
  ((Int.negOfNat 2291867404396686668930172082716672).rawCast)*x 3 +
  ((Int.negOfNat 2207792568525900089293243007631360).rawCast)*x 4 +
  (Nat.rawCast 13581771385903107661091827831799808)*x 5 +
  (Nat.rawCast 8832361838632434025702304061063168)*x 6 +
  (Nat.rawCast 1437969768643698422999037952131072)*x 7 +
  ((Int.negOfNat 102949907611045253722356597129216).rawCast)*x 8 +
  (Nat.rawCast 252420157288711141982262358179840)*x 9

def slopeInterior16Form29 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 585049248605330684195645266329600)*x 3 +
  (Nat.rawCast 2045846812813323258512740152508416)*x 4 +
  (Nat.rawCast 5479085564928373415725916271673344)*x 5 +
  (Nat.rawCast 3106347751226506071380844431278080)*x 6 +
  (Nat.rawCast 22662376544966671682204357099520)*x 7 +
  ((Int.negOfNat 901641467100228917073749930409984).rawCast)*x 8 +
  ((Int.negOfNat 162346178438183103177006941995008).rawCast)*x 9

def slopeInterior16Form30 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 89811223321295690055900595224576)*x 3 +
  ((Int.negOfNat 798108922685442367225233867276288).rawCast)*x 4 +
  ((Int.negOfNat 1917885827796692919899108262543360).rawCast)*x 5 +
  ((Int.negOfNat 2349038068601058144914690763915264).rawCast)*x 6 +
  ((Int.negOfNat 1201928058618414201618206388387840).rawCast)*x 7 +
  (Nat.rawCast 127370664998741185809402229161984)*x 8 +
  (Nat.rawCast 33797749559023924319108103929856)*x 9

def slopeInterior16Form31 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 259258576551497050465673737666560).rawCast)*x 4 +
  ((Int.negOfNat 209482025459185357197861325897728).rawCast)*x 5 +
  (Nat.rawCast 378122056168254484578927542009856)*x 6 +
  (Nat.rawCast 422043924302996678369095672922112)*x 7 +
  (Nat.rawCast 201720017459202150147284174635008)*x 8 +
  (Nat.rawCast 29581127074200952676853668118528)*x 9

def slopeInterior16Form32 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 16177813395656457968587930337280).rawCast)*x 4 +
  (Nat.rawCast 38802889894936800763782931415040)*x 5 +
  (Nat.rawCast 149600894752235961363251255574528)*x 6 +
  (Nat.rawCast 84196760590707547585959602159616)*x 7 +
  ((Int.negOfNat 43290502730507514462531540221952).rawCast)*x 8 +
  ((Int.negOfNat 17771436576819071873029748293632).rawCast)*x 9

def slopeInterior16Form33 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 13313746291763795087241567535104).rawCast)*x 5 +
  ((Int.negOfNat 60602051552907631551020135350272).rawCast)*x 6 +
  ((Int.negOfNat 70597374819717726943997205676032).rawCast)*x 7 +
  ((Int.negOfNat 41026109737758463967749333843968).rawCast)*x 8 +
  ((Int.negOfNat 4539828647244443288821297053696).rawCast)*x 9

def slopeInterior16Form34 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 2375809833784515781413914542080).rawCast)*x 5 +
  ((Int.negOfNat 3810447274609394117528480907264).rawCast)*x 6 +
  (Nat.rawCast 7411064840978504457928744894464)*x 7 +
  (Nat.rawCast 16987640672913837739770994753536)*x 8 +
  (Nat.rawCast 5779006391988992807158312599552)*x 9

def slopeInterior16Form35 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 2172894544646304256292441554944)*x 6 +
  (Nat.rawCast 2864137611788459441805827506176)*x 7 +
  (Nat.rawCast 1453023212598859261016618827776)*x 8 +
  ((Int.negOfNat 181574222831112613719265247232).rawCast)*x 9

def slopeInterior16Form36 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 108481453892864447543368482816)*x 6 +
  ((Int.negOfNat 814730224814523794607210233856).rawCast)*x 7 +
  ((Int.negOfNat 1848902199443442557528410423296).rawCast)*x 8 +
  ((Int.negOfNat 1047492830290600256246082699264).rawCast)*x 9

def slopeInterior16Form37 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 23201091815862240719501524992)*x 7 +
  (Nat.rawCast 212001846016218819151244820480)*x 8 +
  (Nat.rawCast 239127031066234501761406599168)*x 9

def slopeInterior16Form38 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 22896871635130559807040258048)*x 7 +
  (Nat.rawCast 57621589468850972123820195840)*x 8 +
  (Nat.rawCast 62802966489534663246200438784)*x 9

def slopeInterior16Form39 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 11511086627912386822507855872).rawCast)*x 8 +
  ((Int.negOfNat 26135377996894478637616594944).rawCast)*x 9

def slopeInterior16Form40 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 118168194093471133134225408).rawCast)*x 8 +
  (Nat.rawCast 270322930243138190221246464)*x 9

def slopeInterior16Form41 (x : ℕ → ℝ) : ℝ :=
  (Nat.rawCast 748021301396969051413020672)*x 9

def slopeInterior16Form42 (x : ℕ → ℝ) : ℝ :=
  ((Int.negOfNat 68409576932993375649398784).rawCast)*x 9

def slopeInterior16ClockForm (A : ℕ) (x : ℕ → ℝ) : ℝ :=
  (4/5)^(4-4)*slopeInterior16Form4 x*degreeElevationCoefficient 38 (4-4) A +
  (4/5)^(5-4)*slopeInterior16Form5 x*degreeElevationCoefficient 38 (5-4) A +
  (4/5)^(6-4)*slopeInterior16Form6 x*degreeElevationCoefficient 38 (6-4) A +
  (4/5)^(7-4)*slopeInterior16Form7 x*degreeElevationCoefficient 38 (7-4) A +
  (4/5)^(8-4)*slopeInterior16Form8 x*degreeElevationCoefficient 38 (8-4) A +
  (4/5)^(9-4)*slopeInterior16Form9 x*degreeElevationCoefficient 38 (9-4) A +
  (4/5)^(10-4)*slopeInterior16Form10 x*degreeElevationCoefficient 38 (10-4) A +
  (4/5)^(11-4)*slopeInterior16Form11 x*degreeElevationCoefficient 38 (11-4) A +
  (4/5)^(12-4)*slopeInterior16Form12 x*degreeElevationCoefficient 38 (12-4) A +
  (4/5)^(13-4)*slopeInterior16Form13 x*degreeElevationCoefficient 38 (13-4) A +
  (4/5)^(14-4)*slopeInterior16Form14 x*degreeElevationCoefficient 38 (14-4) A +
  (4/5)^(15-4)*slopeInterior16Form15 x*degreeElevationCoefficient 38 (15-4) A +
  (4/5)^(16-4)*slopeInterior16Form16 x*degreeElevationCoefficient 38 (16-4) A +
  (4/5)^(17-4)*slopeInterior16Form17 x*degreeElevationCoefficient 38 (17-4) A +
  (4/5)^(18-4)*slopeInterior16Form18 x*degreeElevationCoefficient 38 (18-4) A +
  (4/5)^(19-4)*slopeInterior16Form19 x*degreeElevationCoefficient 38 (19-4) A +
  (4/5)^(20-4)*slopeInterior16Form20 x*degreeElevationCoefficient 38 (20-4) A +
  (4/5)^(21-4)*slopeInterior16Form21 x*degreeElevationCoefficient 38 (21-4) A +
  (4/5)^(22-4)*slopeInterior16Form22 x*degreeElevationCoefficient 38 (22-4) A +
  (4/5)^(23-4)*slopeInterior16Form23 x*degreeElevationCoefficient 38 (23-4) A +
  (4/5)^(24-4)*slopeInterior16Form24 x*degreeElevationCoefficient 38 (24-4) A +
  (4/5)^(25-4)*slopeInterior16Form25 x*degreeElevationCoefficient 38 (25-4) A +
  (4/5)^(26-4)*slopeInterior16Form26 x*degreeElevationCoefficient 38 (26-4) A +
  (4/5)^(27-4)*slopeInterior16Form27 x*degreeElevationCoefficient 38 (27-4) A +
  (4/5)^(28-4)*slopeInterior16Form28 x*degreeElevationCoefficient 38 (28-4) A +
  (4/5)^(29-4)*slopeInterior16Form29 x*degreeElevationCoefficient 38 (29-4) A +
  (4/5)^(30-4)*slopeInterior16Form30 x*degreeElevationCoefficient 38 (30-4) A +
  (4/5)^(31-4)*slopeInterior16Form31 x*degreeElevationCoefficient 38 (31-4) A +
  (4/5)^(32-4)*slopeInterior16Form32 x*degreeElevationCoefficient 38 (32-4) A +
  (4/5)^(33-4)*slopeInterior16Form33 x*degreeElevationCoefficient 38 (33-4) A +
  (4/5)^(34-4)*slopeInterior16Form34 x*degreeElevationCoefficient 38 (34-4) A +
  (4/5)^(35-4)*slopeInterior16Form35 x*degreeElevationCoefficient 38 (35-4) A +
  (4/5)^(36-4)*slopeInterior16Form36 x*degreeElevationCoefficient 38 (36-4) A +
  (4/5)^(37-4)*slopeInterior16Form37 x*degreeElevationCoefficient 38 (37-4) A +
  (4/5)^(38-4)*slopeInterior16Form38 x*degreeElevationCoefficient 38 (38-4) A +
  (4/5)^(39-4)*slopeInterior16Form39 x*degreeElevationCoefficient 38 (39-4) A +
  (4/5)^(40-4)*slopeInterior16Form40 x*degreeElevationCoefficient 38 (40-4) A +
  (4/5)^(41-4)*slopeInterior16Form41 x*degreeElevationCoefficient 38 (41-4) A +
  (4/5)^(42-4)*slopeInterior16Form42 x*degreeElevationCoefficient 38 (42-4) A

def slopeInterior16TensorCoefficient (A B : ℕ) : ℝ :=
  slopeInterior16ClockForm A (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)

end
end HTGeometry.ThetaRatioKineticContraction

