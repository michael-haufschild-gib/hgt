import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.CompactAssembly




namespace HTGeometry.ThetaRatioInfinity

noncomputable section

def boundaryImClock76_0 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(NNRat.rawCast 27429101485 5159780352)) + (((9-d)^0*(0)) + ((9-d)^1*(Rat.rawCast (Int.negOfNat 184857827557) 417942208512)))) + ((((9-d)^1*(0)) + ((9-d)^2*(Rat.rawCast (Int.negOfNat 37242466582621) 15045919506432))) + (((9-d)^2*(0)) + ((9-d)^3*(NNRat.rawCast 25392432737659 33853318889472))))) + ((((9-d)^3*(0)) + (((9-d)^4*(Rat.rawCast (Int.negOfNat 20284677665801) 1828079220031488)) + ((9-d)^4*(0)))) + ((((9-d)^5*(Rat.rawCast (Int.negOfNat 1479421697135717) 65810851921133568)) + ((9-d)^5*(0))) + (((9-d)^6*(NNRat.rawCast 1119105389526979 296148833645101056)) + ((9-d)^6*(0)))))) + (((((9-d)^7*(Rat.rawCast (Int.negOfNat 742521673386751) 2665339502805909504)) + (((9-d)^7*(0)) + ((9-d)^8*(NNRat.rawCast 13468290577691 1332669751402954752)))) + ((((9-d)^8*(0)) + ((9-d)^9*(Rat.rawCast (Int.negOfNat 63860187804325) 431784999454557339648))) + (((9-d)^9*(0)) + ((9-d)^10*(0))))) + (((((9-d)^11*(0)) + ((9-d)^12*(0))) + (((9-d)^13*(0)) + ((9-d)^14*(0)))) + ((((9-d)^15*(0)) + ((9-d)^16*(0))) + (((9-d)^17*(0)) + ((9-d)^18*(0)))))))

def boundaryImClock76_0Norm (d : ℂ) : {c : ℂ // boundaryImClock76_0 d=c} := by

  have he : boundaryImClock76_0 d=boundaryImClock76_0 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_0]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_1 (d : ℂ) : ℂ :=
  (((((9-d)^0*(1 * NNRat.rawCast 1697645176421 11609505792)) + ((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 77546215409849) 835884417024))) + (((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 1254464250852989) 180551034077184)) + (((9-d)^3*(1 * NNRat.rawCast 35213777399831863 3249918613389312)) + ((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 2145131480309245) 914039610015744))))) + ((((9-d)^5*(1 * NNRat.rawCast 14783918267123351 65810851921133568)) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 2939577980692427) 789730223053602816)) + ((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 35338293534191977) 21322716022447276032)))) + (((9-d)^8*(1 * NNRat.rawCast 18980919410755759 95952222101012742144)) + (((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 2765220130844951) 287856666303038226432)) + ((9-d)^10*(1 * NNRat.rawCast 2763132821290541 15544259980364064227328))))))

def boundaryImClock76_1Norm (d : ℂ) : {c : ℂ // boundaryImClock76_1 d=c} := by

  have he : boundaryImClock76_1 d=boundaryImClock76_1 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_1]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_2 (d : ℂ) : ℂ :=
  (((((9-d)^0*(1 * NNRat.rawCast 196225277815531 123834728448)) + (((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 1815291212169305) 1253826625536)) + ((9-d)^2*(1 * NNRat.rawCast 996130696258992781 2888816545234944)))) + (((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 15747911874540521) 1083306204463104)) + (((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 305667986187197137) 38999023360671744)) + ((9-d)^5*(1 * NNRat.rawCast 259977087727915727 131621703842267136))))) + ((((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 150934558425116527) 592297667290202112)) + (((9-d)^7*(1 * NNRat.rawCast 102343859453501011 4738381338321616896)) + ((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 885911481751024529) 767617776808101937152)))) + (((9-d)^9*(1 * NNRat.rawCast 13412501716325153 575713332606076452864)) + (((9-d)^10*(1 * NNRat.rawCast 115602713701059643 124354079842912513818624)) + ((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 12177572871726983) 279796679646553156091904))))))

def boundaryImClock76_2Norm (d : ℂ) : {c : ℂ // boundaryImClock76_2 d=c} := by

  have he : boundaryImClock76_2 d=boundaryImClock76_2 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_2]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_3 (d : ℂ) : ℂ :=
  (((((9-d)^0*(1 * NNRat.rawCast 353780154807803 41278242816)) + (((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 145595861950152211) 17832200896512)) + ((9-d)^2*(1 * NNRat.rawCast 875971993557133867 320979616137216)))) + (((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 110290885026902232415) 207994791256915968)) + (((9-d)^4*(1 * NNRat.rawCast 259917494939025929 3656158440062976)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 104024458499492322599) 16847578091810193408))))) + ((((9-d)^6*(1 * NNRat.rawCast 23876849155910486101 151628202826291740672)) + (((9-d)^7*(1 * NNRat.rawCast 49325366184687466103 1364653825436625666048)) + ((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 61447296244520948231) 12281884428929630994432)))) + ((((9-d)^9*(1 * NNRat.rawCast 11462164070981874049 36845653286788892983296)) + ((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 10668827186198714329) 994832638743300110548992))) + (((9-d)^11*(1 * NNRat.rawCast 276250494121672511 2238373437172425248735232)) + ((9-d)^12*(1 * NNRat.rawCast 259263771223410611 80581443738207308954468352))))))

def boundaryImClock76_3Norm (d : ℂ) : {c : ℂ // boundaryImClock76_3 d=c} := by

  have he : boundaryImClock76_3 d=boundaryImClock76_3 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_3]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_4 (d : ℂ) : ℂ :=
  (((((9-d)^0*(1 * NNRat.rawCast 108052329608933 4586471424)) + (((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 259355272022446715) 17832200896512)) + ((9-d)^2*(1 * NNRat.rawCast 41754076126747365605 11555266180939776)))) + ((((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 153634139936233586977) 207994791256915968)) + ((9-d)^4*(1 * NNRat.rawCast 2332084216577419178165 14975624970497949696))) + (((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 8012122957936442058515) 269561249468963094528)) + ((9-d)^6*(1 * NNRat.rawCast 174567286430279108027 37907050706572935168))))) + ((((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 2788856400941062613429) 5458615301746502664192)) + (((9-d)^8*(1 * NNRat.rawCast 1662452534149833013517 49127537715718523977728)) + ((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 831144632839076075257) 884295678882933431599104)))) + ((((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 11602777841668913155) 994832638743300110548992)) + ((9-d)^11*(1 * NNRat.rawCast 36715794121288289951 35813974994758803979763712))) + (((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 6771534277469186855) 644651549905658471635746816)) + ((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 308296208412382897) 3867909299433950829814480896))))))

def boundaryImClock76_4Norm (d : ℂ) : {c : ℂ // boundaryImClock76_4 d=c} := by

  have he : boundaryImClock76_4 d=boundaryImClock76_4 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_4]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_5 (d : ℂ) : ℂ :=
  (((((9-d)^0*(1 * NNRat.rawCast 235771451135333 9172942848)) + (((9-d)^1*(1 * NNRat.rawCast 102538004872463045 3962711310336)) + ((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 69542130774647286185) 3851755393646592)))) + ((((9-d)^3*(1 * NNRat.rawCast 1282628309404222887073 277326388342554624)) + ((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 11095787700535033481053) 14975624970497949696))) + (((9-d)^5*(1 * NNRat.rawCast 22315043395977035489309 269561249468963094528)) + ((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 7284592085209150152173) 1213025622610333925376))))) + (((((9-d)^7*(1 * NNRat.rawCast 1171637831918493252461 5458615301746502664192)) + ((9-d)^8*(1 * NNRat.rawCast 603891207997987813253 49127537715718523977728))) + (((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 2650852379824084196465) 884295678882933431599104)) + ((9-d)^10*(1 * NNRat.rawCast 278565705665590818863 1326443518324400147398656)))) + ((((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 2651240975580384035) 663221759162200073699328)) + ((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 41233895519141854669) 644651549905658471635746816))) + (((9-d)^13*(1 * NNRat.rawCast 1733146236921181453 11603727898301852489443442688)) + ((9-d)^14*(1 * NNRat.rawCast 33325770944820067 52216775542358336202495492096))))))

def boundaryImClock76_5Norm (d : ℂ) : {c : ℂ // boundaryImClock76_5 d=c} := by

  have he : boundaryImClock76_5 d=boundaryImClock76_5 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_5]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_6 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 403807254809563) 24461180928)) + ((9-d)^1*(1 * NNRat.rawCast 74291364526466905 660451885056))) + (((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 44837104917074734837) 1283918464548864)) + ((9-d)^3*(1 * NNRat.rawCast 1548806645332958792549 415989582513831936)))) + ((((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 11044526420847116351173) 29951249940995899392)) + ((9-d)^5*(1 * NNRat.rawCast 37548666297781708544957 269561249468963094528))) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 3662866265733844675643) 101085468550861160448)) + ((9-d)^7*(1 * NNRat.rawCast 8923524902276450482633 1819538433915500888064))))) + (((((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 34444039147129021737943) 98255075431437047955456)) + ((9-d)^9*(1 * NNRat.rawCast 11124450723713509024759 884295678882933431599104))) + (((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 730400333513838868537) 3979330554973200442195968)) + ((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 51231536509561229437) 11937991664919601326587904)))) + ((((9-d)^12*(1 * NNRat.rawCast 129834755092999434521 429767699937105647757164544)) + ((9-d)^13*(1 * NNRat.rawCast 6375695219256325151 3867909299433950829814480896))) + (((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 2150726749913651) 26108387771179168101247746048)) + ((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 20228983537427) 14685968121288282056951857152))))))

def boundaryImClock76_6Norm (d : ℂ) : {c : ℂ // boundaryImClock76_6 d=c} := by

  have he : boundaryImClock76_6 d=boundaryImClock76_6 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_6]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_7 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 553194879498421) 8153726976)) + ((9-d)^1*(1 * NNRat.rawCast 144758318102038195 2641807540224))) + (((9-d)^2*(1 * NNRat.rawCast 24208145906366581123 427972821516288)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 174126955421105363063) 6847565144260608)))) + ((((9-d)^4*(1 * NNRat.rawCast 15361466634911803010177 3327916660110655488)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 158870754839314040804773) 269561249468963094528))) + (((9-d)^6*(1 * NNRat.rawCast 90036390415964904175955 1213025622610333925376)) + ((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 43882471341432012974747) 5458615301746502664192))))) + (((((9-d)^8*(1 * NNRat.rawCast 43813546331831456080615 98255075431437047955456)) + ((9-d)^9*(1 * NNRat.rawCast 1452750819988746324919 294765226294311143866368))) + (((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 2967678770428371016883) 1989665277486600221097984)) + ((9-d)^11*(1 * NNRat.rawCast 876512525061514920299 23875983329839202653175808)))) + ((((9-d)^12*(1 * NNRat.rawCast 40891582619342933323 429767699937105647757164544)) + ((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 56090595233724044413) 11603727898301852489443442688))) + (((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 215813021449087265) 17405591847452778734165164032)) + (((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 49776973961981) 26108387771179168101247746048)) + ((9-d)^16*(1 * NNRat.rawCast 121763303179 264347426183189077025133428736)))))))

def boundaryImClock76_7Norm (d : ℂ) : {c : ℂ // boundaryImClock76_7 d=c} := by

  have he : boundaryImClock76_7 d=boundaryImClock76_7 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_7]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_8 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 78086561417617) 905969664)) + ((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 57764338619576083) 440301256704))) + (((9-d)^2*(1 * NNRat.rawCast 754723872866343775 7925422620672)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 424643147979146083777) 184884258895036416)))) + ((((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 20474442936624974109997) 7487812485248974848)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 1332887890223042354405) 134780624734481547264))) + (((9-d)^6*(1 * NNRat.rawCast 65594174281734999347747 606512811305166962688)) + (((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 87546033245226997776389) 5458615301746502664192)) + ((9-d)^8*(1 * NNRat.rawCast 27484358263067175510793 24563768857859261988864)))))) + (((((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 28621178566725299905333) 442147839441466715799552)) + ((9-d)^10*(1 * NNRat.rawCast 6732687577698146896513 1989665277486600221097984))) + (((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 907436930742855671087) 23875983329839202653175808)) + ((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 780432523886176868077) 322325774952829235817873408)))) + ((((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 40581628574320095505) 5801863949150926244721721344)) + ((9-d)^14*(1 * NNRat.rawCast 438359376756264859 26108387771179168101247746048))) + (((9-d)^15*(1 * NNRat.rawCast 9251706189649 407943558924674501581996032)) + (((9-d)^16*(1 * NNRat.rawCast 295754879875 264347426183189077025133428736)) + ((9-d)^17*(1 * NNRat.rawCast 5764801 148695427228043855826637553664)))))))

def boundaryImClock76_8Norm (d : ℂ) : {c : ℂ // boundaryImClock76_8 d=c} := by

  have he : boundaryImClock76_8 d=boundaryImClock76_8 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_8]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_9 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 47653438766765) 301989888)) + ((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 709180814539553) 10871635968))) + (((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 1452100659165115363) 11888133931008)) + ((9-d)^3*(1 * NNRat.rawCast 1197431664934064086981 15407021574586368)))) + ((((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 12180153571556963385197) 831979165027663872)) + ((9-d)^5*(1 * NNRat.rawCast 822779298208131658295 415989582513831936))) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 36095393956487947591759) 101085468550861160448)) + (((9-d)^7*(1 * NNRat.rawCast 265230337975473560334823 5458615301746502664192)) + ((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 75744369757104597786673) 24563768857859261988864)))))) + (((((9-d)^9*(1 * NNRat.rawCast 103686602394755897927 2046980738154938499072)) + ((9-d)^10*(1 * NNRat.rawCast 236052740124371921015 165805439790550018424832))) + (((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 6190141896446080159) 93265559882184385363968)) + ((9-d)^12*(1 * NNRat.rawCast 434824457127091522529 107441924984276411939291136)))) + ((((9-d)^13*(1 * NNRat.rawCast 20910924802386688763 483488662429243853726810112)) + ((9-d)^14*(1 * NNRat.rawCast 309441909453956615 4351397961863194683541291008))) + (((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 246438973711903) 78325163313537504303743238144)) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 1016211943691) 176231617455459384683422285824)) + ((9-d)^17*(1 * NNRat.rawCast 45294865 198260569637391807768850071552)))))))

def boundaryImClock76_9Norm (d : ℂ) : {c : ℂ // boundaryImClock76_9 d=c} := by

  have he : boundaryImClock76_9 d=boundaryImClock76_9 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_9]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_10 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 43314015356077) 150994944)) + ((9-d)^1*(1 * NNRat.rawCast 3853735675901 2038431744))) + (((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 159961707471277067) 1761205026816)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 39840762943397988995) 1711891286065152)))) + ((((9-d)^4*(1 * NNRat.rawCast 2383920112706856025837 138663194171277312)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 1332203911636682979547) 623984373770747904))) + (((9-d)^6*(1 * NNRat.rawCast 22767639542521803714427 303256405652583481344)) + (((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 21394567256770296485579) 2729307650873251332096)) + ((9-d)^8*(1 * NNRat.rawCast 2803365520936702504999 4093961476309876998144)))))) + (((((9-d)^9*(1 * NNRat.rawCast 2178165190301217171071 18422826643394446491648)) + ((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 12490145536615428779039) 994832638743300110548992))) + (((9-d)^11*(1 * NNRat.rawCast 356100210095292795113 1989665277486600221097984)) + ((9-d)^12*(1 * NNRat.rawCast 84819599235729847945 53720962492138205969645568)))) + ((((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 11030220801096393163) 241744331214621926863405056)) + ((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 300497245475259401) 1450465987287731561180430336))) + (((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 5667455241208943) 39162581656768752151871619072)) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 14309462993) 3263548471397396012655968256)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 823543) 5507238045483105771356946432)))))))

def boundaryImClock76_10Norm (d : ℂ) : {c : ℂ // boundaryImClock76_10 d=c} := by

  have he : boundaryImClock76_10 d=boundaryImClock76_10 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_10]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_11 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 7215135204485) 25165824)) + ((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 5322463246392437) 16307453952))) + (((9-d)^2*(1 * NNRat.rawCast 359448526698477877 1761205026816)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 16889721904996319377) 142657607172096)))) + ((((9-d)^4*(1 * NNRat.rawCast 246548045283582801661 11555266180939776)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 12827771875331338031779) 5615859363936731136))) + (((9-d)^6*(1 * NNRat.rawCast 8694167503360249384345 16847578091810193408)) + (((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 106111160218854659779825) 1364653825436625666048)) + ((9-d)^8*(1 * NNRat.rawCast 59835780665371331143681 12281884428929630994432)))))) + (((((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 12397113453579769175881) 55268479930183339474944)) + ((9-d)^10*(1 * NNRat.rawCast 3756422781579954181171 248708159685825027637248))) + (((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 354172127059892889013) 2238373437172425248735232)) + ((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 32236630840567180195) 2238373437172425248735232)))) + ((((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 15871506289105900207) 241744331214621926863405056)) + ((9-d)^14*(1 * NNRat.rawCast 136391578290798275 2175698980931597341770645504))) + (((9-d)^15*(1 * NNRat.rawCast 1440045205742479 6527096942794792025311936512)) + (((9-d)^16*(1 * NNRat.rawCast 637681789283 19581290828384376075935809536)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 24118045) 11014476090966211542713892864)))))))

def boundaryImClock76_11Norm (d : ℂ) : {c : ℂ // boundaryImClock76_11 d=c} := by

  have he : boundaryImClock76_11 d=boundaryImClock76_11 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_11]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_12 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 1480272887473) 8388608)) + ((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 487403723358485) 1811939328))) + (((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 42015173395724431) 293534171136)) + ((9-d)^3*(1 * NNRat.rawCast 508970529139131805 3962711310336)))) + ((((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 575934161908701477383) 11555266180939776)) + ((9-d)^5*(1 * NNRat.rawCast 3716147500141826913041 467988280328060928))) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 6657888251587653932215) 9476762676643233792)) + (((9-d)^7*(1 * NNRat.rawCast 842726915517664572821 14215144014964850688)) + ((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 224033475842517801395) 75814101413145870336)))))) + (((((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 50050519095905892985) 3454279995636458717184)) + ((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 431107406961313709959) 82902719895275009212416))) + (((9-d)^11*(1 * NNRat.rawCast 268304706585517554167 1119186718586212624367616)) + ((9-d)^12*(1 * NNRat.rawCast 357808292494234197353 13430240623034551492411392)))) + ((((9-d)^13*(1 * NNRat.rawCast 1700590599923844623 6715120311517275746205696)) + ((9-d)^14*(1 * NNRat.rawCast 48146518272214579 90654124205483222573776896))) + (((9-d)^15*(1 * NNRat.rawCast 10405510821289 67990593154112416930332672)) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 119061920929) 3263548471397396012655968256)) + ((9-d)^17*(1 * NNRat.rawCast 991613 917873007580517628559491072)))))))

def boundaryImClock76_12Norm (d : ℂ) : {c : ℂ // boundaryImClock76_12 d=c} := by

  have he : boundaryImClock76_12 d=boundaryImClock76_12 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_12]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_13 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 385687074393) 8388608)) + ((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 140435009266811) 905969664))) + (((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 8053311891194269) 146767085568)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 70663623927078715) 1320903770112)))) + ((((9-d)^4*(1 * NNRat.rawCast 34343830477044446173 962938848411648)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 219802882573527109825) 25999348907114496))) + (((9-d)^6*(1 * NNRat.rawCast 152141996556233844401 263243407684534272)) + (((9-d)^7*(1 * NNRat.rawCast 3704515312396018479853 85290864089789104128)) + ((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 4537868508482449510447) 511745184538734624768)))))) + (((((9-d)^9*(1 * NNRat.rawCast 7789231460582828545727 13817119982545834868736)) + ((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 183488636763979444499) 124354079842912513818624))) + (((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 306893460640637783507) 373062239528737541455872)) + ((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 345076523572688408639) 10072680467275913619308544)))) + ((((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 416739548982250871) 1119186718586212624367616)) + ((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 1883935891253153) 1678780077879318936551424))) + (((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 3057373250401) 3777255175228467607240704)) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 518880257) 30218041401827740857925632)) + ((9-d)^17*(1 * NNRat.rawCast 2518649 271962372616449667721330688)))))))

def boundaryImClock76_13Norm (d : ℂ) : {c : ℂ // boundaryImClock76_13 d=c} := by

  have he : boundaryImClock76_13 d=boundaryImClock76_13 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_13]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_14 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * NNRat.rawCast 4514555151 524288)) + ((9-d)^1*(1 * NNRat.rawCast 12147692281 8388608))) + (((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 1581418449566329) 24461180928)) + ((9-d)^3*(1 * NNRat.rawCast 2244965563384789 165112971264)))) + ((((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 443197318256033323) 26748301344768)) + ((9-d)^5*(1 * NNRat.rawCast 66110645978421189829 12999674453557248))) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 48826751755423573697) 131621703842267136)) + (((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 1275647106807323008463) 14215144014964850688)) + ((9-d)^8*(1 * NNRat.rawCast 6720583837678091972885 383808888404050968576)))))) + (((((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 1181084971815308952085) 1151426665212152905728)) + ((9-d)^10*(1 * NNRat.rawCast 42200567518653481859 62177039921456256909312))) + (((9-d)^11*(1 * NNRat.rawCast 226520684664239487989 139898339823276578045952)) + ((9-d)^12*(1 * NNRat.rawCast 29744438864974513301 839390038939659468275712)))) + ((((9-d)^13*(1 * NNRat.rawCast 20655960538821725 62177039921456256909312)) + ((9-d)^14*(1 * NNRat.rawCast 957224681919997 839390038939659468275712))) + (((9-d)^15*(1 * NNRat.rawCast 2820366673361 2518170116818978404827136)) + (((9-d)^16*(1 * NNRat.rawCast 1155165971 7554510350456935214481408)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 171157) 16997648288528104232583168)))))))

def boundaryImClock76_14Norm (d : ℂ) : {c : ℂ // boundaryImClock76_14 d=c} := by

  have he : boundaryImClock76_14 d=boundaryImClock76_14 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_14]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_15 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * NNRat.rawCast 31307254623 4194304)) + ((9-d)^1*(1 * NNRat.rawCast 104806913525 4194304))) + (((9-d)^2*(1 * NNRat.rawCast 59150350688339 4076863488)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 852519606732089) 41278242816)))) + ((((9-d)^4*(1 * NNRat.rawCast 418625329293845641 53496602689536)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 3846618513379848161) 1444408272617472))) + (((9-d)^6*(1 * NNRat.rawCast 33730229198817979157 175495605123022848)) + (((9-d)^7*(1 * NNRat.rawCast 129757651923090564323 1776893001870606336)) + ((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 767660047926502459415) 47976111050506371072)))))) + (((((9-d)^9*(1 * NNRat.rawCast 1178619399096245367895 1151426665212152905728)) + ((9-d)^10*(1 * NNRat.rawCast 2567486478940465339 10362839986909376151552))) + (((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 85208931354555915247) 46632779941092192681984)) + ((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 15460873766844241777) 559593359293106312183808)))) + ((((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 11378897714332081) 62177039921456256909312)) + ((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 179309194221989) 279796679646553156091904))) + (((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 370489998715) 419695019469829734137856)) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 834148613) 2518170116818978404827136)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 75943) 5665882762842701410861056)))))))

def boundaryImClock76_15Norm (d : ℂ) : {c : ℂ // boundaryImClock76_15 d=c} := by

  have he : boundaryImClock76_15 d=boundaryImClock76_15 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_15]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_16 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * NNRat.rawCast 2143063575 2097152)) + ((9-d)^1*(1 * NNRat.rawCast 19409725565 4194304))) + (((9-d)^2*(1 * NNRat.rawCast 13294660908083 679477248)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 19998355996631) 12230590464)))) + ((((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 12908401958343563) 4458050224128)) + ((9-d)^5*(1 * NNRat.rawCast 284744187583252627 240734712102912))) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 219997941271283275) 1828079220031488)) + (((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 2037969511651823051) 49358138940850176)) + ((9-d)^8*(1 * NNRat.rawCast 648917405575460129209 63968148067341828096)))))) + (((((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 1176811753864755329497) 1727139997818229358592)) + ((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 186993163112492717) 191904444202025484288))) + (((9-d)^11*(1 * NNRat.rawCast 13639926687849953299 10362839986909376151552)) + ((9-d)^12*(1 * NNRat.rawCast 693243905027729521 46632779941092192681984)))) + ((((9-d)^13*(1 * NNRat.rawCast 413417462475143 10362839986909376151552)) + ((9-d)^14*(1 * NNRat.rawCast 769261509433 7772129990182032113664))) + (((9-d)^15*(1 * NNRat.rawCast 51504189035 139898339823276578045952)) + (((9-d)^16*(1 * NNRat.rawCast 142757915 419695019469829734137856)) + ((9-d)^17*(1 * NNRat.rawCast 4859 157385632301186150301696)))))))

def boundaryImClock76_16Norm (d : ℂ) : {c : ℂ // boundaryImClock76_16 d=c} := by

  have he : boundaryImClock76_16 d=boundaryImClock76_16 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_16]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_17 (d : ℂ) : ℂ :=
  ((((((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 3537700575) 2097152)) + ((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 3493834939) 37748736))) + (((9-d)^3*(1 * NNRat.rawCast 5344082188891 1146617856)) + ((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 1220935858955671) 1486016741376)))) + ((((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 17834903652550199) 60183678025728)) + ((9-d)^6*(1 * NNRat.rawCast 157688744149548647 2437438960041984))) + (((9-d)^7*(1 * NNRat.rawCast 3802187662892235037 263243407684534272)) + ((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 51329531888847422429) 10661358011223638016))))) + (((((9-d)^9*(1 * NNRat.rawCast 12193802341173352315 35982083287879778304)) + ((9-d)^10*(1 * NNRat.rawCast 405894573348658397 287856666303038226432))) + (((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 1662912652745549323) 2590709996727344037888)) + ((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 69965147823604477) 15544259980364064227328)))) + ((((9-d)^13*(1 * NNRat.rawCast 29660368261253 863569998909114679296)) + ((9-d)^14*(1 * NNRat.rawCast 789598641251 3886064995091016056832))) + (((9-d)^15*(1 * NNRat.rawCast 6688106383 46632779941092192681984)) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 9341461) 104923754867457433534464)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 15397) 944313793807116901810176)))))))

def boundaryImClock76_17Norm (d : ℂ) : {c : ℂ // boundaryImClock76_17 d=c} := by

  have he : boundaryImClock76_17 d=boundaryImClock76_17 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_17]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_18 (d : ℂ) : ℂ :=
  ((((((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 20767772435) 18874368)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 2020697904707) 3057647616))) + (((9-d)^4*(1 * NNRat.rawCast 137647615951147 247669456896)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 80424429991165) 3343537668096)))) + ((((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 39646388344825051) 1624959306694656)) + ((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 326326367575866481) 131621703842267136))) + (((9-d)^8*(1 * NNRat.rawCast 302336333003724493 197432555763400704)) + ((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 2943027671712739409) 23988055525253185536))))) + (((((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 15397603669177765) 23988055525253185536)) + ((9-d)^11*(1 * NNRat.rawCast 168867306342210395 863569998909114679296))) + (((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 1449196054625731) 2590709996727344037888)) + ((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 6814808029253) 143928333151519113216)))) + ((((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 672978592433) 2590709996727344037888)) + ((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 3081004639) 7772129990182032113664))) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 1315019) 8743646238954786127872)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 245) 39346408075296537575424))))))

def boundaryImClock76_18Norm (d : ℂ) : {c : ℂ // boundaryImClock76_18 d=c} := by

  have he : boundaryImClock76_18 d=boundaryImClock76_18 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_18]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_19 (d : ℂ) : ℂ :=
  (((((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 15170363) 5308416)) + (((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 2820755267987) 20639121408)) + ((9-d)^5*(1 * NNRat.rawCast 28377898278787 1114512556032)))) + ((((9-d)^6*(1 * NNRat.rawCast 1261522490832569 270826551115776)) + ((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 17600440647665) 270826551115776))) + (((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 175095897514994519) 592297667290202112)) + ((9-d)^9*(1 * NNRat.rawCast 211017156126564169 7996018508417728512))))) + (((((9-d)^10*(1 * NNRat.rawCast 284337688244123 2665339502805909504)) + ((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 425029829189723) 23988055525253185536))) + (((9-d)^12*(1 * NNRat.rawCast 76578580512751 53973124931819667456)) + ((9-d)^13*(1 * NNRat.rawCast 1449123128095 47976111050506371072)))) + ((((9-d)^14*(1 * NNRat.rawCast 8068557079 47976111050506371072)) + ((9-d)^15*(1 * NNRat.rawCast 1208055905 3886064995091016056832))) + (((9-d)^16*(1 * NNRat.rawCast 70265 431784999454557339648)) + ((9-d)^17*(1 * NNRat.rawCast 47 4371823119477393063936))))))

def boundaryImClock76_19Norm (d : ℂ) : {c : ℂ // boundaryImClock76_19 d=c} := by

  have he : boundaryImClock76_19 d=boundaryImClock76_19 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_19]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_20 (d : ℂ) : ℂ :=
  (((((9-d)^4*(1 * NNRat.rawCast 4830556825 254803968)) + (((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 48440424487) 10319560704)) + ((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 3118383321145) 7522959753216)))) + ((((9-d)^7*(1 * NNRat.rawCast 27327568185443 609359740010496)) + ((9-d)^8*(1 * NNRat.rawCast 2756658698183947 98716277881700352))) + (((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 1546504537702189) 666334875701477376)) + ((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 29923102734281) 666334875701477376))))) + ((((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 58328125867511) 5997013881313296384)) + (((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 47362056109777) 71964166575759556608)) + ((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 128086332385) 11994027762626592768)))) + ((((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 6422749579) 107946249863639334912)) + ((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 37748009) 323838749590918004736))) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 126809) 1943032497545508028416)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 5) 1092955779869348265984))))))

def boundaryImClock76_20Norm (d : ℂ) : {c : ℂ // boundaryImClock76_20 d=c} := by

  have he : boundaryImClock76_20 d=boundaryImClock76_20 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_20]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImClock76_21 (d : ℂ) : ℂ :=
  (((((9-d)^5*(1 * NNRat.rawCast 1415963209 46438023168)) + (((9-d)^6*(1 * NNRat.rawCast 28759598545 3761479876608)) + ((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 122089290161) 76169967501312)))) + (((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 8201635047221) 8226356490141696)) + (((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 11523388527833) 222111625233825792)) + ((9-d)^10*(1 * NNRat.rawCast 2027567501417 111055812616912896))))) + ((((9-d)^11*(1 * NNRat.rawCast 697175670491 249875578388054016)) + (((9-d)^12*(1 * NNRat.rawCast 339604856879 2998506940656648192)) + ((9-d)^13*(1 * NNRat.rawCast 1088169557 666334875701477376)))) + ((((9-d)^14*(1 * NNRat.rawCast 160573861 17991041643939889152)) + ((9-d)^15*(1 * NNRat.rawCast 236221 13493281232954916864))) + (((9-d)^16*(1 * NNRat.rawCast 1589 161919374795459002368)) + ((9-d)^17*(1 * NNRat.rawCast 1 1457274373159131021312))))))

def boundaryImClock76_21Norm (d : ℂ) : {c : ℂ // boundaryImClock76_21 d=c} := by

  have he : boundaryImClock76_21 d=boundaryImClock76_21 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryImClock76_21]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryImVBlock76_0_0 (h : ℂ) : ℂ :=
  ((((h ^ (21-0:ℕ) * (NNRat.rawCast 27429101485 5159780352)) + (h ^ (21-0:ℕ) * (0))) + ((h ^ (21-1:ℕ) * (1 * NNRat.rawCast 1697645176421 11609505792)) + (h ^ (21-2:ℕ) * (1 * NNRat.rawCast 196225277815531 123834728448)))) + (((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 353780154807803 41278242816)) + (h ^ (21-4:ℕ) * (1 * NNRat.rawCast 108052329608933 4586471424))) + ((h ^ (21-5:ℕ) * (1 * NNRat.rawCast 235771451135333 9172942848)) + ((h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 403807254809563) 24461180928)) + (h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 553194879498421) 8153726976))))))

def boundaryImVBlock76_1_0 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 78086561417617) 905969664)) + (h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 47653438766765) 301989888))) + ((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 43314015356077) 150994944)) + (h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 7215135204485) 25165824)))) + (((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1480272887473) 8388608)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 385687074393) 8388608))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 4514555151 524288)) + (h ^ (21-15:ℕ) * (1 * NNRat.rawCast 31307254623 4194304)))))

def boundaryImVBlock76_2_0 (h : ℂ) : ℂ :=
  (h ^ (21-16:ℕ) * (1 * NNRat.rawCast 2143063575 2097152))

theorem boundaryCompactImVC75_0_blocks76 (h : ℂ) :

    boundaryCompactImVC75_0 h=((boundaryImVBlock76_0_0 h) + ((boundaryImVBlock76_1_0 h) + (boundaryImVBlock76_2_0 h))) := by

  dsimp only [boundaryCompactImVC75_0,boundaryImVBlock76_0_0,boundaryImVBlock76_1_0,boundaryImVBlock76_2_0]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_1 (h : ℂ) : ℂ :=
  ((((h ^ (21-0:ℕ) * (Rat.rawCast (Int.negOfNat 184857827557) 417942208512)) + (h ^ (21-0:ℕ) * (0))) + ((h ^ (21-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 77546215409849) 835884417024)) + (h ^ (21-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1815291212169305) 1253826625536)))) + (((h ^ (21-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 145595861950152211) 17832200896512)) + (h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 259355272022446715) 17832200896512))) + ((h ^ (21-5:ℕ) * (1 * NNRat.rawCast 102538004872463045 3962711310336)) + ((h ^ (21-6:ℕ) * (1 * NNRat.rawCast 74291364526466905 660451885056)) + (h ^ (21-7:ℕ) * (1 * NNRat.rawCast 144758318102038195 2641807540224))))))

def boundaryImVBlock76_1_1 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 57764338619576083) 440301256704)) + (h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 709180814539553) 10871635968))) + ((h ^ (21-10:ℕ) * (1 * NNRat.rawCast 3853735675901 2038431744)) + (h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5322463246392437) 16307453952)))) + (((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 487403723358485) 1811939328)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 140435009266811) 905969664))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 12147692281 8388608)) + (h ^ (21-15:ℕ) * (1 * NNRat.rawCast 104806913525 4194304)))))

def boundaryImVBlock76_2_1 (h : ℂ) : ℂ :=
  ((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 19409725565 4194304)) + (h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3537700575) 2097152)))

theorem boundaryCompactImVC75_1_blocks76 (h : ℂ) :

    boundaryCompactImVC75_1 h=((boundaryImVBlock76_0_1 h) + ((boundaryImVBlock76_1_1 h) + (boundaryImVBlock76_2_1 h))) := by

  dsimp only [boundaryCompactImVC75_1,boundaryImVBlock76_0_1,boundaryImVBlock76_1_1,boundaryImVBlock76_2_1]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_2 (h : ℂ) : ℂ :=
  ((((h ^ (21-0:ℕ) * (Rat.rawCast (Int.negOfNat 37242466582621) 15045919506432)) + (h ^ (21-0:ℕ) * (0))) + ((h ^ (21-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1254464250852989) 180551034077184)) + (h ^ (21-2:ℕ) * (1 * NNRat.rawCast 996130696258992781 2888816545234944)))) + (((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 875971993557133867 320979616137216)) + (h ^ (21-4:ℕ) * (1 * NNRat.rawCast 41754076126747365605 11555266180939776))) + ((h ^ (21-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 69542130774647286185) 3851755393646592)) + ((h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 44837104917074734837) 1283918464548864)) + (h ^ (21-7:ℕ) * (1 * NNRat.rawCast 24208145906366581123 427972821516288))))))

def boundaryImVBlock76_1_2 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * NNRat.rawCast 754723872866343775 7925422620672)) + (h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1452100659165115363) 11888133931008))) + ((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 159961707471277067) 1761205026816)) + (h ^ (21-11:ℕ) * (1 * NNRat.rawCast 359448526698477877 1761205026816)))) + (((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 42015173395724431) 293534171136)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8053311891194269) 146767085568))) + ((h ^ (21-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1581418449566329) 24461180928)) + (h ^ (21-15:ℕ) * (1 * NNRat.rawCast 59150350688339 4076863488)))))

def boundaryImVBlock76_2_2 (h : ℂ) : ℂ :=
  ((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 13294660908083 679477248)) + ((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3493834939) 37748736)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 20767772435) 18874368))))

theorem boundaryCompactImVC75_2_blocks76 (h : ℂ) :

    boundaryCompactImVC75_2 h=((boundaryImVBlock76_0_2 h) + ((boundaryImVBlock76_1_2 h) + (boundaryImVBlock76_2_2 h))) := by

  dsimp only [boundaryCompactImVC75_2,boundaryImVBlock76_0_2,boundaryImVBlock76_1_2,boundaryImVBlock76_2_2]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_3 (h : ℂ) : ℂ :=
  ((((h ^ (21-0:ℕ) * (NNRat.rawCast 25392432737659 33853318889472)) + (h ^ (21-0:ℕ) * (0))) + ((h ^ (21-1:ℕ) * (1 * NNRat.rawCast 35213777399831863 3249918613389312)) + (h ^ (21-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15747911874540521) 1083306204463104)))) + (((h ^ (21-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 110290885026902232415) 207994791256915968)) + (h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 153634139936233586977) 207994791256915968))) + ((h ^ (21-5:ℕ) * (1 * NNRat.rawCast 1282628309404222887073 277326388342554624)) + ((h ^ (21-6:ℕ) * (1 * NNRat.rawCast 1548806645332958792549 415989582513831936)) + (h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 174126955421105363063) 6847565144260608))))))

def boundaryImVBlock76_1_3 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 424643147979146083777) 184884258895036416)) + (h ^ (21-9:ℕ) * (1 * NNRat.rawCast 1197431664934064086981 15407021574586368))) + ((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 39840762943397988995) 1711891286065152)) + (h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 16889721904996319377) 142657607172096)))) + (((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 508970529139131805 3962711310336)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 70663623927078715) 1320903770112))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 2244965563384789 165112971264)) + (h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 852519606732089) 41278242816)))))

def boundaryImVBlock76_2_3 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 19998355996631) 12230590464)) + (h ^ (21-17:ℕ) * (1 * NNRat.rawCast 5344082188891 1146617856))) + ((h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2020697904707) 3057647616)) + (h ^ (21-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15170363) 5308416))))

theorem boundaryCompactImVC75_3_blocks76 (h : ℂ) :

    boundaryCompactImVC75_3 h=((boundaryImVBlock76_0_3 h) + ((boundaryImVBlock76_1_3 h) + (boundaryImVBlock76_2_3 h))) := by

  dsimp only [boundaryCompactImVC75_3,boundaryImVBlock76_0_3,boundaryImVBlock76_1_3,boundaryImVBlock76_2_3]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_4 (h : ℂ) : ℂ :=
  ((((h ^ (21-0:ℕ) * (Rat.rawCast (Int.negOfNat 20284677665801) 1828079220031488)) + (h ^ (21-0:ℕ) * (0))) + ((h ^ (21-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2145131480309245) 914039610015744)) + (h ^ (21-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 305667986187197137) 38999023360671744)))) + (((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 259917494939025929 3656158440062976)) + (h ^ (21-4:ℕ) * (1 * NNRat.rawCast 2332084216577419178165 14975624970497949696))) + ((h ^ (21-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11095787700535033481053) 14975624970497949696)) + ((h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11044526420847116351173) 29951249940995899392)) + (h ^ (21-7:ℕ) * (1 * NNRat.rawCast 15361466634911803010177 3327916660110655488))))))

def boundaryImVBlock76_1_4 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 20474442936624974109997) 7487812485248974848)) + (h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12180153571556963385197) 831979165027663872))) + ((h ^ (21-10:ℕ) * (1 * NNRat.rawCast 2383920112706856025837 138663194171277312)) + (h ^ (21-11:ℕ) * (1 * NNRat.rawCast 246548045283582801661 11555266180939776)))) + (((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 575934161908701477383) 11555266180939776)) + (h ^ (21-13:ℕ) * (1 * NNRat.rawCast 34343830477044446173 962938848411648))) + ((h ^ (21-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 443197318256033323) 26748301344768)) + (h ^ (21-15:ℕ) * (1 * NNRat.rawCast 418625329293845641 53496602689536)))))

def boundaryImVBlock76_2_4 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12908401958343563) 4458050224128)) + (h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1220935858955671) 1486016741376))) + ((h ^ (21-18:ℕ) * (1 * NNRat.rawCast 137647615951147 247669456896)) + ((h ^ (21-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2820755267987) 20639121408)) + (h ^ (21-20:ℕ) * (1 * NNRat.rawCast 4830556825 254803968)))))

theorem boundaryCompactImVC75_4_blocks76 (h : ℂ) :

    boundaryCompactImVC75_4 h=((boundaryImVBlock76_0_4 h) + ((boundaryImVBlock76_1_4 h) + (boundaryImVBlock76_2_4 h))) := by

  dsimp only [boundaryCompactImVC75_4,boundaryImVBlock76_0_4,boundaryImVBlock76_1_4,boundaryImVBlock76_2_4]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_5 (h : ℂ) : ℂ :=
  ((((h ^ (21-0:ℕ) * (Rat.rawCast (Int.negOfNat 1479421697135717) 65810851921133568)) + (h ^ (21-0:ℕ) * (0))) + ((h ^ (21-1:ℕ) * (1 * NNRat.rawCast 14783918267123351 65810851921133568)) + (h ^ (21-2:ℕ) * (1 * NNRat.rawCast 259977087727915727 131621703842267136)))) + (((h ^ (21-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 104024458499492322599) 16847578091810193408)) + (h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8012122957936442058515) 269561249468963094528))) + ((h ^ (21-5:ℕ) * (1 * NNRat.rawCast 22315043395977035489309 269561249468963094528)) + ((h ^ (21-6:ℕ) * (1 * NNRat.rawCast 37548666297781708544957 269561249468963094528)) + (h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 158870754839314040804773) 269561249468963094528))))))

def boundaryImVBlock76_1_5 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1332887890223042354405) 134780624734481547264)) + (h ^ (21-9:ℕ) * (1 * NNRat.rawCast 822779298208131658295 415989582513831936))) + ((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1332203911636682979547) 623984373770747904)) + (h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12827771875331338031779) 5615859363936731136)))) + (((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 3716147500141826913041 467988280328060928)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 219802882573527109825) 25999348907114496))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 66110645978421189829 12999674453557248)) + (h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3846618513379848161) 1444408272617472)))))

def boundaryImVBlock76_2_5 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 284744187583252627 240734712102912)) + ((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 17834903652550199) 60183678025728)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 80424429991165) 3343537668096)))) + ((h ^ (21-19:ℕ) * (1 * NNRat.rawCast 28377898278787 1114512556032)) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 48440424487) 10319560704)) + (h ^ (21-21:ℕ) * (1 * NNRat.rawCast 1415963209 46438023168)))))

theorem boundaryCompactImVC75_5_blocks76 (h : ℂ) :

    boundaryCompactImVC75_5 h=((boundaryImVBlock76_0_5 h) + ((boundaryImVBlock76_1_5 h) + (boundaryImVBlock76_2_5 h))) := by

  dsimp only [boundaryCompactImVC75_5,boundaryImVBlock76_0_5,boundaryImVBlock76_1_5,boundaryImVBlock76_2_5]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_6 (h : ℂ) : ℂ :=
  ((((h ^ (21-0:ℕ) * (NNRat.rawCast 1119105389526979 296148833645101056)) + (h ^ (21-0:ℕ) * (0))) + ((h ^ (21-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2939577980692427) 789730223053602816)) + (h ^ (21-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 150934558425116527) 592297667290202112)))) + (((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 23876849155910486101 151628202826291740672)) + (h ^ (21-4:ℕ) * (1 * NNRat.rawCast 174567286430279108027 37907050706572935168))) + ((h ^ (21-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 7284592085209150152173) 1213025622610333925376)) + ((h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3662866265733844675643) 101085468550861160448)) + (h ^ (21-7:ℕ) * (1 * NNRat.rawCast 90036390415964904175955 1213025622610333925376))))))

def boundaryImVBlock76_1_6 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * NNRat.rawCast 65594174281734999347747 606512811305166962688)) + (h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 36095393956487947591759) 101085468550861160448))) + ((h ^ (21-10:ℕ) * (1 * NNRat.rawCast 22767639542521803714427 303256405652583481344)) + (h ^ (21-11:ℕ) * (1 * NNRat.rawCast 8694167503360249384345 16847578091810193408)))) + (((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6657888251587653932215) 9476762676643233792)) + (h ^ (21-13:ℕ) * (1 * NNRat.rawCast 152141996556233844401 263243407684534272))) + ((h ^ (21-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 48826751755423573697) 131621703842267136)) + (h ^ (21-15:ℕ) * (1 * NNRat.rawCast 33730229198817979157 175495605123022848)))))

def boundaryImVBlock76_2_6 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 219997941271283275) 1828079220031488)) + ((h ^ (21-17:ℕ) * (1 * NNRat.rawCast 157688744149548647 2437438960041984)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 39646388344825051) 1624959306694656)))) + ((h ^ (21-19:ℕ) * (1 * NNRat.rawCast 1261522490832569 270826551115776)) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3118383321145) 7522959753216)) + (h ^ (21-21:ℕ) * (1 * NNRat.rawCast 28759598545 3761479876608)))))

theorem boundaryCompactImVC75_6_blocks76 (h : ℂ) :

    boundaryCompactImVC75_6 h=((boundaryImVBlock76_0_6 h) + ((boundaryImVBlock76_1_6 h) + (boundaryImVBlock76_2_6 h))) := by

  dsimp only [boundaryCompactImVC75_6,boundaryImVBlock76_0_6,boundaryImVBlock76_1_6,boundaryImVBlock76_2_6]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_7 (h : ℂ) : ℂ :=
  ((((h ^ (21-0:ℕ) * (Rat.rawCast (Int.negOfNat 742521673386751) 2665339502805909504)) + (h ^ (21-0:ℕ) * (0))) + ((h ^ (21-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 35338293534191977) 21322716022447276032)) + (h ^ (21-2:ℕ) * (1 * NNRat.rawCast 102343859453501011 4738381338321616896)))) + (((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 49325366184687466103 1364653825436625666048)) + (h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2788856400941062613429) 5458615301746502664192))) + ((h ^ (21-5:ℕ) * (1 * NNRat.rawCast 1171637831918493252461 5458615301746502664192)) + ((h ^ (21-6:ℕ) * (1 * NNRat.rawCast 8923524902276450482633 1819538433915500888064)) + (h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 43882471341432012974747) 5458615301746502664192))))))

def boundaryImVBlock76_1_7 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 87546033245226997776389) 5458615301746502664192)) + (h ^ (21-9:ℕ) * (1 * NNRat.rawCast 265230337975473560334823 5458615301746502664192))) + ((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 21394567256770296485579) 2729307650873251332096)) + (h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 106111160218854659779825) 1364653825436625666048)))) + (((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 842726915517664572821 14215144014964850688)) + (h ^ (21-13:ℕ) * (1 * NNRat.rawCast 3704515312396018479853 85290864089789104128))) + ((h ^ (21-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1275647106807323008463) 14215144014964850688)) + (h ^ (21-15:ℕ) * (1 * NNRat.rawCast 129757651923090564323 1776893001870606336)))))

def boundaryImVBlock76_2_7 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2037969511651823051) 49358138940850176)) + ((h ^ (21-17:ℕ) * (1 * NNRat.rawCast 3802187662892235037 263243407684534272)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 326326367575866481) 131621703842267136)))) + ((h ^ (21-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 17600440647665) 270826551115776)) + ((h ^ (21-20:ℕ) * (1 * NNRat.rawCast 27327568185443 609359740010496)) + (h ^ (21-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 122089290161) 76169967501312)))))

theorem boundaryCompactImVC75_7_blocks76 (h : ℂ) :

    boundaryCompactImVC75_7 h=((boundaryImVBlock76_0_7 h) + ((boundaryImVBlock76_1_7 h) + (boundaryImVBlock76_2_7 h))) := by

  dsimp only [boundaryCompactImVC75_7,boundaryImVBlock76_0_7,boundaryImVBlock76_1_7,boundaryImVBlock76_2_7]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_8 (h : ℂ) : ℂ :=
  ((((h ^ (21-0:ℕ) * (NNRat.rawCast 13468290577691 1332669751402954752)) + (h ^ (21-0:ℕ) * (0))) + ((h ^ (21-1:ℕ) * (1 * NNRat.rawCast 18980919410755759 95952222101012742144)) + (h ^ (21-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 885911481751024529) 767617776808101937152)))) + (((h ^ (21-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 61447296244520948231) 12281884428929630994432)) + (h ^ (21-4:ℕ) * (1 * NNRat.rawCast 1662452534149833013517 49127537715718523977728))) + ((h ^ (21-5:ℕ) * (1 * NNRat.rawCast 603891207997987813253 49127537715718523977728)) + ((h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 34444039147129021737943) 98255075431437047955456)) + (h ^ (21-7:ℕ) * (1 * NNRat.rawCast 43813546331831456080615 98255075431437047955456))))))

def boundaryImVBlock76_1_8 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * NNRat.rawCast 27484358263067175510793 24563768857859261988864)) + (h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 75744369757104597786673) 24563768857859261988864))) + ((h ^ (21-10:ℕ) * (1 * NNRat.rawCast 2803365520936702504999 4093961476309876998144)) + (h ^ (21-11:ℕ) * (1 * NNRat.rawCast 59835780665371331143681 12281884428929630994432)))) + (((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 224033475842517801395) 75814101413145870336)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 4537868508482449510447) 511745184538734624768))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 6720583837678091972885 383808888404050968576)) + (h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 767660047926502459415) 47976111050506371072)))))

def boundaryImVBlock76_2_8 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 648917405575460129209 63968148067341828096)) + ((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 51329531888847422429) 10661358011223638016)) + (h ^ (21-18:ℕ) * (1 * NNRat.rawCast 302336333003724493 197432555763400704)))) + ((h ^ (21-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 175095897514994519) 592297667290202112)) + ((h ^ (21-20:ℕ) * (1 * NNRat.rawCast 2756658698183947 98716277881700352)) + (h ^ (21-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8201635047221) 8226356490141696)))))

theorem boundaryCompactImVC75_8_blocks76 (h : ℂ) :

    boundaryCompactImVC75_8 h=((boundaryImVBlock76_0_8 h) + ((boundaryImVBlock76_1_8 h) + (boundaryImVBlock76_2_8 h))) := by

  dsimp only [boundaryCompactImVC75_8,boundaryImVBlock76_0_8,boundaryImVBlock76_1_8,boundaryImVBlock76_2_8]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_9 (h : ℂ) : ℂ :=
  ((((h ^ (21-0:ℕ) * (Rat.rawCast (Int.negOfNat 63860187804325) 431784999454557339648)) + (h ^ (21-0:ℕ) * (0))) + ((h ^ (21-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2765220130844951) 287856666303038226432)) + (h ^ (21-2:ℕ) * (1 * NNRat.rawCast 13412501716325153 575713332606076452864)))) + (((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 11462164070981874049 36845653286788892983296)) + (h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 831144632839076075257) 884295678882933431599104))) + ((h ^ (21-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2650852379824084196465) 884295678882933431599104)) + ((h ^ (21-6:ℕ) * (1 * NNRat.rawCast 11124450723713509024759 884295678882933431599104)) + (h ^ (21-7:ℕ) * (1 * NNRat.rawCast 1452750819988746324919 294765226294311143866368))))))

def boundaryImVBlock76_1_9 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 28621178566725299905333) 442147839441466715799552)) + (h ^ (21-9:ℕ) * (1 * NNRat.rawCast 103686602394755897927 2046980738154938499072))) + ((h ^ (21-10:ℕ) * (1 * NNRat.rawCast 2178165190301217171071 18422826643394446491648)) + (h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12397113453579769175881) 55268479930183339474944)))) + (((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 50050519095905892985) 3454279995636458717184)) + (h ^ (21-13:ℕ) * (1 * NNRat.rawCast 7789231460582828545727 13817119982545834868736))) + ((h ^ (21-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1181084971815308952085) 1151426665212152905728)) + (h ^ (21-15:ℕ) * (1 * NNRat.rawCast 1178619399096245367895 1151426665212152905728)))))

def boundaryImVBlock76_2_9 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1176811753864755329497) 1727139997818229358592)) + ((h ^ (21-17:ℕ) * (1 * NNRat.rawCast 12193802341173352315 35982083287879778304)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2943027671712739409) 23988055525253185536)))) + ((h ^ (21-19:ℕ) * (1 * NNRat.rawCast 211017156126564169 7996018508417728512)) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1546504537702189) 666334875701477376)) + (h ^ (21-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11523388527833) 222111625233825792)))))

theorem boundaryCompactImVC75_9_blocks76 (h : ℂ) :

    boundaryCompactImVC75_9 h=((boundaryImVBlock76_0_9 h) + ((boundaryImVBlock76_1_9 h) + (boundaryImVBlock76_2_9 h))) := by

  dsimp only [boundaryCompactImVC75_9,boundaryImVBlock76_0_9,boundaryImVBlock76_1_9,boundaryImVBlock76_2_9]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_10 (h : ℂ) : ℂ :=
  ((((h ^ (21-1:ℕ) * (1 * NNRat.rawCast 2763132821290541 15544259980364064227328)) + (h ^ (21-2:ℕ) * (1 * NNRat.rawCast 115602713701059643 124354079842912513818624))) + ((h ^ (21-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 10668827186198714329) 994832638743300110548992)) + (h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11602777841668913155) 994832638743300110548992)))) + (((h ^ (21-5:ℕ) * (1 * NNRat.rawCast 278565705665590818863 1326443518324400147398656)) + (h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 730400333513838868537) 3979330554973200442195968))) + ((h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2967678770428371016883) 1989665277486600221097984)) + (h ^ (21-0:ℕ) * (0)))))

def boundaryImVBlock76_1_10 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * NNRat.rawCast 6732687577698146896513 1989665277486600221097984)) + (h ^ (21-9:ℕ) * (1 * NNRat.rawCast 236052740124371921015 165805439790550018424832))) + ((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12490145536615428779039) 994832638743300110548992)) + (h ^ (21-11:ℕ) * (1 * NNRat.rawCast 3756422781579954181171 248708159685825027637248)))) + (((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 431107406961313709959) 82902719895275009212416)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 183488636763979444499) 124354079842912513818624))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 42200567518653481859 62177039921456256909312)) + (h ^ (21-15:ℕ) * (1 * NNRat.rawCast 2567486478940465339 10362839986909376151552)))))

def boundaryImVBlock76_2_10 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 186993163112492717) 191904444202025484288)) + ((h ^ (21-17:ℕ) * (1 * NNRat.rawCast 405894573348658397 287856666303038226432)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15397603669177765) 23988055525253185536)))) + ((h ^ (21-19:ℕ) * (1 * NNRat.rawCast 284337688244123 2665339502805909504)) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 29923102734281) 666334875701477376)) + (h ^ (21-21:ℕ) * (1 * NNRat.rawCast 2027567501417 111055812616912896)))))

theorem boundaryCompactImVC75_10_blocks76 (h : ℂ) :

    boundaryCompactImVC75_10 h=((boundaryImVBlock76_0_10 h) + ((boundaryImVBlock76_1_10 h) + (boundaryImVBlock76_2_10 h))) := by

  dsimp only [boundaryCompactImVC75_10,boundaryImVBlock76_0_10,boundaryImVBlock76_1_10,boundaryImVBlock76_2_10]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_11 (h : ℂ) : ℂ :=
  (((h ^ (21-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12177572871726983) 279796679646553156091904)) + ((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 276250494121672511 2238373437172425248735232)) + (h ^ (21-4:ℕ) * (1 * NNRat.rawCast 36715794121288289951 35813974994758803979763712)))) + (((h ^ (21-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2651240975580384035) 663221759162200073699328)) + (h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 51231536509561229437) 11937991664919601326587904))) + ((h ^ (21-7:ℕ) * (1 * NNRat.rawCast 876512525061514920299 23875983329839202653175808)) + (h ^ (21-0:ℕ) * (0)))))

def boundaryImVBlock76_1_11 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 907436930742855671087) 23875983329839202653175808)) + (h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6190141896446080159) 93265559882184385363968))) + ((h ^ (21-10:ℕ) * (1 * NNRat.rawCast 356100210095292795113 1989665277486600221097984)) + (h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 354172127059892889013) 2238373437172425248735232)))) + (((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 268304706585517554167 1119186718586212624367616)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 306893460640637783507) 373062239528737541455872))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 226520684664239487989 139898339823276578045952)) + (h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 85208931354555915247) 46632779941092192681984)))))

def boundaryImVBlock76_2_11 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 13639926687849953299 10362839986909376151552)) + ((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1662912652745549323) 2590709996727344037888)) + (h ^ (21-18:ℕ) * (1 * NNRat.rawCast 168867306342210395 863569998909114679296)))) + ((h ^ (21-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 425029829189723) 23988055525253185536)) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 58328125867511) 5997013881313296384)) + (h ^ (21-21:ℕ) * (1 * NNRat.rawCast 697175670491 249875578388054016)))))

theorem boundaryCompactImVC75_11_blocks76 (h : ℂ) :

    boundaryCompactImVC75_11 h=((boundaryImVBlock76_0_11 h) + ((boundaryImVBlock76_1_11 h) + (boundaryImVBlock76_2_11 h))) := by

  dsimp only [boundaryCompactImVC75_11,boundaryImVBlock76_0_11,boundaryImVBlock76_1_11,boundaryImVBlock76_2_11]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_12 (h : ℂ) : ℂ :=
  (((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 259263771223410611 80581443738207308954468352)) + ((h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6771534277469186855) 644651549905658471635746816)) + (h ^ (21-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 41233895519141854669) 644651549905658471635746816)))) + ((h ^ (21-6:ℕ) * (1 * NNRat.rawCast 129834755092999434521 429767699937105647757164544)) + ((h ^ (21-7:ℕ) * (1 * NNRat.rawCast 40891582619342933323 429767699937105647757164544)) + (h ^ (21-0:ℕ) * (0)))))

def boundaryImVBlock76_1_12 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 780432523886176868077) 322325774952829235817873408)) + (h ^ (21-9:ℕ) * (1 * NNRat.rawCast 434824457127091522529 107441924984276411939291136))) + ((h ^ (21-10:ℕ) * (1 * NNRat.rawCast 84819599235729847945 53720962492138205969645568)) + (h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 32236630840567180195) 2238373437172425248735232)))) + (((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 357808292494234197353 13430240623034551492411392)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 345076523572688408639) 10072680467275913619308544))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 29744438864974513301 839390038939659468275712)) + (h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15460873766844241777) 559593359293106312183808)))))

def boundaryImVBlock76_2_12 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 693243905027729521 46632779941092192681984)) + ((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 69965147823604477) 15544259980364064227328)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1449196054625731) 2590709996727344037888)))) + ((h ^ (21-19:ℕ) * (1 * NNRat.rawCast 76578580512751 53973124931819667456)) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 47362056109777) 71964166575759556608)) + (h ^ (21-21:ℕ) * (1 * NNRat.rawCast 339604856879 2998506940656648192)))))

theorem boundaryCompactImVC75_12_blocks76 (h : ℂ) :

    boundaryCompactImVC75_12 h=((boundaryImVBlock76_0_12 h) + ((boundaryImVBlock76_1_12 h) + (boundaryImVBlock76_2_12 h))) := by

  dsimp only [boundaryCompactImVC75_12,boundaryImVBlock76_0_12,boundaryImVBlock76_1_12,boundaryImVBlock76_2_12]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_13 (h : ℂ) : ℂ :=
  (((h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 308296208412382897) 3867909299433950829814480896)) + (h ^ (21-5:ℕ) * (1 * NNRat.rawCast 1733146236921181453 11603727898301852489443442688))) + ((h ^ (21-6:ℕ) * (1 * NNRat.rawCast 6375695219256325151 3867909299433950829814480896)) + ((h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 56090595233724044413) 11603727898301852489443442688)) + (h ^ (21-0:ℕ) * (0)))))

def boundaryImVBlock76_1_13 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 40581628574320095505) 5801863949150926244721721344)) + (h ^ (21-9:ℕ) * (1 * NNRat.rawCast 20910924802386688763 483488662429243853726810112))) + ((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11030220801096393163) 241744331214621926863405056)) + (h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15871506289105900207) 241744331214621926863405056)))) + (((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 1700590599923844623 6715120311517275746205696)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 416739548982250871) 1119186718586212624367616))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 20655960538821725 62177039921456256909312)) + (h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11378897714332081) 62177039921456256909312)))))

def boundaryImVBlock76_2_13 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 413417462475143 10362839986909376151552)) + ((h ^ (21-17:ℕ) * (1 * NNRat.rawCast 29660368261253 863569998909114679296)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6814808029253) 143928333151519113216)))) + ((h ^ (21-19:ℕ) * (1 * NNRat.rawCast 1449123128095 47976111050506371072)) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 128086332385) 11994027762626592768)) + (h ^ (21-21:ℕ) * (1 * NNRat.rawCast 1088169557 666334875701477376)))))

theorem boundaryCompactImVC75_13_blocks76 (h : ℂ) :

    boundaryCompactImVC75_13 h=((boundaryImVBlock76_0_13 h) + ((boundaryImVBlock76_1_13 h) + (boundaryImVBlock76_2_13 h))) := by

  dsimp only [boundaryCompactImVC75_13,boundaryImVBlock76_0_13,boundaryImVBlock76_1_13,boundaryImVBlock76_2_13]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_14 (h : ℂ) : ℂ :=
  (((h ^ (21-5:ℕ) * (1 * NNRat.rawCast 33325770944820067 52216775542358336202495492096)) + (h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2150726749913651) 26108387771179168101247746048))) + ((h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 215813021449087265) 17405591847452778734165164032)) + (h ^ (21-0:ℕ) * (0))))

def boundaryImVBlock76_1_14 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * NNRat.rawCast 438359376756264859 26108387771179168101247746048)) + (h ^ (21-9:ℕ) * (1 * NNRat.rawCast 309441909453956615 4351397961863194683541291008))) + ((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 300497245475259401) 1450465987287731561180430336)) + (h ^ (21-11:ℕ) * (1 * NNRat.rawCast 136391578290798275 2175698980931597341770645504)))) + (((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 48146518272214579 90654124205483222573776896)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1883935891253153) 1678780077879318936551424))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 957224681919997 839390038939659468275712)) + (h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 179309194221989) 279796679646553156091904)))))

def boundaryImVBlock76_2_14 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 769261509433 7772129990182032113664)) + ((h ^ (21-17:ℕ) * (1 * NNRat.rawCast 789598641251 3886064995091016056832)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 672978592433) 2590709996727344037888)))) + ((h ^ (21-19:ℕ) * (1 * NNRat.rawCast 8068557079 47976111050506371072)) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6422749579) 107946249863639334912)) + (h ^ (21-21:ℕ) * (1 * NNRat.rawCast 160573861 17991041643939889152)))))

theorem boundaryCompactImVC75_14_blocks76 (h : ℂ) :

    boundaryCompactImVC75_14 h=((boundaryImVBlock76_0_14 h) + ((boundaryImVBlock76_1_14 h) + (boundaryImVBlock76_2_14 h))) := by

  dsimp only [boundaryCompactImVC75_14,boundaryImVBlock76_0_14,boundaryImVBlock76_1_14,boundaryImVBlock76_2_14]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_15 (h : ℂ) : ℂ :=
  ((h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 20228983537427) 14685968121288282056951857152)) + ((h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 49776973961981) 26108387771179168101247746048)) + (h ^ (21-0:ℕ) * (0))))

def boundaryImVBlock76_1_15 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * NNRat.rawCast 9251706189649 407943558924674501581996032)) + (h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 246438973711903) 78325163313537504303743238144))) + ((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5667455241208943) 39162581656768752151871619072)) + (h ^ (21-11:ℕ) * (1 * NNRat.rawCast 1440045205742479 6527096942794792025311936512)))) + (((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 10405510821289 67990593154112416930332672)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3057373250401) 3777255175228467607240704))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 2820366673361 2518170116818978404827136)) + (h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 370489998715) 419695019469829734137856)))))

def boundaryImVBlock76_2_15 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 51504189035 139898339823276578045952)) + ((h ^ (21-17:ℕ) * (1 * NNRat.rawCast 6688106383 46632779941092192681984)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3081004639) 7772129990182032113664)))) + ((h ^ (21-19:ℕ) * (1 * NNRat.rawCast 1208055905 3886064995091016056832)) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 37748009) 323838749590918004736)) + (h ^ (21-21:ℕ) * (1 * NNRat.rawCast 236221 13493281232954916864)))))

theorem boundaryCompactImVC75_15_blocks76 (h : ℂ) :

    boundaryCompactImVC75_15 h=((boundaryImVBlock76_0_15 h) + ((boundaryImVBlock76_1_15 h) + (boundaryImVBlock76_2_15 h))) := by

  dsimp only [boundaryCompactImVC75_15,boundaryImVBlock76_0_15,boundaryImVBlock76_1_15,boundaryImVBlock76_2_15]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_16 (h : ℂ) : ℂ :=
  ((h ^ (21-7:ℕ) * (1 * NNRat.rawCast 121763303179 264347426183189077025133428736)) + (h ^ (21-0:ℕ) * (0)))

def boundaryImVBlock76_1_16 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * NNRat.rawCast 295754879875 264347426183189077025133428736)) + (h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1016211943691) 176231617455459384683422285824))) + ((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 14309462993) 3263548471397396012655968256)) + (h ^ (21-11:ℕ) * (1 * NNRat.rawCast 637681789283 19581290828384376075935809536)))) + (((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 119061920929) 3263548471397396012655968256)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 518880257) 30218041401827740857925632))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 1155165971 7554510350456935214481408)) + (h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 834148613) 2518170116818978404827136)))))

def boundaryImVBlock76_2_16 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 142757915 419695019469829734137856)) + ((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 9341461) 104923754867457433534464)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1315019) 8743646238954786127872)))) + ((h ^ (21-19:ℕ) * (1 * NNRat.rawCast 70265 431784999454557339648)) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 126809) 1943032497545508028416)) + (h ^ (21-21:ℕ) * (1 * NNRat.rawCast 1589 161919374795459002368)))))

theorem boundaryCompactImVC75_16_blocks76 (h : ℂ) :

    boundaryCompactImVC75_16 h=((boundaryImVBlock76_0_16 h) + ((boundaryImVBlock76_1_16 h) + (boundaryImVBlock76_2_16 h))) := by

  dsimp only [boundaryCompactImVC75_16,boundaryImVBlock76_0_16,boundaryImVBlock76_1_16,boundaryImVBlock76_2_16]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_17 (h : ℂ) : ℂ :=
  (h ^ (21-0:ℕ) * (0))

def boundaryImVBlock76_1_17 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * NNRat.rawCast 5764801 148695427228043855826637553664)) + (h ^ (21-9:ℕ) * (1 * NNRat.rawCast 45294865 198260569637391807768850071552))) + ((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 823543) 5507238045483105771356946432)) + (h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 24118045) 11014476090966211542713892864)))) + (((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 991613 917873007580517628559491072)) + (h ^ (21-13:ℕ) * (1 * NNRat.rawCast 2518649 271962372616449667721330688))) + ((h ^ (21-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 171157) 16997648288528104232583168)) + (h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 75943) 5665882762842701410861056)))))

def boundaryImVBlock76_2_17 (h : ℂ) : ℂ :=
  (((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 4859 157385632301186150301696)) + ((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15397) 944313793807116901810176)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 245) 39346408075296537575424)))) + ((h ^ (21-19:ℕ) * (1 * NNRat.rawCast 47 4371823119477393063936)) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5) 1092955779869348265984)) + (h ^ (21-21:ℕ) * (1 * NNRat.rawCast 1 1457274373159131021312)))))

theorem boundaryCompactImVC75_17_blocks76 (h : ℂ) :

    boundaryCompactImVC75_17 h=((boundaryImVBlock76_0_17 h) + ((boundaryImVBlock76_1_17 h) + (boundaryImVBlock76_2_17 h))) := by

  dsimp only [boundaryCompactImVC75_17,boundaryImVBlock76_0_17,boundaryImVBlock76_1_17,boundaryImVBlock76_2_17]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImVBlock76_0_18 (h : ℂ) : ℂ :=
  (h ^ (21-0:ℕ) * (0))

def boundaryImVBlock76_1_18 (h : ℂ) : ℂ :=
  0

def boundaryImVBlock76_2_18 (h : ℂ) : ℂ :=
  0

theorem boundaryCompactImVC75_18_blocks76 (h : ℂ) :

    boundaryCompactImVC75_18 h=((boundaryImVBlock76_0_18 h) + ((boundaryImVBlock76_1_18 h) + (boundaryImVBlock76_2_18 h))) := by

  dsimp only [boundaryCompactImVC75_18,boundaryImVBlock76_0_18,boundaryImVBlock76_1_18,boundaryImVBlock76_2_18]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryImClockBlock76_0 (h r : ℂ) : ℂ :=
  ((((h^(21-0:ℕ)*boundaryImClock76_0 (r*h^2)) + (h^(21-1:ℕ)*boundaryImClock76_1 (r*h^2))) + ((h^(21-2:ℕ)*boundaryImClock76_2 (r*h^2)) + (h^(21-3:ℕ)*boundaryImClock76_3 (r*h^2)))) + (((h^(21-4:ℕ)*boundaryImClock76_4 (r*h^2)) + (h^(21-5:ℕ)*boundaryImClock76_5 (r*h^2))) + ((h^(21-6:ℕ)*boundaryImClock76_6 (r*h^2)) + (h^(21-7:ℕ)*boundaryImClock76_7 (r*h^2)))))

def boundaryImVSumBlock76_0 (h r : ℂ) : ℂ :=
  ((((((9-r*h^2)^0*boundaryImVBlock76_0_0 h) + ((9-r*h^2)^1*boundaryImVBlock76_0_1 h)) + (((9-r*h^2)^2*boundaryImVBlock76_0_2 h) + ((9-r*h^2)^3*boundaryImVBlock76_0_3 h))) + ((((9-r*h^2)^4*boundaryImVBlock76_0_4 h) + ((9-r*h^2)^5*boundaryImVBlock76_0_5 h)) + (((9-r*h^2)^6*boundaryImVBlock76_0_6 h) + (((9-r*h^2)^7*boundaryImVBlock76_0_7 h) + ((9-r*h^2)^8*boundaryImVBlock76_0_8 h))))) + (((((9-r*h^2)^9*boundaryImVBlock76_0_9 h) + ((9-r*h^2)^10*boundaryImVBlock76_0_10 h)) + (((9-r*h^2)^11*boundaryImVBlock76_0_11 h) + (((9-r*h^2)^12*boundaryImVBlock76_0_12 h) + ((9-r*h^2)^13*boundaryImVBlock76_0_13 h)))) + ((((9-r*h^2)^14*boundaryImVBlock76_0_14 h) + ((9-r*h^2)^15*boundaryImVBlock76_0_15 h)) + (((9-r*h^2)^16*boundaryImVBlock76_0_16 h) + (((9-r*h^2)^17*boundaryImVBlock76_0_17 h) + ((9-r*h^2)^18*boundaryImVBlock76_0_18 h))))))

theorem boundaryImClockBlock76_0_eq (h r : ℂ) : boundaryImVSumBlock76_0 h r=boundaryImClockBlock76_0 h r := by

  dsimp only [boundaryImVSumBlock76_0,boundaryImClockBlock76_0,boundaryImVBlock76_0_0,boundaryImVBlock76_0_1,boundaryImVBlock76_0_2,boundaryImVBlock76_0_3,boundaryImVBlock76_0_4,boundaryImVBlock76_0_5,boundaryImVBlock76_0_6,boundaryImVBlock76_0_7,boundaryImVBlock76_0_8,boundaryImVBlock76_0_9,boundaryImVBlock76_0_10,boundaryImVBlock76_0_11,boundaryImVBlock76_0_12,boundaryImVBlock76_0_13,boundaryImVBlock76_0_14,boundaryImVBlock76_0_15,boundaryImVBlock76_0_16,boundaryImVBlock76_0_17,boundaryImVBlock76_0_18,boundaryImClock76_0,boundaryImClock76_1,boundaryImClock76_2,boundaryImClock76_3,boundaryImClock76_4,boundaryImClock76_5,boundaryImClock76_6,boundaryImClock76_7]

  simp only [mul_add,mul_zero,zero_add,add_zero,pow_zero,pow_one,one_mul]

  ac_rfl


def boundaryImClockBlock76_1 (h r : ℂ) : ℂ :=
  ((((h^(21-8:ℕ)*boundaryImClock76_8 (r*h^2)) + (h^(21-9:ℕ)*boundaryImClock76_9 (r*h^2))) + ((h^(21-10:ℕ)*boundaryImClock76_10 (r*h^2)) + (h^(21-11:ℕ)*boundaryImClock76_11 (r*h^2)))) + (((h^(21-12:ℕ)*boundaryImClock76_12 (r*h^2)) + (h^(21-13:ℕ)*boundaryImClock76_13 (r*h^2))) + ((h^(21-14:ℕ)*boundaryImClock76_14 (r*h^2)) + (h^(21-15:ℕ)*boundaryImClock76_15 (r*h^2)))))

def boundaryImVSumBlock76_1 (h r : ℂ) : ℂ :=
  ((((((9-r*h^2)^0*boundaryImVBlock76_1_0 h) + ((9-r*h^2)^1*boundaryImVBlock76_1_1 h)) + (((9-r*h^2)^2*boundaryImVBlock76_1_2 h) + ((9-r*h^2)^3*boundaryImVBlock76_1_3 h))) + ((((9-r*h^2)^4*boundaryImVBlock76_1_4 h) + ((9-r*h^2)^5*boundaryImVBlock76_1_5 h)) + (((9-r*h^2)^6*boundaryImVBlock76_1_6 h) + (((9-r*h^2)^7*boundaryImVBlock76_1_7 h) + ((9-r*h^2)^8*boundaryImVBlock76_1_8 h))))) + (((((9-r*h^2)^9*boundaryImVBlock76_1_9 h) + ((9-r*h^2)^10*boundaryImVBlock76_1_10 h)) + (((9-r*h^2)^11*boundaryImVBlock76_1_11 h) + (((9-r*h^2)^12*boundaryImVBlock76_1_12 h) + ((9-r*h^2)^13*boundaryImVBlock76_1_13 h)))) + ((((9-r*h^2)^14*boundaryImVBlock76_1_14 h) + ((9-r*h^2)^15*boundaryImVBlock76_1_15 h)) + (((9-r*h^2)^16*boundaryImVBlock76_1_16 h) + (((9-r*h^2)^17*boundaryImVBlock76_1_17 h) + ((9-r*h^2)^18*boundaryImVBlock76_1_18 h))))))

theorem boundaryImClockBlock76_1_eq (h r : ℂ) : boundaryImVSumBlock76_1 h r=boundaryImClockBlock76_1 h r := by

  dsimp only [boundaryImVSumBlock76_1,boundaryImClockBlock76_1,boundaryImVBlock76_1_0,boundaryImVBlock76_1_1,boundaryImVBlock76_1_2,boundaryImVBlock76_1_3,boundaryImVBlock76_1_4,boundaryImVBlock76_1_5,boundaryImVBlock76_1_6,boundaryImVBlock76_1_7,boundaryImVBlock76_1_8,boundaryImVBlock76_1_9,boundaryImVBlock76_1_10,boundaryImVBlock76_1_11,boundaryImVBlock76_1_12,boundaryImVBlock76_1_13,boundaryImVBlock76_1_14,boundaryImVBlock76_1_15,boundaryImVBlock76_1_16,boundaryImVBlock76_1_17,boundaryImVBlock76_1_18,boundaryImClock76_8,boundaryImClock76_9,boundaryImClock76_10,boundaryImClock76_11,boundaryImClock76_12,boundaryImClock76_13,boundaryImClock76_14,boundaryImClock76_15]

  simp only [mul_add,mul_zero,zero_add,add_zero,pow_zero,pow_one,one_mul]

  ac_rfl


def boundaryImClockBlock76_2 (h r : ℂ) : ℂ :=
  (((h^(21-16:ℕ)*boundaryImClock76_16 (r*h^2)) + ((h^(21-17:ℕ)*boundaryImClock76_17 (r*h^2)) + (h^(21-18:ℕ)*boundaryImClock76_18 (r*h^2)))) + ((h^(21-19:ℕ)*boundaryImClock76_19 (r*h^2)) + ((h^(21-20:ℕ)*boundaryImClock76_20 (r*h^2)) + (h^(21-21:ℕ)*boundaryImClock76_21 (r*h^2)))))

def boundaryImVSumBlock76_2 (h r : ℂ) : ℂ :=
  ((((((9-r*h^2)^0*boundaryImVBlock76_2_0 h) + ((9-r*h^2)^1*boundaryImVBlock76_2_1 h)) + (((9-r*h^2)^2*boundaryImVBlock76_2_2 h) + ((9-r*h^2)^3*boundaryImVBlock76_2_3 h))) + ((((9-r*h^2)^4*boundaryImVBlock76_2_4 h) + ((9-r*h^2)^5*boundaryImVBlock76_2_5 h)) + (((9-r*h^2)^6*boundaryImVBlock76_2_6 h) + (((9-r*h^2)^7*boundaryImVBlock76_2_7 h) + ((9-r*h^2)^8*boundaryImVBlock76_2_8 h))))) + (((((9-r*h^2)^9*boundaryImVBlock76_2_9 h) + ((9-r*h^2)^10*boundaryImVBlock76_2_10 h)) + (((9-r*h^2)^11*boundaryImVBlock76_2_11 h) + (((9-r*h^2)^12*boundaryImVBlock76_2_12 h) + ((9-r*h^2)^13*boundaryImVBlock76_2_13 h)))) + ((((9-r*h^2)^14*boundaryImVBlock76_2_14 h) + ((9-r*h^2)^15*boundaryImVBlock76_2_15 h)) + (((9-r*h^2)^16*boundaryImVBlock76_2_16 h) + (((9-r*h^2)^17*boundaryImVBlock76_2_17 h) + ((9-r*h^2)^18*boundaryImVBlock76_2_18 h))))))

theorem boundaryImClockBlock76_2_eq (h r : ℂ) : boundaryImVSumBlock76_2 h r=boundaryImClockBlock76_2 h r := by

  dsimp only [boundaryImVSumBlock76_2,boundaryImClockBlock76_2,boundaryImVBlock76_2_0,boundaryImVBlock76_2_1,boundaryImVBlock76_2_2,boundaryImVBlock76_2_3,boundaryImVBlock76_2_4,boundaryImVBlock76_2_5,boundaryImVBlock76_2_6,boundaryImVBlock76_2_7,boundaryImVBlock76_2_8,boundaryImVBlock76_2_9,boundaryImVBlock76_2_10,boundaryImVBlock76_2_11,boundaryImVBlock76_2_12,boundaryImVBlock76_2_13,boundaryImVBlock76_2_14,boundaryImVBlock76_2_15,boundaryImVBlock76_2_16,boundaryImVBlock76_2_17,boundaryImVBlock76_2_18,boundaryImClock76_16,boundaryImClock76_17,boundaryImClock76_18,boundaryImClock76_19,boundaryImClock76_20,boundaryImClock76_21]

  simp only [mul_add,mul_zero,zero_add,add_zero,pow_zero,pow_one,one_mul]

  ac_rfl


def boundaryImClockSum76 (h r : ℂ) : ℂ :=
  ((boundaryImClockBlock76_0 h r) + ((boundaryImClockBlock76_1 h r) + (boundaryImClockBlock76_2 h r)))

theorem boundaryImClockSum76_eq (h r : ℂ) :

    boundaryCompactB75 h r=boundaryImClockSum76 h r := by

  have he : boundaryCompactB75 h r=((boundaryImVSumBlock76_0 h r) + ((boundaryImVSumBlock76_1 h r) + (boundaryImVSumBlock76_2 h r))) := by

    dsimp only [boundaryCompactB75,boundaryImVSumBlock76_0,boundaryImVSumBlock76_1,boundaryImVSumBlock76_2]

    rw [boundaryCompactImVC75_0_blocks76,boundaryCompactImVC75_1_blocks76,boundaryCompactImVC75_2_blocks76,boundaryCompactImVC75_3_blocks76,boundaryCompactImVC75_4_blocks76,boundaryCompactImVC75_5_blocks76,boundaryCompactImVC75_6_blocks76,boundaryCompactImVC75_7_blocks76,boundaryCompactImVC75_8_blocks76,boundaryCompactImVC75_9_blocks76,boundaryCompactImVC75_10_blocks76,boundaryCompactImVC75_11_blocks76,boundaryCompactImVC75_12_blocks76,boundaryCompactImVC75_13_blocks76,boundaryCompactImVC75_14_blocks76,boundaryCompactImVC75_15_blocks76,boundaryCompactImVC75_16_blocks76,boundaryCompactImVC75_17_blocks76,boundaryCompactImVC75_18_blocks76]

    have h1 : (Nat.rawCast 1 : ℕ)=1 := rfl

    simp only [h1,mul_add,pow_zero,pow_one,one_mul]

    ac_rfl

  rw [he]

  simp only [boundaryImClockBlock76_0_eq,boundaryImClockBlock76_1_eq,boundaryImClockBlock76_2_eq,boundaryImClockSum76]


end

end HTGeometry.ThetaRatioInfinity
