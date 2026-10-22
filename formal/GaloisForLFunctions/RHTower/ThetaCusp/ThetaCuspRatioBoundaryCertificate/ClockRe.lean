import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CompactAssembly




namespace HTGeometry.ThetaRatioInfinity

noncomputable section

def boundaryReClock76_0 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(NNRat.rawCast 2573973995 2902376448)) + (((9-d)^0*(0)) + ((9-d)^1*(Rat.rawCast (Int.negOfNat 17292029129) 52242776064)))) + ((((9-d)^1*(0)) + ((9-d)^2*(NNRat.rawCast 20219441971579 33853318889472))) + (((9-d)^2*(0)) + ((9-d)^3*(Rat.rawCast (Int.negOfNat 18738851201825) 101559956668416))))) + ((((9-d)^3*(0)) + (((9-d)^4*(NNRat.rawCast 2130476228443 1218719480020992)) + ((9-d)^4*(0)))) + ((((9-d)^5*(NNRat.rawCast 156940142708137 24679069470425088)) + ((9-d)^5*(0))) + (((9-d)^6*(Rat.rawCast (Int.negOfNat 481627174061185) 444223250467651584)) + ((9-d)^6*(0)))))) + (((((9-d)^7*(NNRat.rawCast 81230749376785 999502313552216064)) + (((9-d)^7*(0)) + ((9-d)^8*(Rat.rawCast (Int.negOfNat 215184678307973) 71964166575759556608)))) + ((((9-d)^8*(0)) + ((9-d)^9*(NNRat.rawCast 3583883340325 80959687397729501184))) + (((9-d)^9*(0)) + ((9-d)^10*(0))))) + (((((9-d)^11*(0)) + ((9-d)^12*(0))) + (((9-d)^13*(0)) + ((9-d)^14*(0)))) + ((((9-d)^15*(0)) + ((9-d)^16*(0))) + (((9-d)^17*(0)) + ((9-d)^18*(0)))))))

def boundaryReClock76_0Norm (d : ℂ) : {c : ℂ // boundaryReClock76_0 d=c} := by

  have he : boundaryReClock76_0 d=boundaryReClock76_0 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_0]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_1 (d : ℂ) : ℂ :=
  (((((9-d)^0*(1 * NNRat.rawCast 338900672335 17414258688)) + ((9-d)^1*(1 * NNRat.rawCast 24955595685487 3761479876608))) + (((9-d)^2*(1 * NNRat.rawCast 46128252912581 22568879259648)) + (((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 90256708004023) 38084983750656)) + ((9-d)^4*(1 * NNRat.rawCast 2165935878964505 3656158440062976))))) + ((((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 5150579091074147) 65810851921133568)) + (((9-d)^6*(1 * NNRat.rawCast 557906639413369 98716277881700352)) + ((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 496737052078147) 7996018508417728512)))) + (((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 1724993331041965) 71964166575759556608)) + (((9-d)^9*(1 * NNRat.rawCast 2230642890041647 1295354998363672018944)) + ((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 219554668799417) 5829097492636524085248))))))

def boundaryReClock76_1Norm (d : ℂ) : {c : ℂ // boundaryReClock76_1 d=c} := by

  have he : boundaryReClock76_1 d=boundaryReClock76_1 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_1]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_2 (d : ℂ) : ℂ :=
  (((((9-d)^0*(1 * NNRat.rawCast 55724743567 429981696)) + (((9-d)^1*(1 * NNRat.rawCast 839106961710943 5015306502144)) + ((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 49683018421054853) 722204136308736)))) + (((9-d)^3*(1 * NNRat.rawCast 17324976025536443 2166612408926208)) + (((9-d)^4*(1 * NNRat.rawCast 137173779309851905 350991210246045696)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 808397167512059009) 3158920892214411264))))) + ((((9-d)^6*(1 * NNRat.rawCast 1219387355802268729 28430288029929701376)) + (((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 1195112806016720977) 255872592269367312384)) + ((9-d)^8*(1 * NNRat.rawCast 269967154765347329 767617776808101937152)))) + (((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 310204600881843443) 20725679973818752303104)) + (((9-d)^10*(1 * NNRat.rawCast 12130058470804363 62177039921456256909312)) + ((9-d)^11*(1 * NNRat.rawCast 2092690629306389 559593359293106312183808))))))

def boundaryReClock76_2Norm (d : ℂ) : {c : ℂ // boundaryReClock76_2 d=c} := by

  have he : boundaryReClock76_2 d=boundaryReClock76_2 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_2]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_3 (d : ℂ) : ℂ :=
  (((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 4706340498913) 61917364224)) + (((9-d)^1*(1 * NNRat.rawCast 45036002279140661 40122452017152)) + ((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 8293584138003209) 16926659444736)))) + (((9-d)^3*(1 * NNRat.rawCast 2314620102503007505 19499511680335872)) + (((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 845862351893666249) 38999023360671744)) + ((9-d)^5*(1 * NNRat.rawCast 73965071280821056117 25271367137715290112))))) + ((((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 58122293236334202227) 227442304239437611008)) + (((9-d)^7*(1 * NNRat.rawCast 24762701480477393177 2046980738154938499072)) + ((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 1162115703515777765) 6140942214464815497216)))) + ((((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 549139232604042251) 55268479930183339474944)) + ((9-d)^10*(1 * NNRat.rawCast 1568068473089652007 1492248958114950165823488))) + (((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 195696744640400479) 4476746874344850497470464)) + ((9-d)^12*(1 * NNRat.rawCast 13750076961227201 40290721869103654477234176))))))

def boundaryReClock76_3Norm (d : ℂ) : {c : ℂ // boundaryReClock76_3 d=c} := by

  have he : boundaryReClock76_3 d=boundaryReClock76_3 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_3]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_4 (d : ℂ) : ℂ :=
  (((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 197405054102927) 41278242816)) + (((9-d)^1*(1 * NNRat.rawCast 5151597573795289 1981355655168)) + ((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 222036889921946309) 1925877696823296)))) + ((((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 54745614365774773109) 623984373770747904)) + ((9-d)^4*(1 * NNRat.rawCast 846538065240488697023 44926874911493849088))) + (((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 85126829364201859813) 67390312367240773632)) + ((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 231315239670513525181) 909769216957750444032))))) + ((((9-d)^7*(1 * NNRat.rawCast 313842574109956854443 4093961476309876998144)) + (((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 1217569843162022658095) 147382613147155571933184)) + ((9-d)^9*(1 * NNRat.rawCast 89306678582029681073 221073919720733357899776)))) + ((((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 47621265901752686737) 5968995832459800663293952)) + ((9-d)^11*(1 * NNRat.rawCast 463758260460286567 6715120311517275746205696))) + (((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 2272675605429860617) 1933954649716975414907240448)) + ((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 293575300609695167) 8702795923726389367082582016))))))

def boundaryReClock76_4Norm (d : ℂ) : {c : ℂ // boundaryReClock76_4 d=c} := by

  have he : boundaryReClock76_4 d=boundaryReClock76_4 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_4]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_5 (d : ℂ) : ℂ :=
  (((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 623312575473853) 27518828544)) + (((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 30067988072344235) 17832200896512)) + ((9-d)^2*(1 * NNRat.rawCast 29074569920658936547 5777633090469888)))) + ((((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 3882748207687346909285) 2495937495082991616)) + ((9-d)^4*(1 * NNRat.rawCast 6216584612660265947341 22463437455746924544))) + (((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 57376351664537434940435) 1617367496813778567168)) + ((9-d)^6*(1 * NNRat.rawCast 51430836067057328897645 14556307471324007104512))))) + (((((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 1129103945050697019451) 3639076867831001776128)) + ((9-d)^8*(1 * NNRat.rawCast 2287292812882742527355 98255075431437047955456))) + (((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 5160698425928265416837) 5305774073297600589594624)) + ((9-d)^10*(1 * NNRat.rawCast 30307738044516609971 47751966659678405306351616)))) + ((((9-d)^11*(1 * NNRat.rawCast 197027590222479495187 214883849968552823878582272)) + ((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 5039774240878068055) 644651549905658471635746816))) + (((9-d)^13*(1 * NNRat.rawCast 8348206677096029765 69622367389811114936660656128)) + ((9-d)^14*(1 * NNRat.rawCast 405506432602597781 626601306508300034429945905152))))))

def boundaryReClock76_5Norm (d : ℂ) : {c : ℂ // boundaryReClock76_5 d=c} := by

  have he : boundaryReClock76_5 d=boundaryReClock76_5 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_5]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_6 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 367564930306885) 9172942848)) + ((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 67265735545439009) 3962711310336))) + (((9-d)^2*(1 * NNRat.rawCast 38936215187601031349 7703510787293184)) + ((9-d)^3*(1 * NNRat.rawCast 229055935164392221813 207994791256915968)))) + ((((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 1980495601564716868033) 3743906242624487424)) + ((9-d)^5*(1 * NNRat.rawCast 125224662746615173518425 1617367496813778567168))) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 281761075635426891451) 75814101413145870336)) + ((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 13807642091898483940871) 43668922413972021313536))))) + (((((9-d)^8*(1 * NNRat.rawCast 441846406193946970051 9211413321697223245824)) + ((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 12371300642096435429515) 5305774073297600589594624))) + (((9-d)^10*(1 * NNRat.rawCast 137718802375168940327 1492248958114950165823488)) + ((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 1686110171985694647533) 429767699937105647757164544)))) + ((((9-d)^12*(1 * NNRat.rawCast 18566124275462682571 483488662429243853726810112)) + ((9-d)^13*(1 * NNRat.rawCast 44936924283632287949 69622367389811114936660656128))) + (((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 21101830690497529) 19581290828384376075935809536)) + ((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 18285856292474113) 5639411758574700309869513146368))))))

def boundaryReClock76_6Norm (d : ℂ) : {c : ℂ // boundaryReClock76_6 d=c} := by

  have he : boundaryReClock76_6 d=boundaryReClock76_6 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_6]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_7 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * NNRat.rawCast 2408369381717 2038431744)) + ((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 3780203172032099) 146767085568))) + (((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 23134312829944287313) 1283918464548864)) + ((9-d)^3*(1 * NNRat.rawCast 14510317869674037298997 1663958330055327744)))) + ((((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 15618423417637542795461) 11231718727873462272)) + ((9-d)^5*(1 * NNRat.rawCast 206472121072036806729509 1617367496813778567168))) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 233698320193774483288829) 14556307471324007104512)) + ((9-d)^7*(1 * NNRat.rawCast 185742948129001140193165 65503383620958031970304))))) + (((((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 87804898030082716376593) 294765226294311143866368)) + ((9-d)^9*(1 * NNRat.rawCast 73277382533984112347327 5305774073297600589594624))) + (((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 8226262614482804328827) 47751966659678405306351616)) + ((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 274850889402850673191) 214883849968552823878582272)))) + ((((9-d)^12*(1 * NNRat.rawCast 26776111773646803391 1933954649716975414907240448)) + ((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 231947510939720780939) 69622367389811114936660656128))) + (((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 8209422637318359989) 626601306508300034429945905152)) + (((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 1511966328663049) 2819705879287350154934756573184)) + ((9-d)^16*(1 * NNRat.rawCast 168937493305 49565142409347951942212517888)))))))

def boundaryReClock76_7Norm (d : ℂ) : {c : ℂ // boundaryReClock76_7 d=c} := by

  have he : boundaryReClock76_7 d=boundaryReClock76_7 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_7]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_8 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * NNRat.rawCast 840943075781335 8153726976)) + ((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 2739206985380101) 330225942528))) + (((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 3283120390260343081) 213986410758144)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 121585713866489571841) 15407021574586368)))) + ((((9-d)^4*(1 * NNRat.rawCast 120991256636412595293395 29951249940995899392)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 1016063989492284869895919) 1617367496813778567168))) + (((9-d)^6*(1 * NNRat.rawCast 107343733308333326334655 2426051245220667850752)) + (((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 287923889288486821105085) 131006767241916063940608)) + ((9-d)^8*(1 * NNRat.rawCast 22179299769693391051463 98255075431437047955456)))))) + (((((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 71932924127465264777429) 5305774073297600589594624)) + ((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 2194088939615026270777) 7958661109946400884391936))) + (((9-d)^11*(1 * NNRat.rawCast 15663352326677126150243 429767699937105647757164544)) + ((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 1304097701503479099571) 3867909299433950829814480896)))) + ((((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 24492496571545759715) 69622367389811114936660656128)) + ((9-d)^14*(1 * NNRat.rawCast 11310413425473433145 313300653254150017214972952576))) + (((9-d)^15*(1 * NNRat.rawCast 339871085508091991 5639411758574700309869513146368)) + (((9-d)^16*(1 * NNRat.rawCast 8265944738779 1586084557099134462150800572416)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 14325530485) 114198088111137681274857641213952)))))))

def boundaryReClock76_8Norm (d : ℂ) : {c : ℂ // boundaryReClock76_8 d=c} := by

  have he : boundaryReClock76_8 d=boundaryReClock76_8 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_8]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_9 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * NNRat.rawCast 67201316424679 452984832)) + ((9-d)^1*(1 * NNRat.rawCast 14148525842108561 440301256704))) + (((9-d)^2*(1 * NNRat.rawCast 2577054043646679577 95105071448064)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 3896779907004063833143) 184884258895036416)))) + ((((9-d)^4*(1 * NNRat.rawCast 62358839466823347069269 29951249940995899392)) + ((9-d)^5*(1 * NNRat.rawCast 26788283590402750610645 134780624734481547264))) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 10544893741401536648471) 2426051245220667850752)) + (((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 93342218685735778372457) 10917230603493005328384)) + ((9-d)^8*(1 * NNRat.rawCast 301421433559311819865325 294765226294311143866368)))))) + (((((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 3412479099071539444645) 82902719895275009212416)) + ((9-d)^10*(1 * NNRat.rawCast 28720732444219307679151 23875983329839202653175808))) + (((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 530562256287476278741) 7958661109946400884391936)) + ((9-d)^12*(1 * NNRat.rawCast 2120623462217466563867 3867909299433950829814480896)))) + ((((9-d)^13*(1 * NNRat.rawCast 445549157507532871811 17405591847452778734165164032)) + ((9-d)^14*(1 * NNRat.rawCast 17353859589311349559 313300653254150017214972952576))) + (((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 33453624729784819) 469950979881225025822459428864)) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 342464455864405) 6344338228396537848603202289664)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 2426981221) 57099044055568840637428820606976)))))))

def boundaryReClock76_9Norm (d : ℂ) : {c : ℂ // boundaryReClock76_9 d=c} := by

  have he : boundaryReClock76_9 d=boundaryReClock76_9 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_9]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_10 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * NNRat.rawCast 128399801008549 905969664)) + ((9-d)^1*(1 * NNRat.rawCast 3591841198761031 48922361856))) + (((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 43031725233047023) 47552535724032)) + ((9-d)^3*(1 * NNRat.rawCast 195124945227342650339 7703510787293184)))) + ((((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 20611009260936251150755) 1663958330055327744)) + ((9-d)^5*(1 * NNRat.rawCast 32479145122147016955665 16847578091810193408))) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 145741444199649128321281) 909769216957750444032)) + (((9-d)^7*(1 * NNRat.rawCast 304167568125043871031755 16375845905239507992576)) + ((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 331499366305689418554149) 147382613147155571933184)))))) + (((((9-d)^9*(1 * NNRat.rawCast 101473495072202368216489 884295678882933431599104)) + ((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 173821314463967610587) 221073919720733357899776))) + (((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 284809855741897658651) 8953493748689700994940928)) + ((9-d)^12*(1 * NNRat.rawCast 78606866482981670647 214883849968552823878582272)))) + ((((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 137281532535594258137) 2900931974575463122360860672)) + ((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 14810488993092655) 45327062102741611286888448))) + (((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 81733900791335149) 234975489940612512911229714432)) + (((9-d)^16*(1 * NNRat.rawCast 855060108259 1057389704732756308100533714944)) + ((9-d)^17*(1 * NNRat.rawCast 26945503417 38066029370379227091619213737984)))))))

def boundaryReClock76_10Norm (d : ℂ) : {c : ℂ // boundaryReClock76_10 d=c} := by

  have he : boundaryReClock76_10 d=boundaryReClock76_10 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_10]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_11 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * NNRat.rawCast 10267109560423 50331648)) + ((9-d)^1*(1 * NNRat.rawCast 751753536487855 8153726976))) + (((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 517796061788995) 16307453952)) + ((9-d)^3*(1 * NNRat.rawCast 33783576514210273303 1711891286065152)))) + ((((9-d)^4*(1 * NNRat.rawCast 710644361937096360637 277326388342554624)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 44884578798858997377449) 22463437455746924544))) + (((9-d)^6*(1 * NNRat.rawCast 217283734849662393760351 909769216957750444032)) + (((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 158415410897264082940625) 16375845905239507992576)) + ((9-d)^8*(1 * NNRat.rawCast 113344674946822636143241 147382613147155571933184)))))) + (((((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 21420596387907027650563) 331610879581100036849664)) + ((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 7364025302116830422221) 2984497916229900331646976))) + (((9-d)^11*(1 * NNRat.rawCast 2431146124146807267779 8953493748689700994940928)) + ((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 618220385259497250371) 322325774952829235817873408)))) + ((((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 23136298541254051547) 2900931974575463122360860672)) + ((9-d)^14*(1 * NNRat.rawCast 4516372364942935217 13054193885589584050623873024))) + (((9-d)^15*(1 * NNRat.rawCast 74320809587825143 78325163313537504303743238144)) + (((9-d)^16*(1 * NNRat.rawCast 78978986476313 234975489940612512911229714432)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 7534594907) 1057389704732756308100533714944)))))))

def boundaryReClock76_11Norm (d : ℂ) : {c : ℂ // boundaryReClock76_11 d=c} := by

  have he : boundaryReClock76_11 d=boundaryReClock76_11 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_11]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_12 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * NNRat.rawCast 4688785053799 25165824)) + ((9-d)^1*(1 * NNRat.rawCast 1786487770662925 16307453952))) + (((9-d)^2*(1 * NNRat.rawCast 29569024117770637 587068342272)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 7361057213124629149) 142657607172096)))) + ((((9-d)^4*(1 * NNRat.rawCast 315172826303921751737 15407021574586368)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 33163026330405157318661) 11231718727873462272))) + (((9-d)^6*(1 * NNRat.rawCast 57682450310238252761467 303256405652583481344)) + (((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 148836131214605550856559) 8187922952619753996288)) + ((9-d)^8*(1 * NNRat.rawCast 34705095933069585653809 18422826643394446491648)))))) + (((((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 23017327816305596756789) 331610879581100036849664)) + ((9-d)^10*(1 * NNRat.rawCast 15913194802104545222659 2984497916229900331646976))) + (((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 12096348797041315544957) 26860481246069102984822784)) + ((9-d)^12*(1 * NNRat.rawCast 1046849667960175476809 483488662429243853726810112)))) + ((((9-d)^13*(1 * NNRat.rawCast 228223513353820054213 1450465987287731561180430336)) + ((9-d)^14*(1 * NNRat.rawCast 6578963650269116407 13054193885589584050623873024))) + (((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 2806193702380529) 13054193885589584050623873024)) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 28241139865477) 58743872485153128227807428608)) + ((9-d)^17*(1 * NNRat.rawCast 758012507 132173713091594538512566714368)))))))

def boundaryReClock76_12Norm (d : ℂ) : {c : ℂ // boundaryReClock76_12 d=c} := by

  have he : boundaryReClock76_12 d=boundaryReClock76_12 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_12]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_13 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * NNRat.rawCast 1065954322969 8388608)) + ((9-d)^1*(1 * NNRat.rawCast 22204205508317 603979776))) + (((9-d)^2*(1 * NNRat.rawCast 7015422420796223 293534171136)) + ((9-d)^3*(1 * NNRat.rawCast 283551782499224893 7925422620672)))) + ((((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 150637807624708758265) 5777633090469888)) + ((9-d)^5*(1 * NNRat.rawCast 13698989235951035150963 1871953121312243712))) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 35273132611297615146547) 37907050706572935168)) + (((9-d)^7*(1 * NNRat.rawCast 39768630018302239350229 682326912718312833024)) + ((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 16606306217037983949313) 9211413321697223245824)))))) + (((((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 8469310340657753919685) 331610879581100036849664)) + ((9-d)^10*(1 * NNRat.rawCast 388050210858173238445 746124479057475082911744))) + (((9-d)^11*(1 * NNRat.rawCast 31145032053012378161 69949169911638289022976)) + ((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 71698112184124150135) 20145360934551827238617088)))) + ((((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 694079110520357887337) 2175698980931597341770645504)) + ((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 1061782103192386915) 543924745232899335442661376))) + (((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 912627572016575) 362616496821932890295107584)) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 1566533457391) 4895322707096094018983952384)) + ((9-d)^17*(1 * NNRat.rawCast 11700680453 176231617455459384683422285824)))))))

def boundaryReClock76_13Norm (d : ℂ) : {c : ℂ // boundaryReClock76_13 d=c} := by

  have he : boundaryReClock76_13 d=boundaryReClock76_13 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_13]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_14 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * NNRat.rawCast 330759446817 8388608)) + ((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 204813782125) 452984832))) + (((9-d)^2*(1 * NNRat.rawCast 2191897219508795 146767085568)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 37311574969886143) 3962711310336)))) + ((((9-d)^4*(1 * NNRat.rawCast 30631781454315436439 1925877696823296)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 171062954862404659955) 25999348907114496))) + (((9-d)^6*(1 * NNRat.rawCast 4980749091225040376033 4211894522952548352)) + (((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 4981256759504263998289) 56860576059859402752)) + ((9-d)^8*(1 * NNRat.rawCast 1545855966180359988673 9211413321697223245824)))))) + (((((9-d)^9*(1 * NNRat.rawCast 30434543818219388941837 82902719895275009212416)) + ((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 1625256668537592527107) 93265559882184385363968))) + (((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 991483469309568904681) 3357560155758637873102848)) + ((9-d)^12*(1 * NNRat.rawCast 228960159330259212487 20145360934551827238617088)))) + ((((9-d)^13*(1 * NNRat.rawCast 6074204053222347575 15109020700913870428962816)) + ((9-d)^14*(1 * NNRat.rawCast 56585322924564629 20145360934551827238617088))) + (((9-d)^15*(1 * NNRat.rawCast 153363552041435 30218041401827740857925632)) + (((9-d)^16*(1 * NNRat.rawCast 103476255715 60436082803655481715851264)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 72277303) 543924745232899335442661376)))))))

def boundaryReClock76_14Norm (d : ℂ) : {c : ℂ // boundaryReClock76_14 d=c} := by

  have he : boundaryReClock76_14 d=boundaryReClock76_14 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_14]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_15 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 14668844751) 4194304)) + ((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 250681695941) 25165824))) + (((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 195638259582067) 24461180928)) + ((9-d)^3*(1 * NNRat.rawCast 5908005846099869 660451885056)))) + ((((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 253988364770939839) 35664401793024)) + ((9-d)^5*(1 * NNRat.rawCast 49885731574910801809 12999674453557248))) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 917648299010004047923) 1052973630738137088)) + (((9-d)^7*(1 * NNRat.rawCast 4515688081356966679595 56860576059859402752)) + ((9-d)^8*(1 * NNRat.rawCast 180593255494178709653 383808888404050968576)))))) + (((((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 5871337127094591358921) 10362839986909376151552)) + ((9-d)^10*(1 * NNRat.rawCast 5922961490081569048043 186531119764368770727936))) + (((9-d)^11*(1 * NNRat.rawCast 44743664677374445597 839390038939659468275712)) + ((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 71472793920992688065) 3357560155758637873102848)))) + ((((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 1835568962721740285) 5036340233637956809654272)) + ((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 11858614216838335) 5036340233637956809654272))) + (((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 50511907346555) 10072680467275913619308544)) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 119579308637) 45327062102741611286888448)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 18989215) 203971779462337250790998016)))))))

def boundaryReClock76_15Norm (d : ℂ) : {c : ℂ // boundaryReClock76_15 d=c} := by

  have he : boundaryReClock76_15 d=boundaryReClock76_15 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_15]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_16 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 25694689023) 4194304)) + ((9-d)^1*(1 * Rat.rawCast (Int.negOfNat 8454111609) 4194304))) + (((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 28226486170435) 4076863488)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 496866136571689) 330225942528)))) + ((((9-d)^4*(1 * NNRat.rawCast 39631726330443853 13374150672384)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 190590726744196973) 106993205379072))) + (((9-d)^6*(1 * NNRat.rawCast 171166027756488223399 350991210246045696)) + (((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 2906552668529720416055) 56860576059859402752)) + ((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 360790148552129508947) 767617776808101937152)))))) + (((((9-d)^9*(1 * NNRat.rawCast 3353900685787599339853 6908559991272917434368)) + ((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 721749056167545670429) 23316389970546096340992))) + (((9-d)^11*(1 * NNRat.rawCast 75898718405562616109 559593359293106312183808)) + ((9-d)^12*(1 * NNRat.rawCast 6468702351852070967 279796679646553156091904)))) + ((((9-d)^13*(1 * NNRat.rawCast 29034035389673845 124354079842912513818624)) + ((9-d)^14*(1 * NNRat.rawCast 1882041096446303 1678780077879318936551424))) + (((9-d)^15*(1 * NNRat.rawCast 9321260092597 3357560155758637873102848)) + (((9-d)^16*(1 * NNRat.rawCast 38588663779 15109020700913870428962816)) + ((9-d)^17*(1 * NNRat.rawCast 4489513 8498824144264052116291584)))))))

def boundaryReClock76_16Norm (d : ℂ) : {c : ℂ // boundaryReClock76_16 d=c} := by

  have he : boundaryReClock76_16 d=boundaryReClock76_16 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_16]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_17 (d : ℂ) : ℂ :=
  ((((((9-d)^0*(1 * Rat.rawCast (Int.negOfNat 2143063575) 2097152)) + ((9-d)^1*(1 * NNRat.rawCast 2340170249 4194304))) + (((9-d)^2*(1 * NNRat.rawCast 330508399625 679477248)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 25252133621603) 12230590464)))) + ((((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 395143561787987) 17832200896512)) + ((9-d)^5*(1 * NNRat.rawCast 33494889062154179 60183678025728))) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 25098369019341149041) 116997070082015232)) + (((9-d)^7*(1 * NNRat.rawCast 43089469661531776945 1579460446107205632)) + ((9-d)^8*(1 * NNRat.rawCast 222675550817164993 999502313552216064)))))) + (((((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 1027008814990190065373) 3454279995636458717184)) + ((9-d)^10*(1 * NNRat.rawCast 209943755440339635623 10362839986909376151552))) + (((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 5090260560777314953) 31088519960728128454656)) + ((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 3038075452299828817) 186531119764368770727936)))) + ((((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 12953531278545725) 139898339823276578045952)) + ((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 4049378169677) 62177039921456256909312))) + (((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 98888408879) 279796679646553156091904)) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 3402513433) 2518170116818978404827136)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 13254793) 22663531051370805643444224)))))))

def boundaryReClock76_17Norm (d : ℂ) : {c : ℂ // boundaryReClock76_17 d=c} := by

  have he : boundaryReClock76_17 d=boundaryReClock76_17 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_17]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_18 (d : ℂ) : ℂ :=
  ((((((9-d)^1*(1 * NNRat.rawCast 317173155 1048576)) + ((9-d)^2*(1 * NNRat.rawCast 14721710857 37748736))) + (((9-d)^3*(1 * NNRat.rawCast 7601836559675 9172942848)) + ((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 1574506515896309) 2972033482752)))) + ((((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 382742526859747) 30091839012864)) + ((9-d)^6*(1 * NNRat.rawCast 607067186808576749 9749755840167936))) + (((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 2986895310826234465) 263243407684534272)) + ((9-d)^8*(1 * NNRat.rawCast 578136324146852569 10661358011223638016))))) + (((((9-d)^9*(1 * NNRat.rawCast 152159557915890669563 1151426665212152905728)) + ((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 8412143827697953753) 863569998909114679296))) + (((9-d)^11*(1 * NNRat.rawCast 840239744932859063 7772129990182032113664)) + ((9-d)^12*(1 * NNRat.rawCast 241831928414606501 31088519960728128454656)))) + ((((9-d)^13*(1 * NNRat.rawCast 210883010884061 46632779941092192681984)) + ((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 19107514648465) 46632779941092192681984))) + (((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 17206671299) 15544259980364064227328)) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 454484377) 1259085058409489202413568)) + ((9-d)^17*(1 * NNRat.rawCast 3202801 22663531051370805643444224)))))))

def boundaryReClock76_18Norm (d : ℂ) : {c : ℂ // boundaryReClock76_18 d=c} := by

  have he : boundaryReClock76_18 d=boundaryReClock76_18 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_18]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_19 (d : ℂ) : ℂ :=
  ((((((9-d)^2*(1 * Rat.rawCast (Int.negOfNat 295633355) 18874368)) + ((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 261107069759) 3057647616))) + (((9-d)^4*(1 * NNRat.rawCast 99116094182567 495338913792)) + ((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 723720349910629) 13374150672384)))) + ((((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 1615212828003749) 203119913336832)) + ((9-d)^7*(1 * NNRat.rawCast 850454224292735941 263243407684534272))) + (((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 217078033682838691) 2369190669160808448)) + ((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 225651476856301229) 5997013881313296384))))) + (((((9-d)^10*(1 * NNRat.rawCast 1391085708731893169 431784999454557339648)) + ((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 67366298761168637) 1295354998363672018944))) + (((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 11415856074045205) 5181419993454688075776)) + ((9-d)^13*(1 * NNRat.rawCast 390881856585281 15544259980364064227328)))) + ((((9-d)^14*(1 * NNRat.rawCast 831670544725 1943032497545508028416)) + ((9-d)^15*(1 * NNRat.rawCast 64740079991 46632779941092192681984))) + (((9-d)^16*(1 * NNRat.rawCast 527387345 419695019469829734137856)) + ((9-d)^17*(1 * NNRat.rawCast 434041 1888627587614233803620352))))))

def boundaryReClock76_19Norm (d : ℂ) : {c : ℂ // boundaryReClock76_19 d=c} := by

  have he : boundaryReClock76_19 d=boundaryReClock76_19 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_19]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_20 (d : ℂ) : ℂ :=
  (((((9-d)^3*(1 * Rat.rawCast (Int.negOfNat 118427) 331776)) + (((9-d)^4*(1 * Rat.rawCast (Int.negOfNat 3499390120043) 82556485632)) + ((9-d)^5*(1 * NNRat.rawCast 13444892471737 743008370688)))) + ((((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 231393718616249) 541653102231552)) + ((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 7967989674815663) 14624633760251904))) + (((9-d)^8*(1 * NNRat.rawCast 20096918107407283 592297667290202112)) + ((9-d)^9*(1 * NNRat.rawCast 96039540769832831 15992037016835457024))))) + (((((9-d)^10*(1 * Rat.rawCast (Int.negOfNat 27862005220957595) 47976111050506371072)) + ((9-d)^11*(1 * NNRat.rawCast 750761698285889 47976111050506371072))) + (((9-d)^12*(1 * NNRat.rawCast 72967459076987 863569998909114679296)) + ((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 52274983049483) 2590709996727344037888)))) + ((((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 639614828653) 2590709996727344037888)) + ((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 6749363443) 7772129990182032113664))) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 1383029) 1457274373159131021312)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 11819) 52461877433728716767232))))))

def boundaryReClock76_20Norm (d : ℂ) : {c : ℂ // boundaryReClock76_20 d=c} := by

  have he : boundaryReClock76_20 d=boundaryReClock76_20 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_20]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_21 (d : ℂ) : ℂ :=
  (((((9-d)^4*(1 * NNRat.rawCast 1063682155 254803968)) + (((9-d)^5*(1 * Rat.rawCast (Int.negOfNat 830159266759) 371504185344)) + ((9-d)^6*(1 * NNRat.rawCast 1470174938317 7522959753216)))) + ((((9-d)^7*(1 * NNRat.rawCast 51748298396375 1218719480020992)) + ((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 369218454545003) 98716277881700352))) + (((9-d)^9*(1 * Rat.rawCast (Int.negOfNat 2540983306797479) 5330679005611819008)) + ((9-d)^10*(1 * NNRat.rawCast 51618736230307 1999004627104432128))))) + ((((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 62061492234979) 35982083287879778304)) + (((9-d)^12*(1 * NNRat.rawCast 11559301569253 71964166575759556608)) + ((9-d)^13*(1 * NNRat.rawCast 3259747474309 431784999454557339648)))) + ((((9-d)^14*(1 * NNRat.rawCast 26178089645 323838749590918004736)) + ((9-d)^15*(1 * NNRat.rawCast 187667839 647677499181836009472))) + (((9-d)^16*(1 * NNRat.rawCast 1935091 5829097492636524085248)) + ((9-d)^17*(1 * NNRat.rawCast 8669 104923754867457433534464))))))

def boundaryReClock76_21Norm (d : ℂ) : {c : ℂ // boundaryReClock76_21 d=c} := by

  have he : boundaryReClock76_21 d=boundaryReClock76_21 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_21]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReClock76_22 (d : ℂ) : ℂ :=
  (((((9-d)^5*(1 * NNRat.rawCast 237639341 23219011584)) + (((9-d)^6*(1 * Rat.rawCast (Int.negOfNat 6390601583) 3761479876608)) + ((9-d)^7*(1 * Rat.rawCast (Int.negOfNat 146122178851) 152339935002624)))) + (((9-d)^8*(1 * Rat.rawCast (Int.negOfNat 462236958017) 8226356490141696)) + (((9-d)^9*(1 * NNRat.rawCast 3484089980375 111055812616912896)) + ((9-d)^10*(1 * NNRat.rawCast 4346286687145 999502313552216064))))) + ((((9-d)^11*(1 * Rat.rawCast (Int.negOfNat 278045141603) 1499253470328324096)) + (((9-d)^12*(1 * Rat.rawCast (Int.negOfNat 116284680869) 2998506940656648192)) + ((9-d)^13*(1 * Rat.rawCast (Int.negOfNat 31501017683) 26986562465909833728)))) + ((((9-d)^14*(1 * Rat.rawCast (Int.negOfNat 620897345) 53973124931819667456)) + ((9-d)^15*(1 * Rat.rawCast (Int.negOfNat 121577) 2998506940656648192))) + (((9-d)^16*(1 * Rat.rawCast (Int.negOfNat 22445) 485758124386377007104)) + ((9-d)^17*(1 * Rat.rawCast (Int.negOfNat 25) 2185911559738696531968))))))

def boundaryReClock76_22Norm (d : ℂ) : {c : ℂ // boundaryReClock76_22 d=c} := by

  have he : boundaryReClock76_22 d=boundaryReClock76_22 d := rfl

  conv at he =>

    rhs

    norm_num [boundaryReClock76_22]

    try ring_nf (config := {mode := .raw})

  trace_state

  exact ⟨_,he⟩


def boundaryReVBlock76_0_0 (h : ℂ) : ℂ :=
  ((((h ^ (22-0:ℕ) * (NNRat.rawCast 2573973995 2902376448)) + (h ^ (22-0:ℕ) * (0))) + ((h ^ (22-1:ℕ) * (1 * NNRat.rawCast 338900672335 17414258688)) + (h ^ (22-2:ℕ) * (1 * NNRat.rawCast 55724743567 429981696)))) + (((h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 4706340498913) 61917364224)) + (h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 197405054102927) 41278242816))) + ((h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 623312575473853) 27518828544)) + ((h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 367564930306885) 9172942848)) + (h ^ (22-7:ℕ) * (1 * NNRat.rawCast 2408369381717 2038431744))))))

def boundaryReVBlock76_1_0 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * NNRat.rawCast 840943075781335 8153726976)) + (h ^ (22-9:ℕ) * (1 * NNRat.rawCast 67201316424679 452984832))) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 128399801008549 905969664)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 10267109560423 50331648)))) + (((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 4688785053799 25165824)) + (h ^ (22-13:ℕ) * (1 * NNRat.rawCast 1065954322969 8388608))) + ((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 330759446817 8388608)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 14668844751) 4194304)))))

def boundaryReVBlock76_2_0 (h : ℂ) : ℂ :=
  ((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 25694689023) 4194304)) + (h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2143063575) 2097152)))

theorem boundaryCompactReVC75_0_blocks76 (h : ℂ) :

    boundaryCompactReVC75_0 h=((boundaryReVBlock76_0_0 h) + ((boundaryReVBlock76_1_0 h) + (boundaryReVBlock76_2_0 h))) := by

  dsimp only [boundaryCompactReVC75_0,boundaryReVBlock76_0_0,boundaryReVBlock76_1_0,boundaryReVBlock76_2_0]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_1 (h : ℂ) : ℂ :=
  ((((h ^ (22-0:ℕ) * (Rat.rawCast (Int.negOfNat 17292029129) 52242776064)) + (h ^ (22-0:ℕ) * (0))) + ((h ^ (22-1:ℕ) * (1 * NNRat.rawCast 24955595685487 3761479876608)) + (h ^ (22-2:ℕ) * (1 * NNRat.rawCast 839106961710943 5015306502144)))) + (((h ^ (22-3:ℕ) * (1 * NNRat.rawCast 45036002279140661 40122452017152)) + (h ^ (22-4:ℕ) * (1 * NNRat.rawCast 5151597573795289 1981355655168))) + ((h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 30067988072344235) 17832200896512)) + ((h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 67265735545439009) 3962711310336)) + (h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3780203172032099) 146767085568))))))

def boundaryReVBlock76_1_1 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2739206985380101) 330225942528)) + (h ^ (22-9:ℕ) * (1 * NNRat.rawCast 14148525842108561 440301256704))) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 3591841198761031 48922361856)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 751753536487855 8153726976)))) + (((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 1786487770662925 16307453952)) + (h ^ (22-13:ℕ) * (1 * NNRat.rawCast 22204205508317 603979776))) + ((h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 204813782125) 452984832)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 250681695941) 25165824)))))

def boundaryReVBlock76_2_1 (h : ℂ) : ℂ :=
  ((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8454111609) 4194304)) + ((h ^ (22-17:ℕ) * (1 * NNRat.rawCast 2340170249 4194304)) + (h ^ (22-18:ℕ) * (1 * NNRat.rawCast 317173155 1048576))))

theorem boundaryCompactReVC75_1_blocks76 (h : ℂ) :

    boundaryCompactReVC75_1 h=((boundaryReVBlock76_0_1 h) + ((boundaryReVBlock76_1_1 h) + (boundaryReVBlock76_2_1 h))) := by

  dsimp only [boundaryCompactReVC75_1,boundaryReVBlock76_0_1,boundaryReVBlock76_1_1,boundaryReVBlock76_2_1]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_2 (h : ℂ) : ℂ :=
  ((((h ^ (22-0:ℕ) * (NNRat.rawCast 20219441971579 33853318889472)) + (h ^ (22-0:ℕ) * (0))) + ((h ^ (22-1:ℕ) * (1 * NNRat.rawCast 46128252912581 22568879259648)) + (h ^ (22-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 49683018421054853) 722204136308736)))) + (((h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8293584138003209) 16926659444736)) + (h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 222036889921946309) 1925877696823296))) + ((h ^ (22-5:ℕ) * (1 * NNRat.rawCast 29074569920658936547 5777633090469888)) + ((h ^ (22-6:ℕ) * (1 * NNRat.rawCast 38936215187601031349 7703510787293184)) + (h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 23134312829944287313) 1283918464548864))))))

def boundaryReVBlock76_1_2 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3283120390260343081) 213986410758144)) + (h ^ (22-9:ℕ) * (1 * NNRat.rawCast 2577054043646679577 95105071448064))) + ((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 43031725233047023) 47552535724032)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 517796061788995) 16307453952)))) + (((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 29569024117770637 587068342272)) + (h ^ (22-13:ℕ) * (1 * NNRat.rawCast 7015422420796223 293534171136))) + ((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 2191897219508795 146767085568)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 195638259582067) 24461180928)))))

def boundaryReVBlock76_2_2 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 28226486170435) 4076863488)) + (h ^ (22-17:ℕ) * (1 * NNRat.rawCast 330508399625 679477248))) + ((h ^ (22-18:ℕ) * (1 * NNRat.rawCast 14721710857 37748736)) + (h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 295633355) 18874368))))

theorem boundaryCompactReVC75_2_blocks76 (h : ℂ) :

    boundaryCompactReVC75_2 h=((boundaryReVBlock76_0_2 h) + ((boundaryReVBlock76_1_2 h) + (boundaryReVBlock76_2_2 h))) := by

  dsimp only [boundaryCompactReVC75_2,boundaryReVBlock76_0_2,boundaryReVBlock76_1_2,boundaryReVBlock76_2_2]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_3 (h : ℂ) : ℂ :=
  ((((h ^ (22-0:ℕ) * (Rat.rawCast (Int.negOfNat 18738851201825) 101559956668416)) + (h ^ (22-0:ℕ) * (0))) + ((h ^ (22-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 90256708004023) 38084983750656)) + (h ^ (22-2:ℕ) * (1 * NNRat.rawCast 17324976025536443 2166612408926208)))) + (((h ^ (22-3:ℕ) * (1 * NNRat.rawCast 2314620102503007505 19499511680335872)) + (h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 54745614365774773109) 623984373770747904))) + ((h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3882748207687346909285) 2495937495082991616)) + ((h ^ (22-6:ℕ) * (1 * NNRat.rawCast 229055935164392221813 207994791256915968)) + (h ^ (22-7:ℕ) * (1 * NNRat.rawCast 14510317869674037298997 1663958330055327744))))))

def boundaryReVBlock76_1_3 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 121585713866489571841) 15407021574586368)) + (h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3896779907004063833143) 184884258895036416))) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 195124945227342650339 7703510787293184)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 33783576514210273303 1711891286065152)))) + (((h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 7361057213124629149) 142657607172096)) + (h ^ (22-13:ℕ) * (1 * NNRat.rawCast 283551782499224893 7925422620672))) + ((h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 37311574969886143) 3962711310336)) + (h ^ (22-15:ℕ) * (1 * NNRat.rawCast 5908005846099869 660451885056)))))

def boundaryReVBlock76_2_3 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 496866136571689) 330225942528)) + (h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 25252133621603) 12230590464))) + ((h ^ (22-18:ℕ) * (1 * NNRat.rawCast 7601836559675 9172942848)) + ((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 261107069759) 3057647616)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 118427) 331776)))))

theorem boundaryCompactReVC75_3_blocks76 (h : ℂ) :

    boundaryCompactReVC75_3 h=((boundaryReVBlock76_0_3 h) + ((boundaryReVBlock76_1_3 h) + (boundaryReVBlock76_2_3 h))) := by

  dsimp only [boundaryCompactReVC75_3,boundaryReVBlock76_0_3,boundaryReVBlock76_1_3,boundaryReVBlock76_2_3]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_4 (h : ℂ) : ℂ :=
  ((((h ^ (22-0:ℕ) * (NNRat.rawCast 2130476228443 1218719480020992)) + (h ^ (22-0:ℕ) * (0))) + ((h ^ (22-1:ℕ) * (1 * NNRat.rawCast 2165935878964505 3656158440062976)) + (h ^ (22-2:ℕ) * (1 * NNRat.rawCast 137173779309851905 350991210246045696)))) + (((h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 845862351893666249) 38999023360671744)) + (h ^ (22-4:ℕ) * (1 * NNRat.rawCast 846538065240488697023 44926874911493849088))) + ((h ^ (22-5:ℕ) * (1 * NNRat.rawCast 6216584612660265947341 22463437455746924544)) + ((h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1980495601564716868033) 3743906242624487424)) + (h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15618423417637542795461) 11231718727873462272))))))

def boundaryReVBlock76_1_4 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * NNRat.rawCast 120991256636412595293395 29951249940995899392)) + (h ^ (22-9:ℕ) * (1 * NNRat.rawCast 62358839466823347069269 29951249940995899392))) + ((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 20611009260936251150755) 1663958330055327744)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 710644361937096360637 277326388342554624)))) + (((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 315172826303921751737 15407021574586368)) + (h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 150637807624708758265) 5777633090469888))) + ((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 30631781454315436439 1925877696823296)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 253988364770939839) 35664401793024)))))

def boundaryReVBlock76_2_4 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 39631726330443853 13374150672384)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 395143561787987) 17832200896512)) + (h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1574506515896309) 2972033482752)))) + ((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 99116094182567 495338913792)) + ((h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3499390120043) 82556485632)) + (h ^ (22-21:ℕ) * (1 * NNRat.rawCast 1063682155 254803968)))))

theorem boundaryCompactReVC75_4_blocks76 (h : ℂ) :

    boundaryCompactReVC75_4 h=((boundaryReVBlock76_0_4 h) + ((boundaryReVBlock76_1_4 h) + (boundaryReVBlock76_2_4 h))) := by

  dsimp only [boundaryCompactReVC75_4,boundaryReVBlock76_0_4,boundaryReVBlock76_1_4,boundaryReVBlock76_2_4]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_5 (h : ℂ) : ℂ :=
  ((((h ^ (22-0:ℕ) * (NNRat.rawCast 156940142708137 24679069470425088)) + (h ^ (22-0:ℕ) * (0))) + ((h ^ (22-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5150579091074147) 65810851921133568)) + (h ^ (22-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 808397167512059009) 3158920892214411264)))) + (((h ^ (22-3:ℕ) * (1 * NNRat.rawCast 73965071280821056117 25271367137715290112)) + (h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 85126829364201859813) 67390312367240773632))) + ((h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 57376351664537434940435) 1617367496813778567168)) + ((h ^ (22-6:ℕ) * (1 * NNRat.rawCast 125224662746615173518425 1617367496813778567168)) + (h ^ (22-7:ℕ) * (1 * NNRat.rawCast 206472121072036806729509 1617367496813778567168))))))

def boundaryReVBlock76_1_5 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1016063989492284869895919) 1617367496813778567168)) + (h ^ (22-9:ℕ) * (1 * NNRat.rawCast 26788283590402750610645 134780624734481547264))) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 32479145122147016955665 16847578091810193408)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 44884578798858997377449) 22463437455746924544)))) + (((h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 33163026330405157318661) 11231718727873462272)) + (h ^ (22-13:ℕ) * (1 * NNRat.rawCast 13698989235951035150963 1871953121312243712))) + ((h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 171062954862404659955) 25999348907114496)) + (h ^ (22-15:ℕ) * (1 * NNRat.rawCast 49885731574910801809 12999674453557248)))))

def boundaryReVBlock76_2_5 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 190590726744196973) 106993205379072)) + ((h ^ (22-17:ℕ) * (1 * NNRat.rawCast 33494889062154179 60183678025728)) + (h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 382742526859747) 30091839012864)))) + (((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 723720349910629) 13374150672384)) + (h ^ (22-20:ℕ) * (1 * NNRat.rawCast 13444892471737 743008370688))) + ((h ^ (22-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 830159266759) 371504185344)) + (h ^ (22-22:ℕ) * (1 * NNRat.rawCast 237639341 23219011584)))))

theorem boundaryCompactReVC75_5_blocks76 (h : ℂ) :

    boundaryCompactReVC75_5 h=((boundaryReVBlock76_0_5 h) + ((boundaryReVBlock76_1_5 h) + (boundaryReVBlock76_2_5 h))) := by

  dsimp only [boundaryCompactReVC75_5,boundaryReVBlock76_0_5,boundaryReVBlock76_1_5,boundaryReVBlock76_2_5]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_6 (h : ℂ) : ℂ :=
  ((((h ^ (22-0:ℕ) * (Rat.rawCast (Int.negOfNat 481627174061185) 444223250467651584)) + (h ^ (22-0:ℕ) * (0))) + ((h ^ (22-1:ℕ) * (1 * NNRat.rawCast 557906639413369 98716277881700352)) + (h ^ (22-2:ℕ) * (1 * NNRat.rawCast 1219387355802268729 28430288029929701376)))) + (((h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 58122293236334202227) 227442304239437611008)) + (h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 231315239670513525181) 909769216957750444032))) + ((h ^ (22-5:ℕ) * (1 * NNRat.rawCast 51430836067057328897645 14556307471324007104512)) + ((h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 281761075635426891451) 75814101413145870336)) + (h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 233698320193774483288829) 14556307471324007104512))))))

def boundaryReVBlock76_1_6 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * NNRat.rawCast 107343733308333326334655 2426051245220667850752)) + (h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 10544893741401536648471) 2426051245220667850752))) + ((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 145741444199649128321281) 909769216957750444032)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 217283734849662393760351 909769216957750444032)))) + (((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 57682450310238252761467 303256405652583481344)) + (h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 35273132611297615146547) 37907050706572935168))) + ((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 4980749091225040376033 4211894522952548352)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 917648299010004047923) 1052973630738137088)))))

def boundaryReVBlock76_2_6 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 171166027756488223399 350991210246045696)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 25098369019341149041) 116997070082015232)) + (h ^ (22-18:ℕ) * (1 * NNRat.rawCast 607067186808576749 9749755840167936)))) + (((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1615212828003749) 203119913336832)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 231393718616249) 541653102231552))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 1470174938317 7522959753216)) + (h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6390601583) 3761479876608)))))

theorem boundaryCompactReVC75_6_blocks76 (h : ℂ) :

    boundaryCompactReVC75_6 h=((boundaryReVBlock76_0_6 h) + ((boundaryReVBlock76_1_6 h) + (boundaryReVBlock76_2_6 h))) := by

  dsimp only [boundaryCompactReVC75_6,boundaryReVBlock76_0_6,boundaryReVBlock76_1_6,boundaryReVBlock76_2_6]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_7 (h : ℂ) : ℂ :=
  ((((h ^ (22-0:ℕ) * (NNRat.rawCast 81230749376785 999502313552216064)) + (h ^ (22-0:ℕ) * (0))) + ((h ^ (22-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 496737052078147) 7996018508417728512)) + (h ^ (22-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1195112806016720977) 255872592269367312384)))) + (((h ^ (22-3:ℕ) * (1 * NNRat.rawCast 24762701480477393177 2046980738154938499072)) + (h ^ (22-4:ℕ) * (1 * NNRat.rawCast 313842574109956854443 4093961476309876998144))) + ((h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1129103945050697019451) 3639076867831001776128)) + ((h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 13807642091898483940871) 43668922413972021313536)) + (h ^ (22-7:ℕ) * (1 * NNRat.rawCast 185742948129001140193165 65503383620958031970304))))))

def boundaryReVBlock76_1_7 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 287923889288486821105085) 131006767241916063940608)) + (h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 93342218685735778372457) 10917230603493005328384))) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 304167568125043871031755 16375845905239507992576)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 158415410897264082940625) 16375845905239507992576)))) + (((h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 148836131214605550856559) 8187922952619753996288)) + (h ^ (22-13:ℕ) * (1 * NNRat.rawCast 39768630018302239350229 682326912718312833024))) + ((h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 4981256759504263998289) 56860576059859402752)) + (h ^ (22-15:ℕ) * (1 * NNRat.rawCast 4515688081356966679595 56860576059859402752)))))

def boundaryReVBlock76_2_7 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2906552668529720416055) 56860576059859402752)) + ((h ^ (22-17:ℕ) * (1 * NNRat.rawCast 43089469661531776945 1579460446107205632)) + (h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2986895310826234465) 263243407684534272)))) + (((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 850454224292735941 263243407684534272)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 7967989674815663) 14624633760251904))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 51748298396375 1218719480020992)) + (h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 146122178851) 152339935002624)))))

theorem boundaryCompactReVC75_7_blocks76 (h : ℂ) :

    boundaryCompactReVC75_7 h=((boundaryReVBlock76_0_7 h) + ((boundaryReVBlock76_1_7 h) + (boundaryReVBlock76_2_7 h))) := by

  dsimp only [boundaryCompactReVC75_7,boundaryReVBlock76_0_7,boundaryReVBlock76_1_7,boundaryReVBlock76_2_7]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_8 (h : ℂ) : ℂ :=
  ((((h ^ (22-0:ℕ) * (Rat.rawCast (Int.negOfNat 215184678307973) 71964166575759556608)) + (h ^ (22-0:ℕ) * (0))) + ((h ^ (22-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1724993331041965) 71964166575759556608)) + (h ^ (22-2:ℕ) * (1 * NNRat.rawCast 269967154765347329 767617776808101937152)))) + (((h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1162115703515777765) 6140942214464815497216)) + (h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1217569843162022658095) 147382613147155571933184))) + ((h ^ (22-5:ℕ) * (1 * NNRat.rawCast 2287292812882742527355 98255075431437047955456)) + ((h ^ (22-6:ℕ) * (1 * NNRat.rawCast 441846406193946970051 9211413321697223245824)) + (h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 87804898030082716376593) 294765226294311143866368))))))

def boundaryReVBlock76_1_8 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * NNRat.rawCast 22179299769693391051463 98255075431437047955456)) + (h ^ (22-9:ℕ) * (1 * NNRat.rawCast 301421433559311819865325 294765226294311143866368))) + ((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 331499366305689418554149) 147382613147155571933184)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 113344674946822636143241 147382613147155571933184)))) + (((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 34705095933069585653809 18422826643394446491648)) + (h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 16606306217037983949313) 9211413321697223245824))) + ((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 1545855966180359988673 9211413321697223245824)) + (h ^ (22-15:ℕ) * (1 * NNRat.rawCast 180593255494178709653 383808888404050968576)))))

def boundaryReVBlock76_2_8 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 360790148552129508947) 767617776808101937152)) + ((h ^ (22-17:ℕ) * (1 * NNRat.rawCast 222675550817164993 999502313552216064)) + (h ^ (22-18:ℕ) * (1 * NNRat.rawCast 578136324146852569 10661358011223638016)))) + (((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 217078033682838691) 2369190669160808448)) + (h ^ (22-20:ℕ) * (1 * NNRat.rawCast 20096918107407283 592297667290202112))) + ((h ^ (22-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 369218454545003) 98716277881700352)) + (h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 462236958017) 8226356490141696)))))

theorem boundaryCompactReVC75_8_blocks76 (h : ℂ) :

    boundaryCompactReVC75_8 h=((boundaryReVBlock76_0_8 h) + ((boundaryReVBlock76_1_8 h) + (boundaryReVBlock76_2_8 h))) := by

  dsimp only [boundaryCompactReVC75_8,boundaryReVBlock76_0_8,boundaryReVBlock76_1_8,boundaryReVBlock76_2_8]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_9 (h : ℂ) : ℂ :=
  ((((h ^ (22-0:ℕ) * (NNRat.rawCast 3583883340325 80959687397729501184)) + (h ^ (22-0:ℕ) * (0))) + ((h ^ (22-1:ℕ) * (1 * NNRat.rawCast 2230642890041647 1295354998363672018944)) + (h ^ (22-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 310204600881843443) 20725679973818752303104)))) + (((h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 549139232604042251) 55268479930183339474944)) + (h ^ (22-4:ℕ) * (1 * NNRat.rawCast 89306678582029681073 221073919720733357899776))) + ((h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5160698425928265416837) 5305774073297600589594624)) + ((h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12371300642096435429515) 5305774073297600589594624)) + (h ^ (22-7:ℕ) * (1 * NNRat.rawCast 73277382533984112347327 5305774073297600589594624))))))

def boundaryReVBlock76_1_9 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 71932924127465264777429) 5305774073297600589594624)) + (h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3412479099071539444645) 82902719895275009212416))) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 101473495072202368216489 884295678882933431599104)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 21420596387907027650563) 331610879581100036849664)))) + (((h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 23017327816305596756789) 331610879581100036849664)) + (h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8469310340657753919685) 331610879581100036849664))) + ((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 30434543818219388941837 82902719895275009212416)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5871337127094591358921) 10362839986909376151552)))))

def boundaryReVBlock76_2_9 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 3353900685787599339853 6908559991272917434368)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1027008814990190065373) 3454279995636458717184)) + (h ^ (22-18:ℕ) * (1 * NNRat.rawCast 152159557915890669563 1151426665212152905728)))) + (((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 225651476856301229) 5997013881313296384)) + (h ^ (22-20:ℕ) * (1 * NNRat.rawCast 96039540769832831 15992037016835457024))) + ((h ^ (22-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2540983306797479) 5330679005611819008)) + (h ^ (22-22:ℕ) * (1 * NNRat.rawCast 3484089980375 111055812616912896)))))

theorem boundaryCompactReVC75_9_blocks76 (h : ℂ) :

    boundaryCompactReVC75_9 h=((boundaryReVBlock76_0_9 h) + ((boundaryReVBlock76_1_9 h) + (boundaryReVBlock76_2_9 h))) := by

  dsimp only [boundaryCompactReVC75_9,boundaryReVBlock76_0_9,boundaryReVBlock76_1_9,boundaryReVBlock76_2_9]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_10 (h : ℂ) : ℂ :=
  ((((h ^ (22-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 219554668799417) 5829097492636524085248)) + (h ^ (22-2:ℕ) * (1 * NNRat.rawCast 12130058470804363 62177039921456256909312))) + ((h ^ (22-3:ℕ) * (1 * NNRat.rawCast 1568068473089652007 1492248958114950165823488)) + (h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 47621265901752686737) 5968995832459800663293952)))) + (((h ^ (22-5:ℕ) * (1 * NNRat.rawCast 30307738044516609971 47751966659678405306351616)) + (h ^ (22-6:ℕ) * (1 * NNRat.rawCast 137718802375168940327 1492248958114950165823488))) + ((h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8226262614482804328827) 47751966659678405306351616)) + (h ^ (22-0:ℕ) * (0)))))

def boundaryReVBlock76_1_10 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2194088939615026270777) 7958661109946400884391936)) + (h ^ (22-9:ℕ) * (1 * NNRat.rawCast 28720732444219307679151 23875983329839202653175808))) + ((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 173821314463967610587) 221073919720733357899776)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 7364025302116830422221) 2984497916229900331646976)))) + (((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 15913194802104545222659 2984497916229900331646976)) + (h ^ (22-13:ℕ) * (1 * NNRat.rawCast 388050210858173238445 746124479057475082911744))) + ((h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1625256668537592527107) 93265559882184385363968)) + (h ^ (22-15:ℕ) * (1 * NNRat.rawCast 5922961490081569048043 186531119764368770727936)))))

def boundaryReVBlock76_2_10 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 721749056167545670429) 23316389970546096340992)) + ((h ^ (22-17:ℕ) * (1 * NNRat.rawCast 209943755440339635623 10362839986909376151552)) + (h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8412143827697953753) 863569998909114679296)))) + (((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 1391085708731893169 431784999454557339648)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 27862005220957595) 47976111050506371072))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 51618736230307 1999004627104432128)) + (h ^ (22-22:ℕ) * (1 * NNRat.rawCast 4346286687145 999502313552216064)))))

theorem boundaryCompactReVC75_10_blocks76 (h : ℂ) :

    boundaryCompactReVC75_10 h=((boundaryReVBlock76_0_10 h) + ((boundaryReVBlock76_1_10 h) + (boundaryReVBlock76_2_10 h))) := by

  dsimp only [boundaryCompactReVC75_10,boundaryReVBlock76_0_10,boundaryReVBlock76_1_10,boundaryReVBlock76_2_10]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_11 (h : ℂ) : ℂ :=
  (((h ^ (22-2:ℕ) * (1 * NNRat.rawCast 2092690629306389 559593359293106312183808)) + ((h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 195696744640400479) 4476746874344850497470464)) + (h ^ (22-4:ℕ) * (1 * NNRat.rawCast 463758260460286567 6715120311517275746205696)))) + (((h ^ (22-5:ℕ) * (1 * NNRat.rawCast 197027590222479495187 214883849968552823878582272)) + (h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1686110171985694647533) 429767699937105647757164544))) + ((h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 274850889402850673191) 214883849968552823878582272)) + (h ^ (22-0:ℕ) * (0)))))

def boundaryReVBlock76_1_11 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * NNRat.rawCast 15663352326677126150243 429767699937105647757164544)) + (h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 530562256287476278741) 7958661109946400884391936))) + ((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 284809855741897658651) 8953493748689700994940928)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 2431146124146807267779 8953493748689700994940928)))) + (((h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12096348797041315544957) 26860481246069102984822784)) + (h ^ (22-13:ℕ) * (1 * NNRat.rawCast 31145032053012378161 69949169911638289022976))) + ((h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 991483469309568904681) 3357560155758637873102848)) + (h ^ (22-15:ℕ) * (1 * NNRat.rawCast 44743664677374445597 839390038939659468275712)))))

def boundaryReVBlock76_2_11 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 75898718405562616109 559593359293106312183808)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5090260560777314953) 31088519960728128454656)) + (h ^ (22-18:ℕ) * (1 * NNRat.rawCast 840239744932859063 7772129990182032113664)))) + (((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 67366298761168637) 1295354998363672018944)) + (h ^ (22-20:ℕ) * (1 * NNRat.rawCast 750761698285889 47976111050506371072))) + ((h ^ (22-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 62061492234979) 35982083287879778304)) + (h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 278045141603) 1499253470328324096)))))

theorem boundaryCompactReVC75_11_blocks76 (h : ℂ) :

    boundaryCompactReVC75_11 h=((boundaryReVBlock76_0_11 h) + ((boundaryReVBlock76_1_11 h) + (boundaryReVBlock76_2_11 h))) := by

  dsimp only [boundaryCompactReVC75_11,boundaryReVBlock76_0_11,boundaryReVBlock76_1_11,boundaryReVBlock76_2_11]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_12 (h : ℂ) : ℂ :=
  (((h ^ (22-3:ℕ) * (1 * NNRat.rawCast 13750076961227201 40290721869103654477234176)) + ((h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2272675605429860617) 1933954649716975414907240448)) + (h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5039774240878068055) 644651549905658471635746816)))) + ((h ^ (22-6:ℕ) * (1 * NNRat.rawCast 18566124275462682571 483488662429243853726810112)) + ((h ^ (22-7:ℕ) * (1 * NNRat.rawCast 26776111773646803391 1933954649716975414907240448)) + (h ^ (22-0:ℕ) * (0)))))

def boundaryReVBlock76_1_12 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1304097701503479099571) 3867909299433950829814480896)) + (h ^ (22-9:ℕ) * (1 * NNRat.rawCast 2120623462217466563867 3867909299433950829814480896))) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 78606866482981670647 214883849968552823878582272)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 618220385259497250371) 322325774952829235817873408)))) + (((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 1046849667960175476809 483488662429243853726810112)) + (h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 71698112184124150135) 20145360934551827238617088))) + ((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 228960159330259212487 20145360934551827238617088)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 71472793920992688065) 3357560155758637873102848)))))

def boundaryReVBlock76_2_12 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 6468702351852070967 279796679646553156091904)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3038075452299828817) 186531119764368770727936)) + (h ^ (22-18:ℕ) * (1 * NNRat.rawCast 241831928414606501 31088519960728128454656)))) + (((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11415856074045205) 5181419993454688075776)) + (h ^ (22-20:ℕ) * (1 * NNRat.rawCast 72967459076987 863569998909114679296))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 11559301569253 71964166575759556608)) + (h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 116284680869) 2998506940656648192)))))

theorem boundaryCompactReVC75_12_blocks76 (h : ℂ) :

    boundaryCompactReVC75_12 h=((boundaryReVBlock76_0_12 h) + ((boundaryReVBlock76_1_12 h) + (boundaryReVBlock76_2_12 h))) := by

  dsimp only [boundaryCompactReVC75_12,boundaryReVBlock76_0_12,boundaryReVBlock76_1_12,boundaryReVBlock76_2_12]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_13 (h : ℂ) : ℂ :=
  (((h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 293575300609695167) 8702795923726389367082582016)) + (h ^ (22-5:ℕ) * (1 * NNRat.rawCast 8348206677096029765 69622367389811114936660656128))) + ((h ^ (22-6:ℕ) * (1 * NNRat.rawCast 44936924283632287949 69622367389811114936660656128)) + ((h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 231947510939720780939) 69622367389811114936660656128)) + (h ^ (22-0:ℕ) * (0)))))

def boundaryReVBlock76_1_13 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 24492496571545759715) 69622367389811114936660656128)) + (h ^ (22-9:ℕ) * (1 * NNRat.rawCast 445549157507532871811 17405591847452778734165164032))) + ((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 137281532535594258137) 2900931974575463122360860672)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 23136298541254051547) 2900931974575463122360860672)))) + (((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 228223513353820054213 1450465987287731561180430336)) + (h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 694079110520357887337) 2175698980931597341770645504))) + ((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 6074204053222347575 15109020700913870428962816)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1835568962721740285) 5036340233637956809654272)))))

def boundaryReVBlock76_2_13 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 29034035389673845 124354079842912513818624)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12953531278545725) 139898339823276578045952)) + (h ^ (22-18:ℕ) * (1 * NNRat.rawCast 210883010884061 46632779941092192681984)))) + (((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 390881856585281 15544259980364064227328)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 52274983049483) 2590709996727344037888))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 3259747474309 431784999454557339648)) + (h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 31501017683) 26986562465909833728)))))

theorem boundaryCompactReVC75_13_blocks76 (h : ℂ) :

    boundaryCompactReVC75_13 h=((boundaryReVBlock76_0_13 h) + ((boundaryReVBlock76_1_13 h) + (boundaryReVBlock76_2_13 h))) := by

  dsimp only [boundaryCompactReVC75_13,boundaryReVBlock76_0_13,boundaryReVBlock76_1_13,boundaryReVBlock76_2_13]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_14 (h : ℂ) : ℂ :=
  (((h ^ (22-5:ℕ) * (1 * NNRat.rawCast 405506432602597781 626601306508300034429945905152)) + (h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 21101830690497529) 19581290828384376075935809536))) + ((h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8209422637318359989) 626601306508300034429945905152)) + (h ^ (22-0:ℕ) * (0))))

def boundaryReVBlock76_1_14 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * NNRat.rawCast 11310413425473433145 313300653254150017214972952576)) + (h ^ (22-9:ℕ) * (1 * NNRat.rawCast 17353859589311349559 313300653254150017214972952576))) + ((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 14810488993092655) 45327062102741611286888448)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 4516372364942935217 13054193885589584050623873024)))) + (((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 6578963650269116407 13054193885589584050623873024)) + (h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1061782103192386915) 543924745232899335442661376))) + ((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 56585322924564629 20145360934551827238617088)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11858614216838335) 5036340233637956809654272)))))

def boundaryReVBlock76_2_14 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 1882041096446303 1678780077879318936551424)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 4049378169677) 62177039921456256909312)) + (h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 19107514648465) 46632779941092192681984)))) + (((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 831670544725 1943032497545508028416)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 639614828653) 2590709996727344037888))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 26178089645 323838749590918004736)) + (h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 620897345) 53973124931819667456)))))

theorem boundaryCompactReVC75_14_blocks76 (h : ℂ) :

    boundaryCompactReVC75_14 h=((boundaryReVBlock76_0_14 h) + ((boundaryReVBlock76_1_14 h) + (boundaryReVBlock76_2_14 h))) := by

  dsimp only [boundaryCompactReVC75_14,boundaryReVBlock76_0_14,boundaryReVBlock76_1_14,boundaryReVBlock76_2_14]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_15 (h : ℂ) : ℂ :=
  ((h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 18285856292474113) 5639411758574700309869513146368)) + ((h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1511966328663049) 2819705879287350154934756573184)) + (h ^ (22-0:ℕ) * (0))))

def boundaryReVBlock76_1_15 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * NNRat.rawCast 339871085508091991 5639411758574700309869513146368)) + (h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 33453624729784819) 469950979881225025822459428864))) + ((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 81733900791335149) 234975489940612512911229714432)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 74320809587825143 78325163313537504303743238144)))) + (((h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2806193702380529) 13054193885589584050623873024)) + (h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 912627572016575) 362616496821932890295107584))) + ((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 153363552041435 30218041401827740857925632)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 50511907346555) 10072680467275913619308544)))))

def boundaryReVBlock76_2_15 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 9321260092597 3357560155758637873102848)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 98888408879) 279796679646553156091904)) + (h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 17206671299) 15544259980364064227328)))) + (((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 64740079991 46632779941092192681984)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6749363443) 7772129990182032113664))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 187667839 647677499181836009472)) + (h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 121577) 2998506940656648192)))))

theorem boundaryCompactReVC75_15_blocks76 (h : ℂ) :

    boundaryCompactReVC75_15 h=((boundaryReVBlock76_0_15 h) + ((boundaryReVBlock76_1_15 h) + (boundaryReVBlock76_2_15 h))) := by

  dsimp only [boundaryCompactReVC75_15,boundaryReVBlock76_0_15,boundaryReVBlock76_1_15,boundaryReVBlock76_2_15]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_16 (h : ℂ) : ℂ :=
  ((h ^ (22-7:ℕ) * (1 * NNRat.rawCast 168937493305 49565142409347951942212517888)) + (h ^ (22-0:ℕ) * (0)))

def boundaryReVBlock76_1_16 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * NNRat.rawCast 8265944738779 1586084557099134462150800572416)) + (h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 342464455864405) 6344338228396537848603202289664))) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 855060108259 1057389704732756308100533714944)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 78978986476313 234975489940612512911229714432)))) + (((h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 28241139865477) 58743872485153128227807428608)) + (h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1566533457391) 4895322707096094018983952384))) + ((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 103476255715 60436082803655481715851264)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 119579308637) 45327062102741611286888448)))))

def boundaryReVBlock76_2_16 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 38588663779 15109020700913870428962816)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3402513433) 2518170116818978404827136)) + (h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 454484377) 1259085058409489202413568)))) + (((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 527387345 419695019469829734137856)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1383029) 1457274373159131021312))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 1935091 5829097492636524085248)) + (h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 22445) 485758124386377007104)))))

theorem boundaryCompactReVC75_16_blocks76 (h : ℂ) :

    boundaryCompactReVC75_16 h=((boundaryReVBlock76_0_16 h) + ((boundaryReVBlock76_1_16 h) + (boundaryReVBlock76_2_16 h))) := by

  dsimp only [boundaryCompactReVC75_16,boundaryReVBlock76_0_16,boundaryReVBlock76_1_16,boundaryReVBlock76_2_16]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_17 (h : ℂ) : ℂ :=
  (h ^ (22-0:ℕ) * (0))

def boundaryReVBlock76_1_17 (h : ℂ) : ℂ :=
  ((((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 14325530485) 114198088111137681274857641213952)) + (h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2426981221) 57099044055568840637428820606976))) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 26945503417 38066029370379227091619213737984)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 7534594907) 1057389704732756308100533714944)))) + (((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 758012507 132173713091594538512566714368)) + (h ^ (22-13:ℕ) * (1 * NNRat.rawCast 11700680453 176231617455459384683422285824))) + ((h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 72277303) 543924745232899335442661376)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 18989215) 203971779462337250790998016)))))

def boundaryReVBlock76_2_17 (h : ℂ) : ℂ :=
  (((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 4489513 8498824144264052116291584)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 13254793) 22663531051370805643444224)) + (h ^ (22-18:ℕ) * (1 * NNRat.rawCast 3202801 22663531051370805643444224)))) + (((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 434041 1888627587614233803620352)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11819) 52461877433728716767232))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 8669 104923754867457433534464)) + (h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 25) 2185911559738696531968)))))

theorem boundaryCompactReVC75_17_blocks76 (h : ℂ) :

    boundaryCompactReVC75_17 h=((boundaryReVBlock76_0_17 h) + ((boundaryReVBlock76_1_17 h) + (boundaryReVBlock76_2_17 h))) := by

  dsimp only [boundaryCompactReVC75_17,boundaryReVBlock76_0_17,boundaryReVBlock76_1_17,boundaryReVBlock76_2_17]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReVBlock76_0_18 (h : ℂ) : ℂ :=
  (h ^ (22-0:ℕ) * (0))

def boundaryReVBlock76_1_18 (h : ℂ) : ℂ :=
  0

def boundaryReVBlock76_2_18 (h : ℂ) : ℂ :=
  0

theorem boundaryCompactReVC75_18_blocks76 (h : ℂ) :

    boundaryCompactReVC75_18 h=((boundaryReVBlock76_0_18 h) + ((boundaryReVBlock76_1_18 h) + (boundaryReVBlock76_2_18 h))) := by

  dsimp only [boundaryCompactReVC75_18,boundaryReVBlock76_0_18,boundaryReVBlock76_1_18,boundaryReVBlock76_2_18]

  try simp only [add_zero,zero_add]

  all_goals ac_rfl

def boundaryReClockBlock76_0 (h r : ℂ) : ℂ :=
  ((((h^(22-0:ℕ)*boundaryReClock76_0 (r*h^2)) + (h^(22-1:ℕ)*boundaryReClock76_1 (r*h^2))) + ((h^(22-2:ℕ)*boundaryReClock76_2 (r*h^2)) + (h^(22-3:ℕ)*boundaryReClock76_3 (r*h^2)))) + (((h^(22-4:ℕ)*boundaryReClock76_4 (r*h^2)) + (h^(22-5:ℕ)*boundaryReClock76_5 (r*h^2))) + ((h^(22-6:ℕ)*boundaryReClock76_6 (r*h^2)) + (h^(22-7:ℕ)*boundaryReClock76_7 (r*h^2)))))

def boundaryReVSumBlock76_0 (h r : ℂ) : ℂ :=
  ((((((9-r*h^2)^0*boundaryReVBlock76_0_0 h) + ((9-r*h^2)^1*boundaryReVBlock76_0_1 h)) + (((9-r*h^2)^2*boundaryReVBlock76_0_2 h) + ((9-r*h^2)^3*boundaryReVBlock76_0_3 h))) + ((((9-r*h^2)^4*boundaryReVBlock76_0_4 h) + ((9-r*h^2)^5*boundaryReVBlock76_0_5 h)) + (((9-r*h^2)^6*boundaryReVBlock76_0_6 h) + (((9-r*h^2)^7*boundaryReVBlock76_0_7 h) + ((9-r*h^2)^8*boundaryReVBlock76_0_8 h))))) + (((((9-r*h^2)^9*boundaryReVBlock76_0_9 h) + ((9-r*h^2)^10*boundaryReVBlock76_0_10 h)) + (((9-r*h^2)^11*boundaryReVBlock76_0_11 h) + (((9-r*h^2)^12*boundaryReVBlock76_0_12 h) + ((9-r*h^2)^13*boundaryReVBlock76_0_13 h)))) + ((((9-r*h^2)^14*boundaryReVBlock76_0_14 h) + ((9-r*h^2)^15*boundaryReVBlock76_0_15 h)) + (((9-r*h^2)^16*boundaryReVBlock76_0_16 h) + (((9-r*h^2)^17*boundaryReVBlock76_0_17 h) + ((9-r*h^2)^18*boundaryReVBlock76_0_18 h))))))

theorem boundaryReClockBlock76_0_eq (h r : ℂ) : boundaryReVSumBlock76_0 h r=boundaryReClockBlock76_0 h r := by

  dsimp only [boundaryReVSumBlock76_0,boundaryReClockBlock76_0,boundaryReVBlock76_0_0,boundaryReVBlock76_0_1,boundaryReVBlock76_0_2,boundaryReVBlock76_0_3,boundaryReVBlock76_0_4,boundaryReVBlock76_0_5,boundaryReVBlock76_0_6,boundaryReVBlock76_0_7,boundaryReVBlock76_0_8,boundaryReVBlock76_0_9,boundaryReVBlock76_0_10,boundaryReVBlock76_0_11,boundaryReVBlock76_0_12,boundaryReVBlock76_0_13,boundaryReVBlock76_0_14,boundaryReVBlock76_0_15,boundaryReVBlock76_0_16,boundaryReVBlock76_0_17,boundaryReVBlock76_0_18,boundaryReClock76_0,boundaryReClock76_1,boundaryReClock76_2,boundaryReClock76_3,boundaryReClock76_4,boundaryReClock76_5,boundaryReClock76_6,boundaryReClock76_7]

  simp only [mul_add,mul_zero,zero_add,add_zero,pow_zero,pow_one,one_mul]

  ac_rfl


def boundaryReClockBlock76_1 (h r : ℂ) : ℂ :=
  ((((h^(22-8:ℕ)*boundaryReClock76_8 (r*h^2)) + (h^(22-9:ℕ)*boundaryReClock76_9 (r*h^2))) + ((h^(22-10:ℕ)*boundaryReClock76_10 (r*h^2)) + (h^(22-11:ℕ)*boundaryReClock76_11 (r*h^2)))) + (((h^(22-12:ℕ)*boundaryReClock76_12 (r*h^2)) + (h^(22-13:ℕ)*boundaryReClock76_13 (r*h^2))) + ((h^(22-14:ℕ)*boundaryReClock76_14 (r*h^2)) + (h^(22-15:ℕ)*boundaryReClock76_15 (r*h^2)))))

def boundaryReVSumBlock76_1 (h r : ℂ) : ℂ :=
  ((((((9-r*h^2)^0*boundaryReVBlock76_1_0 h) + ((9-r*h^2)^1*boundaryReVBlock76_1_1 h)) + (((9-r*h^2)^2*boundaryReVBlock76_1_2 h) + ((9-r*h^2)^3*boundaryReVBlock76_1_3 h))) + ((((9-r*h^2)^4*boundaryReVBlock76_1_4 h) + ((9-r*h^2)^5*boundaryReVBlock76_1_5 h)) + (((9-r*h^2)^6*boundaryReVBlock76_1_6 h) + (((9-r*h^2)^7*boundaryReVBlock76_1_7 h) + ((9-r*h^2)^8*boundaryReVBlock76_1_8 h))))) + (((((9-r*h^2)^9*boundaryReVBlock76_1_9 h) + ((9-r*h^2)^10*boundaryReVBlock76_1_10 h)) + (((9-r*h^2)^11*boundaryReVBlock76_1_11 h) + (((9-r*h^2)^12*boundaryReVBlock76_1_12 h) + ((9-r*h^2)^13*boundaryReVBlock76_1_13 h)))) + ((((9-r*h^2)^14*boundaryReVBlock76_1_14 h) + ((9-r*h^2)^15*boundaryReVBlock76_1_15 h)) + (((9-r*h^2)^16*boundaryReVBlock76_1_16 h) + (((9-r*h^2)^17*boundaryReVBlock76_1_17 h) + ((9-r*h^2)^18*boundaryReVBlock76_1_18 h))))))

theorem boundaryReClockBlock76_1_eq (h r : ℂ) : boundaryReVSumBlock76_1 h r=boundaryReClockBlock76_1 h r := by

  dsimp only [boundaryReVSumBlock76_1,boundaryReClockBlock76_1,boundaryReVBlock76_1_0,boundaryReVBlock76_1_1,boundaryReVBlock76_1_2,boundaryReVBlock76_1_3,boundaryReVBlock76_1_4,boundaryReVBlock76_1_5,boundaryReVBlock76_1_6,boundaryReVBlock76_1_7,boundaryReVBlock76_1_8,boundaryReVBlock76_1_9,boundaryReVBlock76_1_10,boundaryReVBlock76_1_11,boundaryReVBlock76_1_12,boundaryReVBlock76_1_13,boundaryReVBlock76_1_14,boundaryReVBlock76_1_15,boundaryReVBlock76_1_16,boundaryReVBlock76_1_17,boundaryReVBlock76_1_18,boundaryReClock76_8,boundaryReClock76_9,boundaryReClock76_10,boundaryReClock76_11,boundaryReClock76_12,boundaryReClock76_13,boundaryReClock76_14,boundaryReClock76_15]

  simp only [mul_add,mul_zero,zero_add,add_zero,pow_zero,pow_one,one_mul]

  ac_rfl


def boundaryReClockBlock76_2 (h r : ℂ) : ℂ :=
  (((h^(22-16:ℕ)*boundaryReClock76_16 (r*h^2)) + ((h^(22-17:ℕ)*boundaryReClock76_17 (r*h^2)) + (h^(22-18:ℕ)*boundaryReClock76_18 (r*h^2)))) + (((h^(22-19:ℕ)*boundaryReClock76_19 (r*h^2)) + (h^(22-20:ℕ)*boundaryReClock76_20 (r*h^2))) + ((h^(22-21:ℕ)*boundaryReClock76_21 (r*h^2)) + (h^(22-22:ℕ)*boundaryReClock76_22 (r*h^2)))))

def boundaryReVSumBlock76_2 (h r : ℂ) : ℂ :=
  ((((((9-r*h^2)^0*boundaryReVBlock76_2_0 h) + ((9-r*h^2)^1*boundaryReVBlock76_2_1 h)) + (((9-r*h^2)^2*boundaryReVBlock76_2_2 h) + ((9-r*h^2)^3*boundaryReVBlock76_2_3 h))) + ((((9-r*h^2)^4*boundaryReVBlock76_2_4 h) + ((9-r*h^2)^5*boundaryReVBlock76_2_5 h)) + (((9-r*h^2)^6*boundaryReVBlock76_2_6 h) + (((9-r*h^2)^7*boundaryReVBlock76_2_7 h) + ((9-r*h^2)^8*boundaryReVBlock76_2_8 h))))) + (((((9-r*h^2)^9*boundaryReVBlock76_2_9 h) + ((9-r*h^2)^10*boundaryReVBlock76_2_10 h)) + (((9-r*h^2)^11*boundaryReVBlock76_2_11 h) + (((9-r*h^2)^12*boundaryReVBlock76_2_12 h) + ((9-r*h^2)^13*boundaryReVBlock76_2_13 h)))) + ((((9-r*h^2)^14*boundaryReVBlock76_2_14 h) + ((9-r*h^2)^15*boundaryReVBlock76_2_15 h)) + (((9-r*h^2)^16*boundaryReVBlock76_2_16 h) + (((9-r*h^2)^17*boundaryReVBlock76_2_17 h) + ((9-r*h^2)^18*boundaryReVBlock76_2_18 h))))))

theorem boundaryReClockBlock76_2_eq (h r : ℂ) : boundaryReVSumBlock76_2 h r=boundaryReClockBlock76_2 h r := by

  dsimp only [boundaryReVSumBlock76_2,boundaryReClockBlock76_2,boundaryReVBlock76_2_0,boundaryReVBlock76_2_1,boundaryReVBlock76_2_2,boundaryReVBlock76_2_3,boundaryReVBlock76_2_4,boundaryReVBlock76_2_5,boundaryReVBlock76_2_6,boundaryReVBlock76_2_7,boundaryReVBlock76_2_8,boundaryReVBlock76_2_9,boundaryReVBlock76_2_10,boundaryReVBlock76_2_11,boundaryReVBlock76_2_12,boundaryReVBlock76_2_13,boundaryReVBlock76_2_14,boundaryReVBlock76_2_15,boundaryReVBlock76_2_16,boundaryReVBlock76_2_17,boundaryReVBlock76_2_18,boundaryReClock76_16,boundaryReClock76_17,boundaryReClock76_18,boundaryReClock76_19,boundaryReClock76_20,boundaryReClock76_21,boundaryReClock76_22]

  simp only [mul_add,mul_zero,zero_add,add_zero,pow_zero,pow_one,one_mul]

  ac_rfl


def boundaryReClockSum76 (h r : ℂ) : ℂ :=
  ((boundaryReClockBlock76_0 h r) + ((boundaryReClockBlock76_1 h r) + (boundaryReClockBlock76_2 h r)))

theorem boundaryReClockSum76_eq (h r : ℂ) :

    boundaryCompactA75 h r=boundaryReClockSum76 h r := by

  have he : boundaryCompactA75 h r=((boundaryReVSumBlock76_0 h r) + ((boundaryReVSumBlock76_1 h r) + (boundaryReVSumBlock76_2 h r))) := by

    dsimp only [boundaryCompactA75,boundaryReVSumBlock76_0,boundaryReVSumBlock76_1,boundaryReVSumBlock76_2]

    rw [boundaryCompactReVC75_0_blocks76,boundaryCompactReVC75_1_blocks76,boundaryCompactReVC75_2_blocks76,boundaryCompactReVC75_3_blocks76,boundaryCompactReVC75_4_blocks76,boundaryCompactReVC75_5_blocks76,boundaryCompactReVC75_6_blocks76,boundaryCompactReVC75_7_blocks76,boundaryCompactReVC75_8_blocks76,boundaryCompactReVC75_9_blocks76,boundaryCompactReVC75_10_blocks76,boundaryCompactReVC75_11_blocks76,boundaryCompactReVC75_12_blocks76,boundaryCompactReVC75_13_blocks76,boundaryCompactReVC75_14_blocks76,boundaryCompactReVC75_15_blocks76,boundaryCompactReVC75_16_blocks76,boundaryCompactReVC75_17_blocks76,boundaryCompactReVC75_18_blocks76]

    have h1 : (Nat.rawCast 1 : ℕ)=1 := rfl

    simp only [h1,mul_add,pow_zero,pow_one,one_mul]

    ac_rfl

  rw [he]

  simp only [boundaryReClockBlock76_0_eq,boundaryReClockBlock76_1_eq,boundaryReClockBlock76_2_eq,boundaryReClockSum76]


end

end HTGeometry.ThetaRatioInfinity
