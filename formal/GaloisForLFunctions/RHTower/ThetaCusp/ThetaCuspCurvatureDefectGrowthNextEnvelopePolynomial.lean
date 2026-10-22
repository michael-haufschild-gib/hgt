import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthNextKernelPolynomial
/-! Exact coefficient certificate for the ninth-moment upper envelope
of the pair-relative transfer kernel above cubic support. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section
private def nextCacheP (y : ℝ) : ℝ :=
  (1861439671925411064321195/262144)*y^0+(17029102555455663849163083/131072)*y^1+(322103250906652692527224995/262144)*y^2+
    (3986068609578601786146770907/524288)*y^3+(17747426224968762775188708801/524288)*y^4+(60205290770051699808697176159/524288)*y^5+
    (161889339980151795383364100185/524288)*y^6+(88783224129787319215420379949/131072)*y^7+(40584482588850241239154879101/32768)*y^8+
    (125732997201449447835433962975/65536)*y^9+(83526071203783400209001293023/32768)*y^10+(24021870812074579694285775753/8192)*y^11+
    (3012388545381711954421912695/1024)*y^12+(10598204705085701542133692191/4096)*y^13+(2051032002969296969786490399/1024)*y^14+
    (350249683977929583797321241/256)*y^15+(52856430502952134902727413/64)*y^16+(56420609017661702586319923/128)*y^17+
    (13306021597836988576698663/64)*y^18+(1384664906267936886187899/16)*y^19+(253708974997061236411869/8)*y^20+
    (40781033052359698188063/4)*y^21+(22891888988441303827797/8)*y^22+(1393460938024037275545/2)*y^23+
    (145953189487990653714)*y^24+(26021377372028465547)*y^25+(3892209828844085190)*y^26+
    (479089069751214504)*y^27+(47234407851478656)*y^28+(3584618003916144)*y^29+
    (196488958170240)*y^30+(6920535241728)*y^31+(117546246144)*y^32

private theorem nextCacheP_eq (y : ℝ) : atomGapPolyEval atomGapPairCoeff y=nextCacheP y := by
  norm_num [atomGapPolyEval,atomGapPairCoeff,nextCacheP,Finset.sum_range_succ]

private def nextCachePJet (y : ℝ) : ℝ :=
  (17029102555455663849163083/131072)*(1:ℝ)*y^(1-1)+(322103250906652692527224995/262144)*(2:ℝ)*y^(2-1)+(3986068609578601786146770907/524288)*(3:ℝ)*y^(3-1)+
    (17747426224968762775188708801/524288)*(4:ℝ)*y^(4-1)+(60205290770051699808697176159/524288)*(5:ℝ)*y^(5-1)+(161889339980151795383364100185/524288)*(6:ℝ)*y^(6-1)+
    (88783224129787319215420379949/131072)*(7:ℝ)*y^(7-1)+(40584482588850241239154879101/32768)*(8:ℝ)*y^(8-1)+(125732997201449447835433962975/65536)*(9:ℝ)*y^(9-1)+
    (83526071203783400209001293023/32768)*(10:ℝ)*y^(10-1)+(24021870812074579694285775753/8192)*(11:ℝ)*y^(11-1)+(3012388545381711954421912695/1024)*(12:ℝ)*y^(12-1)+
    (10598204705085701542133692191/4096)*(13:ℝ)*y^(13-1)+(2051032002969296969786490399/1024)*(14:ℝ)*y^(14-1)+(350249683977929583797321241/256)*(15:ℝ)*y^(15-1)+
    (52856430502952134902727413/64)*(16:ℝ)*y^(16-1)+(56420609017661702586319923/128)*(17:ℝ)*y^(17-1)+(13306021597836988576698663/64)*(18:ℝ)*y^(18-1)+
    (1384664906267936886187899/16)*(19:ℝ)*y^(19-1)+(253708974997061236411869/8)*(20:ℝ)*y^(20-1)+(40781033052359698188063/4)*(21:ℝ)*y^(21-1)+
    (22891888988441303827797/8)*(22:ℝ)*y^(22-1)+(1393460938024037275545/2)*(23:ℝ)*y^(23-1)+(145953189487990653714)*(24:ℝ)*y^(24-1)+
    (26021377372028465547)*(25:ℝ)*y^(25-1)+(3892209828844085190)*(26:ℝ)*y^(26-1)+(479089069751214504)*(27:ℝ)*y^(27-1)+
    (47234407851478656)*(28:ℝ)*y^(28-1)+(3584618003916144)*(29:ℝ)*y^(29-1)+(196488958170240)*(30:ℝ)*y^(30-1)+
    (6920535241728)*(31:ℝ)*y^(31-1)+(117546246144)*(32:ℝ)*y^(32-1)

private theorem nextCachePJet_eq (y : ℝ) : atomGapPolyJet atomGapPairCoeff y=nextCachePJet y := by
  norm_num [atomGapPolyJet,atomGapPairCoeff,nextCachePJet,Finset.sum_range_succ]

private def nextCache0 (y : ℝ) : ℝ :=
  (871843089673660138155/8192)*y^0+(11755755193381178703723/8192)*y^1+(69643378780465370858919/8192)*y^2+
    (263011842824181390520695/8192)*y^3+(369657663453124200345645/4096)*y^4+(828688736570439470854383/4096)*y^5+
    (3037295495998622908798353/8192)*y^6+(4578605460227228305516479/8192)*y^7+(5688857469609798148549737/8192)*y^8+
    (5840668421868441577524705/8192)*y^9+(2485729081649937039046785/4096)*y^10+(439917689376217225298457/1024)*y^11+
    (8111244133624688581203/32)*y^12+(63854298094323777543855/512)*y^13+(13079383738637389295355/256)*y^14+
    (555396085271268257787/32)*y^15+(155336723682162420357/32)*y^16+(35372477391523111791/32)*y^17+
    (3224973962940749847/16)*y^18+(114848258396203665/4)*y^19+(3076499258720361)*y^20+
    (466116825510081/2)*y^21+(11119355454789)*y^22+(251048476872)*y^23

private theorem nextCache0_eq (y : ℝ) : pairKernelShiftValue 0 y=nextCache0 y := by
  norm_num [pairKernelShiftValue,atomGapPolyEval,pairKernelShiftCoeff,nextCache0,Finset.sum_range_succ]

private def nextCache0Jet (y : ℝ) : ℝ :=
  (11755755193381178703723/8192)*(1:ℝ)*y^(1-1)+(69643378780465370858919/8192)*(2:ℝ)*y^(2-1)+(263011842824181390520695/8192)*(3:ℝ)*y^(3-1)+
    (369657663453124200345645/4096)*(4:ℝ)*y^(4-1)+(828688736570439470854383/4096)*(5:ℝ)*y^(5-1)+(3037295495998622908798353/8192)*(6:ℝ)*y^(6-1)+
    (4578605460227228305516479/8192)*(7:ℝ)*y^(7-1)+(5688857469609798148549737/8192)*(8:ℝ)*y^(8-1)+(5840668421868441577524705/8192)*(9:ℝ)*y^(9-1)+
    (2485729081649937039046785/4096)*(10:ℝ)*y^(10-1)+(439917689376217225298457/1024)*(11:ℝ)*y^(11-1)+(8111244133624688581203/32)*(12:ℝ)*y^(12-1)+
    (63854298094323777543855/512)*(13:ℝ)*y^(13-1)+(13079383738637389295355/256)*(14:ℝ)*y^(14-1)+(555396085271268257787/32)*(15:ℝ)*y^(15-1)+
    (155336723682162420357/32)*(16:ℝ)*y^(16-1)+(35372477391523111791/32)*(17:ℝ)*y^(17-1)+(3224973962940749847/16)*(18:ℝ)*y^(18-1)+
    (114848258396203665/4)*(19:ℝ)*y^(19-1)+(3076499258720361)*(20:ℝ)*y^(20-1)+(466116825510081/2)*(21:ℝ)*y^(21-1)+
    (11119355454789)*(22:ℝ)*y^(22-1)+(251048476872)*(23:ℝ)*y^(23-1)

private theorem nextCache0Jet_eq (y : ℝ) : pairKernelShiftJet 0 y=nextCache0Jet y := by
  norm_num [pairKernelShiftJet,atomGapPolyJet,pairKernelShiftCoeff,nextCache0Jet,Finset.sum_range_succ]

private def nextCache1 (y : ℝ) : ℝ :=
  (6645960427801621029885/32768)*y^0+(4428481157486486438409/2048)*y^1+(181174146917816943107631/16384)*y^2+
    (619098593820954748087563/16384)*y^3+(1631318687532587774125881/16384)*y^4+(880968583850366324509137/4096)*y^5+
    (6335518165264275578000937/16384)*y^6+(9457687798826244189854283/16384)*y^7+(23364329902920532267694181/32768)*y^8+
    (5969014782499911872916891/8192)*y^9+(5057666384337426221685351/8192)*y^10+(445417210135813617779121/1024)*y^11+
    (522960759804816502529373/2048)*y^12+(63986708932952312122029/512)*y^13+(26069328264687109054407/512)*y^14+
    (550380859092823986279/32)*y^15+(612198405676279216935/128)*y^16+(34648172398989922725/32)*y^17+
    (6280484930133442317/32)*y^18+(111161122559983413/4)*y^19+(23677717407015159/8)*y^20+
    (445686593443155/2)*y^21+(21133400254461/2)*y^22+(237101339268)*y^23

private theorem nextCache1_eq (y : ℝ) : pairKernelShiftValue 1 y=nextCache1 y := by
  norm_num [pairKernelShiftValue,atomGapPolyEval,pairKernelShiftCoeff,nextCache1,Finset.sum_range_succ]

private def nextCache1Jet (y : ℝ) : ℝ :=
  (4428481157486486438409/2048)*(1:ℝ)*y^(1-1)+(181174146917816943107631/16384)*(2:ℝ)*y^(2-1)+(619098593820954748087563/16384)*(3:ℝ)*y^(3-1)+
    (1631318687532587774125881/16384)*(4:ℝ)*y^(4-1)+(880968583850366324509137/4096)*(5:ℝ)*y^(5-1)+(6335518165264275578000937/16384)*(6:ℝ)*y^(6-1)+
    (9457687798826244189854283/16384)*(7:ℝ)*y^(7-1)+(23364329902920532267694181/32768)*(8:ℝ)*y^(8-1)+(5969014782499911872916891/8192)*(9:ℝ)*y^(9-1)+
    (5057666384337426221685351/8192)*(10:ℝ)*y^(10-1)+(445417210135813617779121/1024)*(11:ℝ)*y^(11-1)+(522960759804816502529373/2048)*(12:ℝ)*y^(12-1)+
    (63986708932952312122029/512)*(13:ℝ)*y^(13-1)+(26069328264687109054407/512)*(14:ℝ)*y^(14-1)+(550380859092823986279/32)*(15:ℝ)*y^(15-1)+
    (612198405676279216935/128)*(16:ℝ)*y^(16-1)+(34648172398989922725/32)*(17:ℝ)*y^(17-1)+(6280484930133442317/32)*(18:ℝ)*y^(18-1)+
    (111161122559983413/4)*(19:ℝ)*y^(19-1)+(23677717407015159/8)*(20:ℝ)*y^(20-1)+(445686593443155/2)*(21:ℝ)*y^(21-1)+
    (21133400254461/2)*(22:ℝ)*y^(22-1)+(237101339268)*(23:ℝ)*y^(23-1)

private theorem nextCache1Jet_eq (y : ℝ) : pairKernelShiftJet 1 y=nextCache1Jet y := by
  norm_num [pairKernelShiftJet,atomGapPolyJet,pairKernelShiftCoeff,nextCache1Jet,Finset.sum_range_succ]

private def nextCache2 (y : ℝ) : ℝ :=
  (4371672074476391318475/32768)*y^0+(20827323377633415369897/16384)*y^1+(194521797505410772684815/32768)*y^2+
    (617856941833082618735691/32768)*y^3+(193095340975878705276507/4096)*y^4+(202086513922137766430859/2048)*y^5+
    (5720787331406529685409151/32768)*y^6+(8474055878945399423919435/32768)*y^7+(10420477627187722931313363/32768)*y^8+
    (663116158272662075719521/2048)*y^9+(2238986630136741268431429/8192)*y^10+(392716045272626599549959/2048)*y^11+
    (229484097647738252528211/2048)*y^12+(13969941529271194954881/256)*y^13+(11323917090678738528117/512)*y^14+
    (951104991895889859279/128)*y^15+(263002857837570792081/128)*y^16+(924973339637082339/2)*y^17+
    (2666911618420789671/32)*y^18+(93841958400350625/8)*y^19+(9933678145161801/8)*y^20+
    (92915701577685)*y^21+(8756865312867/2)*y^22+(97629963228)*y^23

private theorem nextCache2_eq (y : ℝ) : pairKernelShiftValue 2 y=nextCache2 y := by
  norm_num [pairKernelShiftValue,atomGapPolyEval,pairKernelShiftCoeff,nextCache2,Finset.sum_range_succ]

private def nextCache2Jet (y : ℝ) : ℝ :=
  (20827323377633415369897/16384)*(1:ℝ)*y^(1-1)+(194521797505410772684815/32768)*(2:ℝ)*y^(2-1)+(617856941833082618735691/32768)*(3:ℝ)*y^(3-1)+
    (193095340975878705276507/4096)*(4:ℝ)*y^(4-1)+(202086513922137766430859/2048)*(5:ℝ)*y^(5-1)+(5720787331406529685409151/32768)*(6:ℝ)*y^(6-1)+
    (8474055878945399423919435/32768)*(7:ℝ)*y^(7-1)+(10420477627187722931313363/32768)*(8:ℝ)*y^(8-1)+(663116158272662075719521/2048)*(9:ℝ)*y^(9-1)+
    (2238986630136741268431429/8192)*(10:ℝ)*y^(10-1)+(392716045272626599549959/2048)*(11:ℝ)*y^(11-1)+(229484097647738252528211/2048)*(12:ℝ)*y^(12-1)+
    (13969941529271194954881/256)*(13:ℝ)*y^(13-1)+(11323917090678738528117/512)*(14:ℝ)*y^(14-1)+(951104991895889859279/128)*(15:ℝ)*y^(15-1)+
    (263002857837570792081/128)*(16:ℝ)*y^(16-1)+(924973339637082339/2)*(17:ℝ)*y^(17-1)+(2666911618420789671/32)*(18:ℝ)*y^(18-1)+
    (93841958400350625/8)*(19:ℝ)*y^(19-1)+(9933678145161801/8)*(20:ℝ)*y^(20-1)+(92915701577685)*(21:ℝ)*y^(21-1)+
    (8756865312867/2)*(22:ℝ)*y^(22-1)+(97629963228)*(23:ℝ)*y^(23-1)

private theorem nextCache2Jet_eq (y : ℝ) : pairKernelShiftJet 2 y=nextCache2Jet y := by
  norm_num [pairKernelShiftJet,atomGapPolyJet,pairKernelShiftCoeff,nextCache2Jet,Finset.sum_range_succ]

private def nextCache3 (y : ℝ) : ℝ :=
  (1468791510391541722545/32768)*y^0+(13072190958811340043705/32768)*y^1+(57311315645929698712167/32768)*y^2+
    (86000695426696014012069/16384)*y^3+(51436226427671786554359/4096)*y^4+(838030023002429831077281/32768)*y^5+
    (1462578878833471202961663/32768)*y^6+(67285856970639524239119/1024)*y^7+(2638849969001171066711373/32768)*y^8+
    (669800725759768932577845/8192)*y^9+(563601950197975277337015/8192)*y^10+(24622518251766810308535/512)*y^11+
    (57311085448434812347989/2048)*y^12+(6945435172451364231879/512)*y^13+(2801004680153099899791/512)*y^14+
    (117014739419895381081/64)*y^15+(64362276160766307711/128)*y^16+(3601368484946842995/32)*y^17+
    (645213290357490813/32)*y^18+(2821074930194193)*y^19+(2374508315391327/8)*y^20+
    (44145756399789/2)*y^21+(2067203984769/2)*y^22+(22900855572)*y^23

private theorem nextCache3_eq (y : ℝ) : pairKernelShiftValue 3 y=nextCache3 y := by
  norm_num [pairKernelShiftValue,atomGapPolyEval,pairKernelShiftCoeff,nextCache3,Finset.sum_range_succ]

private def nextCache3Jet (y : ℝ) : ℝ :=
  (13072190958811340043705/32768)*(1:ℝ)*y^(1-1)+(57311315645929698712167/32768)*(2:ℝ)*y^(2-1)+(86000695426696014012069/16384)*(3:ℝ)*y^(3-1)+
    (51436226427671786554359/4096)*(4:ℝ)*y^(4-1)+(838030023002429831077281/32768)*(5:ℝ)*y^(5-1)+(1462578878833471202961663/32768)*(6:ℝ)*y^(6-1)+
    (67285856970639524239119/1024)*(7:ℝ)*y^(7-1)+(2638849969001171066711373/32768)*(8:ℝ)*y^(8-1)+(669800725759768932577845/8192)*(9:ℝ)*y^(9-1)+
    (563601950197975277337015/8192)*(10:ℝ)*y^(10-1)+(24622518251766810308535/512)*(11:ℝ)*y^(11-1)+(57311085448434812347989/2048)*(12:ℝ)*y^(12-1)+
    (6945435172451364231879/512)*(13:ℝ)*y^(13-1)+(2801004680153099899791/512)*(14:ℝ)*y^(14-1)+(117014739419895381081/64)*(15:ℝ)*y^(15-1)+
    (64362276160766307711/128)*(16:ℝ)*y^(16-1)+(3601368484946842995/32)*(17:ℝ)*y^(17-1)+(645213290357490813/32)*(18:ℝ)*y^(18-1)+
    (2821074930194193)*(19:ℝ)*y^(19-1)+(2374508315391327/8)*(20:ℝ)*y^(20-1)+(44145756399789/2)*(21:ℝ)*y^(21-1)+
    (2067203984769/2)*(22:ℝ)*y^(22-1)+(22900855572)*(23:ℝ)*y^(23-1)

private theorem nextCache3Jet_eq (y : ℝ) : pairKernelShiftJet 3 y=nextCache3Jet y := by
  norm_num [pairKernelShiftJet,atomGapPolyJet,pairKernelShiftCoeff,nextCache3Jet,Finset.sum_range_succ]

private def nextCache4 (y : ℝ) : ℝ :=
  (288260170974765132975/32768)*y^0+(2448550125510930945135/32768)*y^1+(1280202036699810601665/4096)*y^2+
    (29361400386039029068875/32768)*y^3+(33814976200004470039245/16384)*y^4+(134435925768999831610185/32768)*y^5+
    (28983287025965148261165/4096)*y^6+(339670438433120731054725/32768)*y^7+(415275036572088491884155/32768)*y^8+
    (13147310796916070157885/1024)*y^9+(88268222631310971917265/8192)*y^10+(15374423172848854125645/2048)*y^11+
    (8911830214398849080355/2048)*y^12+(537663763467979893585/256)*y^13+(431618254139768918625/512)*y^14+
    (35880989104348495605/128)*y^15+(9815652859339019385/128)*y^16+(136549942025481405/8)*y^17+
    (97296473680276635/32)*y^18+(3383223747235515/8)*y^19+(353803638897225/8)*y^20+
    (3268497667455)*y^21+(304172913555/2)*y^22+(3348078300)*y^23

private theorem nextCache4_eq (y : ℝ) : pairKernelShiftValue 4 y=nextCache4 y := by
  norm_num [pairKernelShiftValue,atomGapPolyEval,pairKernelShiftCoeff,nextCache4,Finset.sum_range_succ]

private def nextCache4Jet (y : ℝ) : ℝ :=
  (2448550125510930945135/32768)*(1:ℝ)*y^(1-1)+(1280202036699810601665/4096)*(2:ℝ)*y^(2-1)+(29361400386039029068875/32768)*(3:ℝ)*y^(3-1)+
    (33814976200004470039245/16384)*(4:ℝ)*y^(4-1)+(134435925768999831610185/32768)*(5:ℝ)*y^(5-1)+(28983287025965148261165/4096)*(6:ℝ)*y^(6-1)+
    (339670438433120731054725/32768)*(7:ℝ)*y^(7-1)+(415275036572088491884155/32768)*(8:ℝ)*y^(8-1)+(13147310796916070157885/1024)*(9:ℝ)*y^(9-1)+
    (88268222631310971917265/8192)*(10:ℝ)*y^(10-1)+(15374423172848854125645/2048)*(11:ℝ)*y^(11-1)+(8911830214398849080355/2048)*(12:ℝ)*y^(12-1)+
    (537663763467979893585/256)*(13:ℝ)*y^(13-1)+(431618254139768918625/512)*(14:ℝ)*y^(14-1)+(35880989104348495605/128)*(15:ℝ)*y^(15-1)+
    (9815652859339019385/128)*(16:ℝ)*y^(16-1)+(136549942025481405/8)*(17:ℝ)*y^(17-1)+(97296473680276635/32)*(18:ℝ)*y^(18-1)+
    (3383223747235515/8)*(19:ℝ)*y^(19-1)+(353803638897225/8)*(20:ℝ)*y^(20-1)+(3268497667455)*(21:ℝ)*y^(21-1)+
    (304172913555/2)*(22:ℝ)*y^(22-1)+(3348078300)*(23:ℝ)*y^(23-1)

private theorem nextCache4Jet_eq (y : ℝ) : pairKernelShiftJet 4 y=nextCache4Jet y := by
  norm_num [pairKernelShiftJet,atomGapPolyJet,pairKernelShiftCoeff,nextCache4Jet,Finset.sum_range_succ]

private def nextCache5 (y : ℝ) : ℝ :=
  (34572140477077535055/32768)*y^0+(141893845138595927619/16384)*y^1+(143030679942947054553/4096)*y^2+
    (1579034227738736833335/16384)*y^3+(3518361383844332934675/16384)*y^4+(6843403824644506459473/16384)*y^5+
    (1460177455170521903283/2048)*y^6+(17046013405623640328007/16384)*y^7+(41609071350853987801527/32768)*y^8+
    (10521550087483973363685/8192)*y^9+(8810443374259976630685/8192)*y^10+(765056442173735268153/1024)*y^11+
    (883783788287881910463/2048)*y^12+(106205197938927541515/512)*y^13+(42437019635002146285/512)*y^14+
    (438840426837632499/16)*y^15+(955453255615549197/128)*y^16+(52879538780156619/32)*y^17+
    (9366541757957151/32)*y^18+(161896936927185/4)*y^19+(33656901215517/8)*y^20+
    (618003350109/2)*y^21+(28573988247/2)*y^22+(312487308)*y^23

private theorem nextCache5_eq (y : ℝ) : pairKernelShiftValue 5 y=nextCache5 y := by
  norm_num [pairKernelShiftValue,atomGapPolyEval,pairKernelShiftCoeff,nextCache5,Finset.sum_range_succ]

private def nextCache5Jet (y : ℝ) : ℝ :=
  (141893845138595927619/16384)*(1:ℝ)*y^(1-1)+(143030679942947054553/4096)*(2:ℝ)*y^(2-1)+(1579034227738736833335/16384)*(3:ℝ)*y^(3-1)+
    (3518361383844332934675/16384)*(4:ℝ)*y^(4-1)+(6843403824644506459473/16384)*(5:ℝ)*y^(5-1)+(1460177455170521903283/2048)*(6:ℝ)*y^(6-1)+
    (17046013405623640328007/16384)*(7:ℝ)*y^(7-1)+(41609071350853987801527/32768)*(8:ℝ)*y^(8-1)+(10521550087483973363685/8192)*(9:ℝ)*y^(9-1)+
    (8810443374259976630685/8192)*(10:ℝ)*y^(10-1)+(765056442173735268153/1024)*(11:ℝ)*y^(11-1)+(883783788287881910463/2048)*(12:ℝ)*y^(12-1)+
    (106205197938927541515/512)*(13:ℝ)*y^(13-1)+(42437019635002146285/512)*(14:ℝ)*y^(14-1)+(438840426837632499/16)*(15:ℝ)*y^(15-1)+
    (955453255615549197/128)*(16:ℝ)*y^(16-1)+(52879538780156619/32)*(17:ℝ)*y^(17-1)+(9366541757957151/32)*(18:ℝ)*y^(18-1)+
    (161896936927185/4)*(19:ℝ)*y^(19-1)+(33656901215517/8)*(20:ℝ)*y^(20-1)+(618003350109/2)*(21:ℝ)*y^(21-1)+
    (28573988247/2)*(22:ℝ)*y^(22-1)+(312487308)*(23:ℝ)*y^(23-1)

private theorem nextCache5Jet_eq (y : ℝ) : pairKernelShiftJet 5 y=nextCache5Jet y := by
  norm_num [pairKernelShiftJet,atomGapPolyJet,pairKernelShiftCoeff,nextCache5Jet,Finset.sum_range_succ]

private def nextCache6 (y : ℝ) : ℝ :=
  (2504601395362738665/32768)*y^0+(5006889166317253389/8192)*y^1+(78404646487608605763/32768)*y^2+
    (209538512940494542869/32768)*y^3+(56667342213234173961/4096)*y^4+(432265802931071213337/16384)*y^5+
    (1462251641422138857711/32768)*y^6+(2127240427885706874789/32768)*y^7+(2593415484420983332929/32768)*y^8+
    (40939701184675931499/512)*y^9+(547500729976980468039/8192)*y^10+(94837086420639234633/2048)*y^11+
    (54597606781534868097/2048)*y^12+(3267927103761897093/256)*y^13+(2600343083587115943/512)*y^14+
    (214114091904277209/128)*y^15+(57980084274994635/128)*y^16+(797981965220655/8)*y^17+
    (562248998655453/32)*y^18+(19324138837599/8)*y^19+(1996617610611/8)*y^20+
    (18217436625)*y^21+(1673901369/2)*y^22+(18187092)*y^23

private theorem nextCache6_eq (y : ℝ) : pairKernelShiftValue 6 y=nextCache6 y := by
  norm_num [pairKernelShiftValue,atomGapPolyEval,pairKernelShiftCoeff,nextCache6,Finset.sum_range_succ]

private def nextCache6Jet (y : ℝ) : ℝ :=
  (5006889166317253389/8192)*(1:ℝ)*y^(1-1)+(78404646487608605763/32768)*(2:ℝ)*y^(2-1)+(209538512940494542869/32768)*(3:ℝ)*y^(3-1)+
    (56667342213234173961/4096)*(4:ℝ)*y^(4-1)+(432265802931071213337/16384)*(5:ℝ)*y^(5-1)+(1462251641422138857711/32768)*(6:ℝ)*y^(6-1)+
    (2127240427885706874789/32768)*(7:ℝ)*y^(7-1)+(2593415484420983332929/32768)*(8:ℝ)*y^(8-1)+(40939701184675931499/512)*(9:ℝ)*y^(9-1)+
    (547500729976980468039/8192)*(10:ℝ)*y^(10-1)+(94837086420639234633/2048)*(11:ℝ)*y^(11-1)+(54597606781534868097/2048)*(12:ℝ)*y^(12-1)+
    (3267927103761897093/256)*(13:ℝ)*y^(13-1)+(2600343083587115943/512)*(14:ℝ)*y^(14-1)+(214114091904277209/128)*(15:ℝ)*y^(15-1)+
    (57980084274994635/128)*(16:ℝ)*y^(16-1)+(797981965220655/8)*(17:ℝ)*y^(17-1)+(562248998655453/32)*(18:ℝ)*y^(18-1)+
    (19324138837599/8)*(19:ℝ)*y^(19-1)+(1996617610611/8)*(20:ℝ)*y^(20-1)+(18217436625)*(21:ℝ)*y^(21-1)+
    (1673901369/2)*(22:ℝ)*y^(22-1)+(18187092)*(23:ℝ)*y^(23-1)

private theorem nextCache6Jet_eq (y : ℝ) : pairKernelShiftJet 6 y=nextCache6Jet y := by
  norm_num [pairKernelShiftJet,atomGapPolyJet,pairKernelShiftCoeff,nextCache6Jet,Finset.sum_range_succ]

private def nextCache7 (y : ℝ) : ℝ :=
  (100969866836107875/32768)*y^0+(790897546169291601/32768)*y^1+(3022121252711642355/32768)*y^2+
    (3928136789006649297/16384)*y^3+(517317184313143497/1024)*y^4+(31003298334069594021/32768)*y^5+
    (52010358662209520079/32768)*y^6+(18870694403729612535/8192)*y^7+(91969063372141325847/32768)*y^8+
    (23211500857496945451/8192)*y^9+(19371517997181987141/8192)*y^10+(209230437704191011/128)*y^11+
    (1921407606862938639/2048)*y^12+(229177503401424993/512)*y^13+(90805670659027773/512)*y^14+
    (3721626198029853/64)*y^15+(2005756592950989/128)*y^16+(109849602995901/32)*y^17+
    (19244084305239/32)*y^18+(164406642435/2)*y^19+(67543206669/8)*y^20+
    (1224949635/2)*y^21+(55919403/2)*y^22+(603612)*y^23

private theorem nextCache7_eq (y : ℝ) : pairKernelShiftValue 7 y=nextCache7 y := by
  norm_num [pairKernelShiftValue,atomGapPolyEval,pairKernelShiftCoeff,nextCache7,Finset.sum_range_succ]

private def nextCache7Jet (y : ℝ) : ℝ :=
  (790897546169291601/32768)*(1:ℝ)*y^(1-1)+(3022121252711642355/32768)*(2:ℝ)*y^(2-1)+(3928136789006649297/16384)*(3:ℝ)*y^(3-1)+
    (517317184313143497/1024)*(4:ℝ)*y^(4-1)+(31003298334069594021/32768)*(5:ℝ)*y^(5-1)+(52010358662209520079/32768)*(6:ℝ)*y^(6-1)+
    (18870694403729612535/8192)*(7:ℝ)*y^(7-1)+(91969063372141325847/32768)*(8:ℝ)*y^(8-1)+(23211500857496945451/8192)*(9:ℝ)*y^(9-1)+
    (19371517997181987141/8192)*(10:ℝ)*y^(10-1)+(209230437704191011/128)*(11:ℝ)*y^(11-1)+(1921407606862938639/2048)*(12:ℝ)*y^(12-1)+
    (229177503401424993/512)*(13:ℝ)*y^(13-1)+(90805670659027773/512)*(14:ℝ)*y^(14-1)+(3721626198029853/64)*(15:ℝ)*y^(15-1)+
    (2005756592950989/128)*(16:ℝ)*y^(16-1)+(109849602995901/32)*(17:ℝ)*y^(17-1)+(19244084305239/32)*(18:ℝ)*y^(18-1)+
    (164406642435/2)*(19:ℝ)*y^(19-1)+(67543206669/8)*(20:ℝ)*y^(20-1)+(1224949635/2)*(21:ℝ)*y^(21-1)+
    (55919403/2)*(22:ℝ)*y^(22-1)+(603612)*(23:ℝ)*y^(23-1)

private theorem nextCache7Jet_eq (y : ℝ) : pairKernelShiftJet 7 y=nextCache7Jet y := by
  norm_num [pairKernelShiftJet,atomGapPolyJet,pairKernelShiftCoeff,nextCache7Jet,Finset.sum_range_succ]

private def nextCache8 (y : ℝ) : ℝ :=
  (1743060955981905/32768)*y^0+(13429472157905535/32768)*y^1+(25144977088871109/16384)*y^2+
    (127626942348481257/32768)*y^3+(131290898242888359/16384)*y^4+(483624814568950989/32768)*y^5+
    (402671318386927131/16384)*y^6+(1166668501931690607/32768)*y^7+(1421220415520473677/32768)*y^8+
    (358536894709954275/8192)*y^9+(298850653349369505/8192)*y^10+(51538195984595985/2048)*y^11+
    (29497107305287881/2048)*y^12+(3506251324276611/512)*y^13+(1383805760942349/512)*y^14+
    (112935154149783/128)*y^15+(30289069215639/128)*y^16+(1650447892305/32)*y^17+
    (287583183027/32)*y^18+(9772064451/8)*y^19+(997738803/8)*y^20+
    (17983701/2)*y^21+(815751/2)*y^22+(8748)*y^23

private theorem nextCache8_eq (y : ℝ) : pairKernelShiftValue 8 y=nextCache8 y := by
  norm_num [pairKernelShiftValue,atomGapPolyEval,pairKernelShiftCoeff,nextCache8,Finset.sum_range_succ]

private def nextCache8Jet (y : ℝ) : ℝ :=
  (13429472157905535/32768)*(1:ℝ)*y^(1-1)+(25144977088871109/16384)*(2:ℝ)*y^(2-1)+(127626942348481257/32768)*(3:ℝ)*y^(3-1)+
    (131290898242888359/16384)*(4:ℝ)*y^(4-1)+(483624814568950989/32768)*(5:ℝ)*y^(5-1)+(402671318386927131/16384)*(6:ℝ)*y^(6-1)+
    (1166668501931690607/32768)*(7:ℝ)*y^(7-1)+(1421220415520473677/32768)*(8:ℝ)*y^(8-1)+(358536894709954275/8192)*(9:ℝ)*y^(9-1)+
    (298850653349369505/8192)*(10:ℝ)*y^(10-1)+(51538195984595985/2048)*(11:ℝ)*y^(11-1)+(29497107305287881/2048)*(12:ℝ)*y^(12-1)+
    (3506251324276611/512)*(13:ℝ)*y^(13-1)+(1383805760942349/512)*(14:ℝ)*y^(14-1)+(112935154149783/128)*(15:ℝ)*y^(15-1)+
    (30289069215639/128)*(16:ℝ)*y^(16-1)+(1650447892305/32)*(17:ℝ)*y^(17-1)+(287583183027/32)*(18:ℝ)*y^(18-1)+
    (9772064451/8)*(19:ℝ)*y^(19-1)+(997738803/8)*(20:ℝ)*y^(20-1)+(17983701/2)*(21:ℝ)*y^(21-1)+
    (815751/2)*(22:ℝ)*y^(22-1)+(8748)*(23:ℝ)*y^(23-1)

private theorem nextCache8Jet_eq (y : ℝ) : pairKernelShiftJet 8 y=nextCache8Jet y := by
  norm_num [pairKernelShiftJet,atomGapPolyJet,pairKernelShiftCoeff,nextCache8Jet,Finset.sum_range_succ]


def pairRelativeMonomialReserve (k : ℕ) (y : ℝ) : ℝ :=
  pairRelativeShiftCoeff 9 y*(Nat.choose 9 k:ℝ)*9^(9-k)-pairRelativeShiftCoeff k y

theorem pairRelativeMonomialReserve_0_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < pairRelativeMonomialReserve 0 y := by
  unfold pairRelativeMonomialReserve pairRelativeShiftCoeff
  norm_num only [Nat.reduceSub,Nat.choose,OfNat.zero_ne_ofNat,ite_false,ite_true,
    pairKernelShiftValue_nine,pairKernelShiftJet_nine,mul_zero,zero_mul,zero_add,add_zero,sub_zero]
  rw [nextCacheP_eq,nextCachePJet_eq,nextCache8_eq,nextCache0_eq,nextCache0Jet_eq]
  unfold nextCacheP nextCachePJet nextCache8 nextCache0 nextCache0Jet
  norm_num only [Nat.reduceSub,Nat.cast_ofNat]
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,
    Mathlib.Tactic.RingNF.nat_rawCast_1,Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

theorem pairRelativeMonomialReserve_1_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < pairRelativeMonomialReserve 1 y := by
  unfold pairRelativeMonomialReserve pairRelativeShiftCoeff
  norm_num only [Nat.reduceSub,Nat.choose,OfNat.zero_ne_ofNat,ite_false,ite_true,
    pairKernelShiftValue_nine,pairKernelShiftJet_nine,mul_zero,zero_mul,zero_add,add_zero,sub_zero]
  rw [nextCacheP_eq,nextCachePJet_eq,nextCache8_eq,nextCache1_eq,nextCache1Jet_eq,nextCache0_eq]
  unfold nextCacheP nextCachePJet nextCache8 nextCache1 nextCache1Jet nextCache0
  norm_num only [Nat.reduceSub,Nat.cast_ofNat]
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,
    Mathlib.Tactic.RingNF.nat_rawCast_1,Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

theorem pairRelativeMonomialReserve_2_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < pairRelativeMonomialReserve 2 y := by
  unfold pairRelativeMonomialReserve pairRelativeShiftCoeff
  norm_num only [Nat.reduceSub,Nat.choose,OfNat.zero_ne_ofNat,ite_false,ite_true,
    pairKernelShiftValue_nine,pairKernelShiftJet_nine,mul_zero,zero_mul,zero_add,add_zero,sub_zero]
  rw [nextCacheP_eq,nextCachePJet_eq,nextCache8_eq,nextCache2_eq,nextCache2Jet_eq,nextCache1_eq]
  unfold nextCacheP nextCachePJet nextCache8 nextCache2 nextCache2Jet nextCache1
  norm_num only [Nat.reduceSub,Nat.cast_ofNat]
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,
    Mathlib.Tactic.RingNF.nat_rawCast_1,Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

theorem pairRelativeMonomialReserve_3_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < pairRelativeMonomialReserve 3 y := by
  unfold pairRelativeMonomialReserve pairRelativeShiftCoeff
  norm_num only [Nat.reduceSub,Nat.choose,OfNat.zero_ne_ofNat,ite_false,ite_true,
    pairKernelShiftValue_nine,pairKernelShiftJet_nine,mul_zero,zero_mul,zero_add,add_zero,sub_zero]
  rw [nextCacheP_eq,nextCachePJet_eq,nextCache8_eq,nextCache3_eq,nextCache3Jet_eq,nextCache2_eq]
  unfold nextCacheP nextCachePJet nextCache8 nextCache3 nextCache3Jet nextCache2
  norm_num only [Nat.reduceSub,Nat.cast_ofNat]
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,
    Mathlib.Tactic.RingNF.nat_rawCast_1,Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

theorem pairRelativeMonomialReserve_4_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < pairRelativeMonomialReserve 4 y := by
  unfold pairRelativeMonomialReserve pairRelativeShiftCoeff
  norm_num only [Nat.reduceSub,Nat.choose,OfNat.zero_ne_ofNat,ite_false,ite_true,
    pairKernelShiftValue_nine,pairKernelShiftJet_nine,mul_zero,zero_mul,zero_add,add_zero,sub_zero]
  rw [nextCacheP_eq,nextCachePJet_eq,nextCache8_eq,nextCache4_eq,nextCache4Jet_eq,nextCache3_eq]
  unfold nextCacheP nextCachePJet nextCache8 nextCache4 nextCache4Jet nextCache3
  norm_num only [Nat.reduceSub,Nat.cast_ofNat]
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,
    Mathlib.Tactic.RingNF.nat_rawCast_1,Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

theorem pairRelativeMonomialReserve_5_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < pairRelativeMonomialReserve 5 y := by
  unfold pairRelativeMonomialReserve pairRelativeShiftCoeff
  norm_num only [Nat.reduceSub,Nat.choose,OfNat.zero_ne_ofNat,ite_false,ite_true,
    pairKernelShiftValue_nine,pairKernelShiftJet_nine,mul_zero,zero_mul,zero_add,add_zero,sub_zero]
  rw [nextCacheP_eq,nextCachePJet_eq,nextCache8_eq,nextCache5_eq,nextCache5Jet_eq,nextCache4_eq]
  unfold nextCacheP nextCachePJet nextCache8 nextCache5 nextCache5Jet nextCache4
  norm_num only [Nat.reduceSub,Nat.cast_ofNat]
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,
    Mathlib.Tactic.RingNF.nat_rawCast_1,Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

theorem pairRelativeMonomialReserve_6_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < pairRelativeMonomialReserve 6 y := by
  unfold pairRelativeMonomialReserve pairRelativeShiftCoeff
  norm_num only [Nat.reduceSub,Nat.choose,OfNat.zero_ne_ofNat,ite_false,ite_true,
    pairKernelShiftValue_nine,pairKernelShiftJet_nine,mul_zero,zero_mul,zero_add,add_zero,sub_zero]
  rw [nextCacheP_eq,nextCachePJet_eq,nextCache8_eq,nextCache6_eq,nextCache6Jet_eq,nextCache5_eq]
  unfold nextCacheP nextCachePJet nextCache8 nextCache6 nextCache6Jet nextCache5
  norm_num only [Nat.reduceSub,Nat.cast_ofNat]
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,
    Mathlib.Tactic.RingNF.nat_rawCast_1,Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

theorem pairRelativeMonomialReserve_7_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < pairRelativeMonomialReserve 7 y := by
  unfold pairRelativeMonomialReserve pairRelativeShiftCoeff
  norm_num only [Nat.reduceSub,Nat.choose,OfNat.zero_ne_ofNat,ite_false,ite_true,
    pairKernelShiftValue_nine,pairKernelShiftJet_nine,mul_zero,zero_mul,zero_add,add_zero,sub_zero]
  rw [nextCacheP_eq,nextCachePJet_eq,nextCache8_eq,nextCache7_eq,nextCache7Jet_eq,nextCache6_eq]
  unfold nextCacheP nextCachePJet nextCache8 nextCache7 nextCache7Jet nextCache6
  norm_num only [Nat.reduceSub,Nat.cast_ofNat]
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,
    Mathlib.Tactic.RingNF.nat_rawCast_1,Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

theorem pairRelativeMonomialReserve_8_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < pairRelativeMonomialReserve 8 y := by
  unfold pairRelativeMonomialReserve pairRelativeShiftCoeff
  norm_num only [Nat.reduceSub,Nat.choose,OfNat.zero_ne_ofNat,ite_false,ite_true,
    pairKernelShiftValue_nine,pairKernelShiftJet_nine,mul_zero,zero_mul,zero_add,add_zero,sub_zero]
  rw [nextCacheP_eq,nextCachePJet_eq,nextCache8_eq,nextCache8Jet_eq,nextCache7_eq]
  unfold nextCacheP nextCachePJet nextCache8 nextCache8Jet nextCache7
  norm_num only [Nat.reduceSub,Nat.cast_ofNat]
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,
    Mathlib.Tactic.RingNF.nat_rawCast_1,Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity
theorem pairRelativeMonomialReserve_pos (y : ℝ) (hy : 0 ≤ y) (k : ℕ) (hk : k ≤ 8) :
    0 < pairRelativeMonomialReserve k y := by
  interval_cases k
  · exact pairRelativeMonomialReserve_0_pos y hy
  · exact pairRelativeMonomialReserve_1_pos y hy
  · exact pairRelativeMonomialReserve_2_pos y hy
  · exact pairRelativeMonomialReserve_3_pos y hy
  · exact pairRelativeMonomialReserve_4_pos y hy
  · exact pairRelativeMonomialReserve_5_pos y hy
  · exact pairRelativeMonomialReserve_6_pos y hy
  · exact pairRelativeMonomialReserve_7_pos y hy
  · exact pairRelativeMonomialReserve_8_pos y hy
end
end RHTower.ThetaCuspDefect
