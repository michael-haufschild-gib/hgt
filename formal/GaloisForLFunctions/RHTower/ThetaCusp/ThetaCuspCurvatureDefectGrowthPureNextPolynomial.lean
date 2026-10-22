import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthPureNextMoments
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthAtomGapCooling
/-! Exact source-linked cubic reserve and quartic absorption for the
pair-relative transfer. All shifted polynomial certificates use default limits. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
open Filter Set Topology
noncomputable section
private def mixedAnchor (q : ℝ) : ℝ :=
  q ^ 2 * 98415 +
      (q ^ 3 * 393660 +
        (q ^ 4 * (1541835/2) +
          (q ^ 5 * 987795 +
            (q ^ 6 * (7468605/8) +
              (q ^ 7 * 695466 +
                (q ^ 8 * (14811093/32) +
                  (q ^ 9 * (3340035/16) +
                    (q ^ 10 * (-2113371/32) +
                      (q ^ 11 * (-897885/8) +
                        (q ^ 12 * (-130977/2) +
                          (q ^ 13 * (-19683/2) +
                            (q ^ 14 * (54675/2) +
                              (q ^ 15 * 8748 + 0)))))))))))))

private def mixedAnchorSlope (q : ℝ) : ℝ :=
  q ^ 2 * (-590490) +
      (q ^ 3 * (-2263545) +
        (q ^ 4 * (-4264650) +
          (q ^ 5 * (-10552275/2) +
            (q ^ 6 * (-19322145/4) +
              (q ^ 7 * (-27969543/8) +
                (q ^ 8 * (-2086398) +
                  (q ^ 9 * (-37753209/32) +
                    (q ^ 10 * (-3033369/4) +
                      (q ^ 11 * (-4434507/32) +
                        (q ^ 12 * (598023/8) +
                          (q ^ 13 * 147258 +
                            (q ^ 14 * (387099/2) +
                              (q ^ 15 * (-41553/2) +
                                (q ^ 16 * (-26244) + 0))))))))))))))

private theorem mixedAnchor_numerator_eq (q : ℝ) : growthNumerator q 3=mixedAnchor q := by
  unfold growthNumerator mixedAnchor
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

private theorem mixedAnchor_slope_eq (q : ℝ) : slopeNumerator q 3=mixedAnchorSlope q := by
  unfold slopeNumerator mixedAnchorSlope
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

private def mixedRefCacheP (y : ℝ) : ℝ :=
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

private theorem mixedRefCacheP_eq (y : ℝ) : atomGapPolyEval atomGapPairCoeff y=mixedRefCacheP y := by
  norm_num [atomGapPolyEval,atomGapPairCoeff,mixedRefCacheP,Finset.sum_range_succ]

private def mixedRefCachePJet (y : ℝ) : ℝ :=
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

private theorem mixedRefCachePJet_eq (y : ℝ) : atomGapPolyJet atomGapPairCoeff y=mixedRefCachePJet y := by
  norm_num [atomGapPolyJet,atomGapPairCoeff,mixedRefCachePJet,Finset.sum_range_succ]


def pureNextPolyEval (c : ℕ → ℝ) (y : ℝ) : ℝ := ∑ j ∈ Finset.range 35, c j*y^j
def pureNextPolyJet (c : ℕ → ℝ) (y : ℝ) : ℝ := ∑ j ∈ Finset.range 35, c j*(j:ℝ)*y^(j-1)

def pureNextCoeff3 : ℕ → ℝ
  | 0 => 306035083745488472557933921185/16777216
  | 1 => 2063790026159291260030386707877/8388608
  | 2 => 6988781405421254292869091299805/4194304
  | 3 => 500237423199862924441099173975/65536
  | 4 => 224686220352189922860511108350951/8388608
  | 5 => 322112947563639672125318072068563/4194304
  | 6 => 780422406494968624312624675089843/4194304
  | 7 => 405940144222364286147448206956769/1048576
  | 8 => 11691088543898484341107072742640729/16777216
  | 9 => 9138845010162793289732492703611589/8388608
  | 10 => 3111847678193942123877413215916001/2097152
  | 11 => 1851858446274988927559430880510809/1048576
  | 12 => 1931901743080192652235817433742105/1048576
  | 13 => 885831399242124025994236765005165/524288
  | 14 => 44746267404322718076708049190661/32768
  | 15 => 15969011233252482422383525500123/16384
  | 16 => 20161440890422849888042713289929/32768
  | 17 => 5632686119702897014465234196613/16384
  | 18 => 696507347814948105975843904827/4096
  | 19 => 152374193468935683344370208755/2048
  | 20 => 58885181736648338930811070365/2048
  | 21 => 10024805330930303949444562449/1024
  | 22 => 374587305522887587339724049/128
  | 23 => 48918379181139491553553707/64
  | 24 => 44372252879555419312542837/256
  | 25 => 4332106248807856400300241/128
  | 26 => 180135678712517394717393/32
  | 27 => 12579619782401084186793/16
  | 28 => 1447172479413963125613/16
  | 29 => 66739076911390293873/8
  | 30 => 592860949303493556
  | 31 => 30463170589005552
  | 32 => 1006871757907968
  | 33 => 16067102519808
  | _ => 0

private def pureRefCache3 (y : ℝ) : ℝ :=
  (306035083745488472557933921185/16777216)*y^0+
    (2063790026159291260030386707877/8388608)*y^1+
    (6988781405421254292869091299805/4194304)*y^2+
    (500237423199862924441099173975/65536)*y^3+
    (224686220352189922860511108350951/8388608)*y^4+
    (322112947563639672125318072068563/4194304)*y^5+
    (780422406494968624312624675089843/4194304)*y^6+
    (405940144222364286147448206956769/1048576)*y^7+
    (11691088543898484341107072742640729/16777216)*y^8+
    (9138845010162793289732492703611589/8388608)*y^9+
    (3111847678193942123877413215916001/2097152)*y^10+
    (1851858446274988927559430880510809/1048576)*y^11+
    (1931901743080192652235817433742105/1048576)*y^12+
    (885831399242124025994236765005165/524288)*y^13+
    (44746267404322718076708049190661/32768)*y^14+
    (15969011233252482422383525500123/16384)*y^15+
    (20161440890422849888042713289929/32768)*y^16+
    (5632686119702897014465234196613/16384)*y^17+
    (696507347814948105975843904827/4096)*y^18+
    (152374193468935683344370208755/2048)*y^19+
    (58885181736648338930811070365/2048)*y^20+
    (10024805330930303949444562449/1024)*y^21+
    (374587305522887587339724049/128)*y^22+
    (48918379181139491553553707/64)*y^23+
    (44372252879555419312542837/256)*y^24+
    (4332106248807856400300241/128)*y^25+
    (180135678712517394717393/32)*y^26+
    (12579619782401084186793/16)*y^27+
    (1447172479413963125613/16)*y^28+
    (66739076911390293873/8)*y^29+
    (592860949303493556)*y^30+
    (30463170589005552)*y^31+
    (1006871757907968)*y^32+
    (16067102519808)*y^33

private theorem pureRefCache3_eq (y : ℝ) : pureNextPolyEval pureNextCoeff3 y=pureRefCache3 y := by
  norm_num [pureNextPolyEval,pureNextCoeff3,pureRefCache3,Finset.sum_range_succ]

private def pureRefCache3Jet (y : ℝ) : ℝ :=
  (2063790026159291260030386707877/8388608)*(1:ℝ)*y^(1-1)+
    (6988781405421254292869091299805/4194304)*(2:ℝ)*y^(2-1)+
    (500237423199862924441099173975/65536)*(3:ℝ)*y^(3-1)+
    (224686220352189922860511108350951/8388608)*(4:ℝ)*y^(4-1)+
    (322112947563639672125318072068563/4194304)*(5:ℝ)*y^(5-1)+
    (780422406494968624312624675089843/4194304)*(6:ℝ)*y^(6-1)+
    (405940144222364286147448206956769/1048576)*(7:ℝ)*y^(7-1)+
    (11691088543898484341107072742640729/16777216)*(8:ℝ)*y^(8-1)+
    (9138845010162793289732492703611589/8388608)*(9:ℝ)*y^(9-1)+
    (3111847678193942123877413215916001/2097152)*(10:ℝ)*y^(10-1)+
    (1851858446274988927559430880510809/1048576)*(11:ℝ)*y^(11-1)+
    (1931901743080192652235817433742105/1048576)*(12:ℝ)*y^(12-1)+
    (885831399242124025994236765005165/524288)*(13:ℝ)*y^(13-1)+
    (44746267404322718076708049190661/32768)*(14:ℝ)*y^(14-1)+
    (15969011233252482422383525500123/16384)*(15:ℝ)*y^(15-1)+
    (20161440890422849888042713289929/32768)*(16:ℝ)*y^(16-1)+
    (5632686119702897014465234196613/16384)*(17:ℝ)*y^(17-1)+
    (696507347814948105975843904827/4096)*(18:ℝ)*y^(18-1)+
    (152374193468935683344370208755/2048)*(19:ℝ)*y^(19-1)+
    (58885181736648338930811070365/2048)*(20:ℝ)*y^(20-1)+
    (10024805330930303949444562449/1024)*(21:ℝ)*y^(21-1)+
    (374587305522887587339724049/128)*(22:ℝ)*y^(22-1)+
    (48918379181139491553553707/64)*(23:ℝ)*y^(23-1)+
    (44372252879555419312542837/256)*(24:ℝ)*y^(24-1)+
    (4332106248807856400300241/128)*(25:ℝ)*y^(25-1)+
    (180135678712517394717393/32)*(26:ℝ)*y^(26-1)+
    (12579619782401084186793/16)*(27:ℝ)*y^(27-1)+
    (1447172479413963125613/16)*(28:ℝ)*y^(28-1)+
    (66739076911390293873/8)*(29:ℝ)*y^(29-1)+
    (592860949303493556)*(30:ℝ)*y^(30-1)+
    (30463170589005552)*(31:ℝ)*y^(31-1)+
    (1006871757907968)*(32:ℝ)*y^(32-1)+
    (16067102519808)*(33:ℝ)*y^(33-1)

private theorem pureRefCache3Jet_eq (y : ℝ) : pureNextPolyJet pureNextCoeff3 y=pureRefCache3Jet y := by
  norm_num [pureNextPolyJet,pureNextCoeff3,pureRefCache3Jet,Finset.sum_range_succ]

theorem dominantTriplePolynomial_pure_shift_eq (y : ℝ) :
    dominantTriplePolynomial (3/2+y)=pureNextPolyEval pureNextCoeff3 y := by
  rw [pureRefCache3_eq]
  unfold dominantTriplePolynomial
  simp only [mixedAnchor_numerator_eq,mixedAnchor_slope_eq]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold tripleMomentPolynomial
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold mixedAnchor mixedAnchorSlope pureRefCache3
  ring

def pureNextCoeff4 : ℕ → ℝ
  | 0 => 429112592723145758166679826565/131072
  | 1 => 11622887749310919175946652372243/262144
  | 2 => 78043973318202705290607195456885/262144
  | 3 => 350154867175780744155591898685055/262144
  | 4 => 1193978592466529670491856192777141/262144
  | 5 => 207859089849827506622888469369255/16384
  | 6 => 3944081099210394366949927279375395/131072
  | 7 => 4067720625456131789121043443282423/65536
  | 8 => 919652999005565380172003439499173/8192
  | 9 => 1461432174480735003513588381769755/8192
  | 10 => 1020394393539403382806160876786235/4096
  | 11 => 626325741679034817673302728285109/2048
  | 12 => 169178907133691268863948384183811/512
  | 13 => 80576677040765491479440138505939/256
  | 14 => 67798930084913356186894769566431/256
  | 15 => 25241471706704324612381325972315/128
  | 16 => 4164191921745125899898982301791/32
  | 17 => 152363251254491413417658570535/2
  | 18 => 316659113075729724582751539075/8
  | 19 => 36498211341657819818834354427/2
  | 20 => 29834626611721946727953584395/4
  | 21 => 2697753955809630091171931523
  | 22 => 1722452875156086822317854359/2
  | 23 => 241770506884753093868688651
  | 24 => 59390980893426586004633376
  | 25 => 12684436415224199865780840
  | 26 => 2335737448696508573742576
  | 27 => 366818404490686850484384
  | 28 => 48430569196042336674432
  | 29 => 5272609434092497516032
  | 30 => 460717532208555724800
  | 31 => 31050670638707048448
  | 32 => 1514657670793003008
  | 33 => 47575197479337984
  | 34 => 722204136308736
  | _ => 0

private def pureRefCache4 (y : ℝ) : ℝ :=
  (429112592723145758166679826565/131072)*y^0+
    (11622887749310919175946652372243/262144)*y^1+
    (78043973318202705290607195456885/262144)*y^2+
    (350154867175780744155591898685055/262144)*y^3+
    (1193978592466529670491856192777141/262144)*y^4+
    (207859089849827506622888469369255/16384)*y^5+
    (3944081099210394366949927279375395/131072)*y^6+
    (4067720625456131789121043443282423/65536)*y^7+
    (919652999005565380172003439499173/8192)*y^8+
    (1461432174480735003513588381769755/8192)*y^9+
    (1020394393539403382806160876786235/4096)*y^10+
    (626325741679034817673302728285109/2048)*y^11+
    (169178907133691268863948384183811/512)*y^12+
    (80576677040765491479440138505939/256)*y^13+
    (67798930084913356186894769566431/256)*y^14+
    (25241471706704324612381325972315/128)*y^15+
    (4164191921745125899898982301791/32)*y^16+
    (152363251254491413417658570535/2)*y^17+
    (316659113075729724582751539075/8)*y^18+
    (36498211341657819818834354427/2)*y^19+
    (29834626611721946727953584395/4)*y^20+
    (2697753955809630091171931523)*y^21+
    (1722452875156086822317854359/2)*y^22+
    (241770506884753093868688651)*y^23+
    (59390980893426586004633376)*y^24+
    (12684436415224199865780840)*y^25+
    (2335737448696508573742576)*y^26+
    (366818404490686850484384)*y^27+
    (48430569196042336674432)*y^28+
    (5272609434092497516032)*y^29+
    (460717532208555724800)*y^30+
    (31050670638707048448)*y^31+
    (1514657670793003008)*y^32+
    (47575197479337984)*y^33+
    (722204136308736)*y^34

private theorem pureRefCache4_eq (y : ℝ) : pureNextPolyEval pureNextCoeff4 y=pureRefCache4 y := by
  norm_num [pureNextPolyEval,pureNextCoeff4,pureRefCache4,Finset.sum_range_succ]

private def pureRefCache4Jet (y : ℝ) : ℝ :=
  (11622887749310919175946652372243/262144)*(1:ℝ)*y^(1-1)+
    (78043973318202705290607195456885/262144)*(2:ℝ)*y^(2-1)+
    (350154867175780744155591898685055/262144)*(3:ℝ)*y^(3-1)+
    (1193978592466529670491856192777141/262144)*(4:ℝ)*y^(4-1)+
    (207859089849827506622888469369255/16384)*(5:ℝ)*y^(5-1)+
    (3944081099210394366949927279375395/131072)*(6:ℝ)*y^(6-1)+
    (4067720625456131789121043443282423/65536)*(7:ℝ)*y^(7-1)+
    (919652999005565380172003439499173/8192)*(8:ℝ)*y^(8-1)+
    (1461432174480735003513588381769755/8192)*(9:ℝ)*y^(9-1)+
    (1020394393539403382806160876786235/4096)*(10:ℝ)*y^(10-1)+
    (626325741679034817673302728285109/2048)*(11:ℝ)*y^(11-1)+
    (169178907133691268863948384183811/512)*(12:ℝ)*y^(12-1)+
    (80576677040765491479440138505939/256)*(13:ℝ)*y^(13-1)+
    (67798930084913356186894769566431/256)*(14:ℝ)*y^(14-1)+
    (25241471706704324612381325972315/128)*(15:ℝ)*y^(15-1)+
    (4164191921745125899898982301791/32)*(16:ℝ)*y^(16-1)+
    (152363251254491413417658570535/2)*(17:ℝ)*y^(17-1)+
    (316659113075729724582751539075/8)*(18:ℝ)*y^(18-1)+
    (36498211341657819818834354427/2)*(19:ℝ)*y^(19-1)+
    (29834626611721946727953584395/4)*(20:ℝ)*y^(20-1)+
    (2697753955809630091171931523)*(21:ℝ)*y^(21-1)+
    (1722452875156086822317854359/2)*(22:ℝ)*y^(22-1)+
    (241770506884753093868688651)*(23:ℝ)*y^(23-1)+
    (59390980893426586004633376)*(24:ℝ)*y^(24-1)+
    (12684436415224199865780840)*(25:ℝ)*y^(25-1)+
    (2335737448696508573742576)*(26:ℝ)*y^(26-1)+
    (366818404490686850484384)*(27:ℝ)*y^(27-1)+
    (48430569196042336674432)*(28:ℝ)*y^(28-1)+
    (5272609434092497516032)*(29:ℝ)*y^(29-1)+
    (460717532208555724800)*(30:ℝ)*y^(30-1)+
    (31050670638707048448)*(31:ℝ)*y^(31-1)+
    (1514657670793003008)*(32:ℝ)*y^(32-1)+
    (47575197479337984)*(33:ℝ)*y^(33-1)+
    (722204136308736)*(34:ℝ)*y^(34-1)

private theorem pureRefCache4Jet_eq (y : ℝ) : pureNextPolyJet pureNextCoeff4 y=pureRefCache4Jet y := by
  norm_num [pureNextPolyJet,pureNextCoeff4,pureRefCache4Jet,Finset.sum_range_succ]

theorem dominantQuadruplePolynomial_pure_shift_eq (y : ℝ) :
    dominantQuadruplePolynomial (3/2+y)=pureNextPolyEval pureNextCoeff4 y := by
  rw [pureRefCache4_eq]
  unfold dominantQuadruplePolynomial
  simp only [mixedAnchor_numerator_eq,mixedAnchor_slope_eq]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold quadrupleMomentPolynomial
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold mixedAnchor mixedAnchorSlope pureRefCache4
  ring

theorem hasDerivAt_pureNextPolyEval (c : ℕ → ℝ) (y : ℝ) :
    HasDerivAt (pureNextPolyEval c) (pureNextPolyJet c y) y := by
  unfold pureNextPolyEval pureNextPolyJet
  apply HasDerivAt.fun_sum
  intro j hj
  simpa only [mul_assoc] using (hasDerivAt_pow j y).const_mul (c j)

def dominantTriplePolynomialJet (q : ℝ) : ℝ := pureNextPolyJet pureNextCoeff3 (q-3/2)

theorem hasDerivAt_dominantTriplePolynomial (q : ℝ) :
    HasDerivAt dominantTriplePolynomial (dominantTriplePolynomialJet q) q := by
  have h := (hasDerivAt_pureNextPolyEval pureNextCoeff3 (q-3/2)).comp q
    ((hasDerivAt_id q).sub_const (3/2))
  simp only [Function.comp_def,id_eq,mul_one] at h
  apply h.congr_of_eventuallyEq
  filter_upwards with r
  simpa only [show (3/2:ℝ)+(r-3/2)=r by ring] using dominantTriplePolynomial_pure_shift_eq (r-3/2)

def dominantQuadruplePolynomialJet (q : ℝ) : ℝ := pureNextPolyJet pureNextCoeff4 (q-3/2)

theorem hasDerivAt_dominantQuadruplePolynomial (q : ℝ) :
    HasDerivAt dominantQuadruplePolynomial (dominantQuadruplePolynomialJet q) q := by
  have h := (hasDerivAt_pureNextPolyEval pureNextCoeff4 (q-3/2)).comp q
    ((hasDerivAt_id q).sub_const (3/2))
  simp only [Function.comp_def,id_eq,mul_one] at h
  apply h.congr_of_eventuallyEq
  filter_upwards with r
  simpa only [show (3/2:ℝ)+(r-3/2)=r by ring] using dominantQuadruplePolynomial_pure_shift_eq (r-3/2)

def pureCubicNextNumerator (q : ℝ) : ℝ :=
  ((3*q+1)*dominantTriplePolynomial q-q*dominantTriplePolynomialJet q)*dominantPairPolynomial q+
    q*dominantTriplePolynomial q*dominantPairPolynomialJet q

def pureQuarticNextNumerator (q : ℝ) : ℝ :=
  ((6*q+2)*dominantQuadruplePolynomial q-q*dominantQuadruplePolynomialJet q)*dominantPairPolynomial q+
    q*dominantQuadruplePolynomial q*dominantPairPolynomialJet q

theorem pureCubicNext_shift_reserve (y : ℝ) (hy : 0 ≤ y) :
    dominantPairPolynomial (3/2+y)*growthCoefficient (3/2+y) 7*growthNumerator (3/2+y) 3*
      polynomialMoment (3/2+y) 3 0^2*polynomialMoment (3/2+y) 3 9 < pureCubicNextNumerator (3/2+y) := by
  unfold pureCubicNextNumerator dominantTriplePolynomialJet
  rw [dominantTriplePolynomial_pure_shift_eq,dominantPairPolynomial_gap_shift_eq,
    dominantPairPolynomialJet_gap_shift_eq,show (3/2:ℝ)+y-3/2=y by ring]
  simp only [pureRefCache3_eq,pureRefCache3Jet_eq,mixedRefCacheP_eq,mixedRefCachePJet_eq,mixedAnchor_numerator_eq]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo,polynomialMoment,Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold pureRefCache3 pureRefCache3Jet mixedRefCacheP mixedRefCachePJet mixedAnchor
  apply sub_pos.mp
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

theorem pureQuarticNext_shift_absorption (y : ℝ) (hy : 0 ≤ y) :
    pureQuarticNextNumerator (3/2+y) < 256*polynomialMoment (3/2+y) 3 0*pureCubicNextNumerator (3/2+y) := by
  unfold pureCubicNextNumerator pureQuarticNextNumerator dominantTriplePolynomialJet dominantQuadruplePolynomialJet
  rw [dominantTriplePolynomial_pure_shift_eq,dominantQuadruplePolynomial_pure_shift_eq,
    dominantPairPolynomial_gap_shift_eq,dominantPairPolynomialJet_gap_shift_eq,
    show (3/2:ℝ)+y-3/2=y by ring]
  simp only [pureRefCache3_eq,pureRefCache3Jet_eq,pureRefCache4_eq,pureRefCache4Jet_eq,
    mixedRefCacheP_eq,mixedRefCachePJet_eq]
  norm_num [polynomialMoment,Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold pureRefCache3 pureRefCache3Jet pureRefCache4 pureRefCache4Jet mixedRefCacheP mixedRefCachePJet
  apply sub_pos.mp
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

theorem pureCubicNext_reserve {q : ℝ} (hq : 3/2 ≤ q) :
    dominantPairPolynomial q*growthCoefficient q 7*growthNumerator q 3*
      polynomialMoment q 3 0^2*polynomialMoment q 3 9 < pureCubicNextNumerator q := by
  have h := pureCubicNext_shift_reserve (q-3/2) (by linarith)
  simpa only [show (3/2:ℝ)+(q-3/2)=q by ring] using h

theorem pureQuarticNext_absorption {q : ℝ} (hq : 3/2 ≤ q) :
    pureQuarticNextNumerator q < 256*polynomialMoment q 3 0*pureCubicNextNumerator q := by
  have h := pureQuarticNext_shift_absorption (q-3/2) (by linarith)
  simpa only [show (3/2:ℝ)+(q-3/2)=q by ring] using h

end
end RHTower.ThetaCuspDefect
