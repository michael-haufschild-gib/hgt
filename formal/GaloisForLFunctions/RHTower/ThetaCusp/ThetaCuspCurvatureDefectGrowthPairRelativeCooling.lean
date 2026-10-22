import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthAbsorptionResidual
/-!
# Relative cooling of the literal dominant growth pair

The transfer of the literal second-atom pair, divided by the leading
transfer coefficient, cools strictly slower than rate eight on q >= 3/2.
Its exp(8q)-weighted value is therefore strictly increasing. The proof
uses exact shifted polynomial identities and a positive Wronskian
certificate, cached separately from the source derivative transport.
No sign of the complete source residual is assumed or established here.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section

def pairShiftPCoeff : ℕ → ℝ
  | 0 => 1861439671925411064321195/262144
  | 1 => 17029102555455663849163083/131072
  | 2 => 322103250906652692527224995/262144
  | 3 => 3986068609578601786146770907/524288
  | 4 => 17747426224968762775188708801/524288
  | 5 => 60205290770051699808697176159/524288
  | 6 => 161889339980151795383364100185/524288
  | 7 => 88783224129787319215420379949/131072
  | 8 => 40584482588850241239154879101/32768
  | 9 => 125732997201449447835433962975/65536
  | 10 => 83526071203783400209001293023/32768
  | 11 => 24021870812074579694285775753/8192
  | 12 => 3012388545381711954421912695/1024
  | 13 => 10598204705085701542133692191/4096
  | 14 => 2051032002969296969786490399/1024
  | 15 => 350249683977929583797321241/256
  | 16 => 52856430502952134902727413/64
  | 17 => 56420609017661702586319923/128
  | 18 => 13306021597836988576698663/64
  | 19 => 1384664906267936886187899/16
  | 20 => 253708974997061236411869/8
  | 21 => 40781033052359698188063/4
  | 22 => 22891888988441303827797/8
  | 23 => 1393460938024037275545/2
  | 24 => 145953189487990653714
  | 25 => 26021377372028465547
  | 26 => 3892209828844085190
  | 27 => 479089069751214504
  | 28 => 47234407851478656
  | 29 => 3584618003916144
  | 30 => 196488958170240
  | 31 => 6920535241728
  | 32 => 117546246144
  | _ => 0

private def pairShiftQCoeff : ℕ → ℝ
  | 0 => 34308668796591836115/16777216
  | 1 => 470184313263605662095/16777216
  | 2 => 781197417932574331791/4194304
  | 3 => 13534445568077094846015/16777216
  | 4 => 10877860182271143516651/4194304
  | 5 => 112507522018914275202771/16777216
  | 6 => 61864840508643093316563/4194304
  | 7 => 479984364775295647013385/16777216
  | 8 => 834488329261056337027989/16777216
  | 9 => 650699821079141215464063/8388608
  | 10 => 452063864777961224696013/4194304
  | 11 => 277731212897899100450295/2097152
  | 12 => 150113097103146543316935/1048576
  | 13 => 71200368375894274233393/524288
  | 14 => 29614510402683292229427/262144
  | 15 => 10803634349209423757163/131072
  | 16 => 1729136284321842391671/32768
  | 17 => 485759413061150818203/16384
  | 18 => 119718943453712946321/8192
  | 19 => 25857092230954891515/4096
  | 20 => 4884296527051557543/2048
  | 21 => 804433743855233901/1024
  | 22 => 115012254742101963/512
  | 23 => 3547480989423825/64
  | 24 => 2997687458782017/256
  | 25 => 268251105264219/128
  | 26 => 20053406757249/64
  | 27 => 1228709504259/32
  | 28 => 60075920187/16
  | 29 => 2253002445/8
  | 30 => 60827031/4
  | 31 => 1051947/2
  | 32 => 8748
  | _ => 0

def pairShiftEval (c : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 33, c j*y^j
def pairShiftJet (c : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 33, c j*(j:ℝ)*y^(j-1)

private theorem hasDerivAt_pairShiftEval (c : ℕ → ℝ) (y : ℝ) :
    HasDerivAt (pairShiftEval c) (pairShiftJet c y) y := by
  unfold pairShiftEval pairShiftJet
  apply HasDerivAt.fun_sum
  intro j hj
  simpa only [mul_assoc] using (hasDerivAt_pow j y).const_mul (c j)

private def pairShiftP (y : ℝ) : ℝ :=
  1861439671925411064321195 / 262144 +
      (y * (17029102555455663849163083 / 131072) +
        (y ^ 2 * (322103250906652692527224995 / 262144) +
          (y ^ 3 * (3986068609578601786146770907 / 524288) +
            (y ^ 4 * (17747426224968762775188708801 / 524288) +
              (y ^ 5 * (60205290770051699808697176159 / 524288) +
                (y ^ 6 * (161889339980151795383364100185 / 524288) +
                  (y ^ 7 * (88783224129787319215420379949 / 131072) +
                    (y ^ 8 * (40584482588850241239154879101 / 32768) +
                      (y ^ 9 * (125732997201449447835433962975 / 65536) +
                        (y ^ 10 * (83526071203783400209001293023 / 32768) +
                          (y ^ 11 * (24021870812074579694285775753 / 8192) +
                            (y ^ 12 * (3012388545381711954421912695 / 1024) +
                              (y ^ 13 * (10598204705085701542133692191 / 4096) +
                                (y ^ 14 * (2051032002969296969786490399 / 1024) +
                                  (y ^ 15 * (350249683977929583797321241 / 256) +
                                    (y ^ 16 * (52856430502952134902727413 / 64) +
                                      (y ^ 17 * (56420609017661702586319923 / 128) +
                                        (y ^ 18 *
                                            (13306021597836988576698663 / 64) +
                                          (y ^ 19 *
                                              (1384664906267936886187899 / 16) +
                                            (y ^ 20 *
                                                (253708974997061236411869 / 8) +
                                              (y ^ 21 *
                                                  (40781033052359698188063 / 4) +
                                                (y ^ 22 *
                                                    (22891888988441303827797 / 8) +
                                                  (y ^ 23 *
                                                      (1393460938024037275545 / 2) +
                                                    (y ^ 24 * 145953189487990653714 +
                                                      (y ^ 25 * 26021377372028465547 +
                                                        (y ^ 26 * 3892209828844085190 +
                                                          (y ^ 27 * 479089069751214504 +
                                                            (y ^ 28 * 47234407851478656 +
                                                              (y ^ 29 * 3584618003916144 +
                                                                (y ^ 30 * 196488958170240 +
                                                                  (y ^ 31 * 6920535241728 +
                                                                    (y ^ 32 * 117546246144 +
                                                                      0))))))))))))))))))))))))))))))))

private def pairShiftPJet (y : ℝ) : ℝ :=
  (17029102555455663849163083/131072)*(1:ℝ)*y^(1-1)+
    (322103250906652692527224995/262144)*(2:ℝ)*y^(2-1)+
    (3986068609578601786146770907/524288)*(3:ℝ)*y^(3-1)+
    (17747426224968762775188708801/524288)*(4:ℝ)*y^(4-1)+
    (60205290770051699808697176159/524288)*(5:ℝ)*y^(5-1)+
    (161889339980151795383364100185/524288)*(6:ℝ)*y^(6-1)+
    (88783224129787319215420379949/131072)*(7:ℝ)*y^(7-1)+
    (40584482588850241239154879101/32768)*(8:ℝ)*y^(8-1)+
    (125732997201449447835433962975/65536)*(9:ℝ)*y^(9-1)+
    (83526071203783400209001293023/32768)*(10:ℝ)*y^(10-1)+
    (24021870812074579694285775753/8192)*(11:ℝ)*y^(11-1)+
    (3012388545381711954421912695/1024)*(12:ℝ)*y^(12-1)+
    (10598204705085701542133692191/4096)*(13:ℝ)*y^(13-1)+
    (2051032002969296969786490399/1024)*(14:ℝ)*y^(14-1)+
    (350249683977929583797321241/256)*(15:ℝ)*y^(15-1)+
    (52856430502952134902727413/64)*(16:ℝ)*y^(16-1)+
    (56420609017661702586319923/128)*(17:ℝ)*y^(17-1)+
    (13306021597836988576698663/64)*(18:ℝ)*y^(18-1)+
    (1384664906267936886187899/16)*(19:ℝ)*y^(19-1)+
    (253708974997061236411869/8)*(20:ℝ)*y^(20-1)+
    (40781033052359698188063/4)*(21:ℝ)*y^(21-1)+
    (22891888988441303827797/8)*(22:ℝ)*y^(22-1)+
    (1393460938024037275545/2)*(23:ℝ)*y^(23-1)+
    145953189487990653714*(24:ℝ)*y^(24-1)+
    26021377372028465547*(25:ℝ)*y^(25-1)+
    3892209828844085190*(26:ℝ)*y^(26-1)+
    479089069751214504*(27:ℝ)*y^(27-1)+
    47234407851478656*(28:ℝ)*y^(28-1)+
    3584618003916144*(29:ℝ)*y^(29-1)+
    196488958170240*(30:ℝ)*y^(30-1)+
    6920535241728*(31:ℝ)*y^(31-1)+
    117546246144*(32:ℝ)*y^(32-1)

private theorem pairShiftEval_P (y : ℝ) :
    pairShiftEval pairShiftPCoeff y=pairShiftP y := by
  norm_num [pairShiftEval,pairShiftPCoeff,pairShiftP,Finset.sum_range_succ]
  ring

private theorem pairShiftJet_P (y : ℝ) :
    pairShiftJet pairShiftPCoeff y=pairShiftPJet y := by
  norm_num [pairShiftJet,pairShiftPCoeff,pairShiftPJet,Finset.sum_range_succ]

private def pairShiftQ (y : ℝ) : ℝ :=
  34308668796591836115 / 16777216 +
      (y * (470184313263605662095 / 16777216) +
        (y ^ 2 * (781197417932574331791 / 4194304) +
          (y ^ 3 * (13534445568077094846015 / 16777216) +
            (y ^ 4 * (10877860182271143516651 / 4194304) +
              (y ^ 5 * (112507522018914275202771 / 16777216) +
                (y ^ 6 * (61864840508643093316563 / 4194304) +
                  (y ^ 7 * (479984364775295647013385 / 16777216) +
                    (y ^ 8 * (834488329261056337027989 / 16777216) +
                      (y ^ 9 * (650699821079141215464063 / 8388608) +
                        (y ^ 10 * (452063864777961224696013 / 4194304) +
                          (y ^ 11 * (277731212897899100450295 / 2097152) +
                            (y ^ 12 * (150113097103146543316935 / 1048576) +
                              (y ^ 13 * (71200368375894274233393 / 524288) +
                                (y ^ 14 * (29614510402683292229427 / 262144) +
                                  (y ^ 15 * (10803634349209423757163 / 131072) +
                                    (y ^ 16 * (1729136284321842391671 / 32768) +
                                      (y ^ 17 * (485759413061150818203 / 16384) +
                                        (y ^ 18 * (119718943453712946321 / 8192) +
                                          (y ^ 19 * (25857092230954891515 / 4096) +
                                            (y ^ 20 * (4884296527051557543 / 2048) +
                                              (y ^ 21 *
                                                  (804433743855233901 / 1024) +
                                                (y ^ 22 *
                                                    (115012254742101963 / 512) +
                                                  (y ^ 23 *
                                                      (3547480989423825 / 64) +
                                                    (y ^ 24 *
                                                        (2997687458782017 / 256) +
                                                      (y ^ 25 *
                                                          (268251105264219 / 128) +
                                                        (y ^ 26 *
                                                            (20053406757249 / 64) +
                                                          (y ^ 27 *
                                                              (1228709504259 / 32) +
                                                            (y ^ 28 *
                                                                (60075920187 / 16) +
                                                              (y ^ 29 *
                                                                  (2253002445 / 8) +
                                                                (y ^ 30 *
                                                                    (60827031 / 4) +
                                                                  (y ^ 31 *
                                                                      (1051947 / 2) +
                                                                    (y ^ 32 * 8748 +
                                                                      0))))))))))))))))))))))))))))))))

private def pairShiftQJet (y : ℝ) : ℝ :=
  (470184313263605662095/16777216)*(1:ℝ)*y^(1-1)+
    (781197417932574331791/4194304)*(2:ℝ)*y^(2-1)+
    (13534445568077094846015/16777216)*(3:ℝ)*y^(3-1)+
    (10877860182271143516651/4194304)*(4:ℝ)*y^(4-1)+
    (112507522018914275202771/16777216)*(5:ℝ)*y^(5-1)+
    (61864840508643093316563/4194304)*(6:ℝ)*y^(6-1)+
    (479984364775295647013385/16777216)*(7:ℝ)*y^(7-1)+
    (834488329261056337027989/16777216)*(8:ℝ)*y^(8-1)+
    (650699821079141215464063/8388608)*(9:ℝ)*y^(9-1)+
    (452063864777961224696013/4194304)*(10:ℝ)*y^(10-1)+
    (277731212897899100450295/2097152)*(11:ℝ)*y^(11-1)+
    (150113097103146543316935/1048576)*(12:ℝ)*y^(12-1)+
    (71200368375894274233393/524288)*(13:ℝ)*y^(13-1)+
    (29614510402683292229427/262144)*(14:ℝ)*y^(14-1)+
    (10803634349209423757163/131072)*(15:ℝ)*y^(15-1)+
    (1729136284321842391671/32768)*(16:ℝ)*y^(16-1)+
    (485759413061150818203/16384)*(17:ℝ)*y^(17-1)+
    (119718943453712946321/8192)*(18:ℝ)*y^(18-1)+
    (25857092230954891515/4096)*(19:ℝ)*y^(19-1)+
    (4884296527051557543/2048)*(20:ℝ)*y^(20-1)+
    (804433743855233901/1024)*(21:ℝ)*y^(21-1)+
    (115012254742101963/512)*(22:ℝ)*y^(22-1)+
    (3547480989423825/64)*(23:ℝ)*y^(23-1)+
    (2997687458782017/256)*(24:ℝ)*y^(24-1)+
    (268251105264219/128)*(25:ℝ)*y^(25-1)+
    (20053406757249/64)*(26:ℝ)*y^(26-1)+
    (1228709504259/32)*(27:ℝ)*y^(27-1)+
    (60075920187/16)*(28:ℝ)*y^(28-1)+
    (2253002445/8)*(29:ℝ)*y^(29-1)+
    (60827031/4)*(30:ℝ)*y^(30-1)+
    (1051947/2)*(31:ℝ)*y^(31-1)+
    8748*(32:ℝ)*y^(32-1)

private theorem pairShiftEval_Q (y : ℝ) :
    pairShiftEval pairShiftQCoeff y=pairShiftQ y := by
  norm_num [pairShiftEval,pairShiftQCoeff,pairShiftQ,Finset.sum_range_succ]
  ring

private theorem pairShiftJet_Q (y : ℝ) :
    pairShiftJet pairShiftQCoeff y=pairShiftQJet y := by
  norm_num [pairShiftJet,pairShiftQCoeff,pairShiftQJet,Finset.sum_range_succ]

theorem dominantPairPolynomial_shift_eq (y : ℝ) :
    dominantPairPolynomial (3/2+y)=pairShiftEval pairShiftPCoeff y := by
  rw [pairShiftEval_P]
  unfold pairShiftP
  unfold dominantPairPolynomial anchorCoolingNumerator binaryGrowthNumerator binarySlopeNumerator
    growthNumerator slopeNumerator
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo,binaryMoment]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

private theorem pairGapDenominator_shift_eq (y : ℝ) :
    (3/2+y)^10*growthCoefficient (3/2+y) 7*growthNumerator (3/2+y) 3=
      pairShiftEval pairShiftQCoeff y := by
  rw [pairShiftEval_Q]
  unfold pairShiftQ growthNumerator
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

private theorem pairGapWronskian_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < (pairShiftJet pairShiftPCoeff y+2*pairShiftEval pairShiftPCoeff y)*
      pairShiftEval pairShiftQCoeff y-
      pairShiftEval pairShiftPCoeff y*pairShiftJet pairShiftQCoeff y := by
  rw [pairShiftEval_P,pairShiftEval_Q,pairShiftJet_P,pairShiftJet_Q]
  unfold pairShiftP pairShiftQ pairShiftPJet pairShiftQJet
  norm_num only [Nat.reduceSub,Nat.cast_ofNat]
  apply sub_pos.mp
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

open Filter Set Topology

private theorem pairShiftQ_pos {y : ℝ} (hy : 0 ≤ y) :
    0 < pairShiftEval pairShiftQCoeff y := by
  rw [pairShiftEval_Q]
  unfold pairShiftQ
  positivity

def dominantPairNormalizedTransfer (q : ℝ) : ℝ :=
  dominantPairTransfer q/growthTransferLeadingCoefficient q

private theorem dominantPairNormalizedTransfer_eq {q : ℝ} (hq : 0 < q) :
    dominantPairNormalizedTransfer q=dominantAtomScale q^2*
      (pairShiftEval pairShiftPCoeff (q-3/2)/pairShiftEval pairShiftQCoeff (q-3/2)) := by
  have hp := dominantPairPolynomial_shift_eq (q-3/2)
  have hqpoly := pairGapDenominator_shift_eq (q-3/2)
  rw [show (3/2:ℝ)+(q-3/2)=q by ring] at hp hqpoly
  have hQ : pairShiftEval pairShiftQCoeff (q-3/2)=q^9*growthTransferLeadingCoefficient q := by
    rw [←hqpoly]
    unfold growthTransferLeadingCoefficient
    ring
  unfold dominantPairNormalizedTransfer
  rw [dominantPairTransfer_eq hq,hQ,←hp,div_div]
  ring

private def pairShiftRatioSlope (y : ℝ) : ℝ :=
  (pairShiftJet pairShiftPCoeff y*pairShiftEval pairShiftQCoeff y-
    pairShiftEval pairShiftPCoeff y*pairShiftJet pairShiftQCoeff y)/
      (pairShiftEval pairShiftQCoeff y)^2

private theorem hasDerivAt_pairShiftRatio {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (fun z => pairShiftEval pairShiftPCoeff z/pairShiftEval pairShiftQCoeff z)
      (pairShiftRatioSlope y) y :=
  (hasDerivAt_pairShiftEval pairShiftPCoeff y).div
    (hasDerivAt_pairShiftEval pairShiftQCoeff y) (pairShiftQ_pos hy).ne'

theorem hasDerivAt_dominantAtomScale (q : ℝ) :
    HasDerivAt dominantAtomScale (-3*dominantAtomScale q) q := by
  have hi : HasDerivAt (fun t : ℝ => -3*t) (-3) q := by
    simpa only [mul_one,one_mul,id_eq,mul_comm] using (hasDerivAt_id q).const_mul (-3)
  have he : HasDerivAt (fun t : ℝ => Real.exp (-3*t)) (-3*Real.exp (-3*q)) q := by
    simpa only [mul_comm] using hi.exp
  exact (he.const_mul (4*Real.exp (-(9/2)))).congr_deriv (by unfold dominantAtomScale; ring)

private theorem hasDerivAt_dominantPairNormalizedTransfer {q : ℝ} (hq : 3/2 ≤ q) :
    HasDerivAt dominantPairNormalizedTransfer
      (dominantAtomScale q^2*(pairShiftRatioSlope (q-3/2)-
        6*(pairShiftEval pairShiftPCoeff (q-3/2)/pairShiftEval pairShiftQCoeff (q-3/2)))) q := by
  have hq0 : 0 < q := by linarith
  have hy : 0 ≤ q-3/2 := by linarith
  have hs := (hasDerivAt_dominantAtomScale q).pow 2
  have hsq : HasDerivAt (fun t => dominantAtomScale t^2) (-6*dominantAtomScale q^2) q := by
    apply hs.congr_deriv
    norm_num
    ring
  have hr := (hasDerivAt_pairShiftRatio hy).comp q ((hasDerivAt_id q).sub_const (3/2))
  simp only [mul_one,Function.comp_def,id_eq] at hr
  apply ((hsq.mul hr).congr_deriv (by ring)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hq0] with z hz
  exact dominantPairNormalizedTransfer_eq hz

theorem dominantPairNormalizedTransfer_deriv_add_eight_pos {q : ℝ} (hq : 3/2 ≤ q) :
    0 < deriv dominantPairNormalizedTransfer q+8*dominantPairNormalizedTransfer q := by
  have hq0 : 0 < q := by linarith
  have hy : 0 ≤ q-3/2 := by linarith
  have hQ := pairShiftQ_pos hy
  rw [(hasDerivAt_dominantPairNormalizedTransfer hq).deriv,
    dominantPairNormalizedTransfer_eq hq0]
  have he : dominantAtomScale q^2*(pairShiftRatioSlope (q-3/2)-
      6*(pairShiftEval pairShiftPCoeff (q-3/2)/pairShiftEval pairShiftQCoeff (q-3/2)))+
      8*(dominantAtomScale q^2*
        (pairShiftEval pairShiftPCoeff (q-3/2)/pairShiftEval pairShiftQCoeff (q-3/2)))=
      dominantAtomScale q^2*
        ((pairShiftJet pairShiftPCoeff (q-3/2)+2*pairShiftEval pairShiftPCoeff (q-3/2))*
          pairShiftEval pairShiftQCoeff (q-3/2)-
          pairShiftEval pairShiftPCoeff (q-3/2)*pairShiftJet pairShiftQCoeff (q-3/2))/
        (pairShiftEval pairShiftQCoeff (q-3/2))^2 := by
    unfold pairShiftRatioSlope
    field_simp [hQ.ne']
    ring
  rw [he]
  exact div_pos (mul_pos (pow_pos (dominantAtomScale_pos q) 2)
    (pairGapWronskian_pos _ hy)) (pow_pos hQ 2)

private theorem hasDerivAt_expEightDominantPair {q : ℝ} (hq : 3/2 ≤ q) :
    HasDerivAt (fun t => Real.exp (8*t)*dominantPairNormalizedTransfer t)
      (Real.exp (8*q)*(deriv dominantPairNormalizedTransfer q+8*dominantPairNormalizedTransfer q)) q := by
  have hi : HasDerivAt (fun t : ℝ => 8*t) 8 q := by
    simpa only [mul_one,one_mul,id_eq,mul_comm] using (hasDerivAt_id q).const_mul 8
  have he : HasDerivAt (fun t : ℝ => Real.exp (8*t)) (8*Real.exp (8*q)) q := by
    simpa only [mul_comm] using hi.exp
  exact (he.mul (hasDerivAt_dominantPairNormalizedTransfer hq).differentiableAt.hasDerivAt).congr_deriv (by ring)

theorem expEightDominantPair_strictMonoOn :
    StrictMonoOn (fun q => Real.exp (8*q)*dominantPairNormalizedTransfer q) (Ici (3/2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro q hq
    exact (hasDerivAt_expEightDominantPair hq).continuousAt.continuousWithinAt
  · intro q hq
    have hq' : 3/2 < q := by simpa only [interior_Ici,mem_Ioi] using hq
    rw [(hasDerivAt_expEightDominantPair hq'.le).deriv]
    exact mul_pos (Real.exp_pos _) (dominantPairNormalizedTransfer_deriv_add_eight_pos hq'.le)


def dominantPairPolynomialJet (q : ℝ) : ℝ :=
  pairShiftJet pairShiftPCoeff (q-3/2)

theorem hasDerivAt_dominantPairPolynomial (q : ℝ) :
    HasDerivAt dominantPairPolynomial (dominantPairPolynomialJet q) q := by
  have h := (hasDerivAt_pairShiftEval pairShiftPCoeff (q-3/2)).comp q
    ((hasDerivAt_id q).sub_const (3/2))
  simp only [Function.comp_def,id_eq,mul_one] at h
  apply h.congr_of_eventuallyEq
  filter_upwards with r
  simpa only [show (3/2:ℝ)+(r-3/2)=r by ring] using dominantPairPolynomial_shift_eq (r-3/2)

end
end RHTower.ThetaCuspDefect
