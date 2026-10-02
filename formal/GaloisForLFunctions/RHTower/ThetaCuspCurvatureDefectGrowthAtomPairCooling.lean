import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthTransferKernelDerivative
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthPairRelativeCooling
/-!
# Exact third-atom cooling relative to the dominant growth pair

The literal n=3 theta atom, including its ray component, has strictly
 decreasing growth transfer relative to the literal n=2 self-pair on
q >= 3/2. The proof preserves the exact atom polynomial and certifies
the quotient Wronskian by positive shifted coefficients. No sign of
the full cumulant transfer or source growth is assumed here.
-/

namespace RHTower.ThetaCuspDefect
noncomputable section

def atomTransferNumerator (q d : ℝ) : ℝ :=
  slopeNumerator q 3*growthNumerator q d-growthNumerator q 3*slopeNumerator q d

def atomTransferNumeratorJet (q d : ℝ) : ℝ :=
  slopeNumeratorJet q 3*growthNumerator q d+slopeNumerator q 3*growthNumeratorJet q d-
    (growthNumeratorJet q 3*slopeNumerator q d+growthNumerator q 3*slopeNumeratorJet q d)

theorem hasDerivAt_atomTransferNumerator (q d : ℝ) :
    HasDerivAt (fun r => atomTransferNumerator r d) (atomTransferNumeratorJet q d) q := by
  exact (((hasDerivAt_slopeNumerator q 3).mul (hasDerivAt_growthNumerator q d)).sub
    ((hasDerivAt_growthNumerator q 3).mul (hasDerivAt_slopeNumerator q d))).congr_deriv (by unfold atomTransferNumeratorJet; ring)

def atomPairTransferWronskian (q d : ℝ) : ℝ :=
  ((q*(d-6)-1)*atomTransferNumerator q d-q*atomTransferNumeratorJet q d)*dominantPairPolynomial q+
    q*atomTransferNumerator q d*dominantPairPolynomialJet q

theorem growthTransferFunctional_bare_atom {q : ℝ} (hq : 0 < q) (d : ℝ) :
    growthTransferFunctional q (bareMoment q d)=atomTransferNumerator q d/q^8 := by
  rw [growthTransferFunctional_eq,growthFunctional_bare_polynomial hq.ne',
    growthSlope_bare_polynomial hq.ne']
  unfold atomTransferNumerator
  field_simp [hq.ne']

theorem dominantPairPolynomial_pos {q : ℝ} (hq : 3/2 ≤ q) : 0 < dominantPairPolynomial q := by
  have hq0 : 0 < q := by linarith
  have h := mul_pos (growthTransferFunctional_dominant_pair_pos hq) (pow_pos hq0 9)
  change 0 < dominantPairTransfer q*q^9 at h
  rw [dominantPairTransfer_eq hq0,div_mul_cancel₀ _ (pow_ne_zero 9 hq0.ne')] at h
  exact pos_of_mul_pos_right h (sq_nonneg _)

def atomPairPolynomialRatio (q d : ℝ) : ℝ :=
  Real.exp (-(d-6)*q)*q*atomTransferNumerator q d/dominantPairPolynomial q

theorem hasDerivAt_atomPairPolynomialRatio {q : ℝ} (hq : 3/2 ≤ q) (d : ℝ) :
    HasDerivAt (fun r => atomPairPolynomialRatio r d)
      (-Real.exp (-(d-6)*q)*atomPairTransferWronskian q d/dominantPairPolynomial q^2) q := by
  have he := ((hasDerivAt_id q).const_mul (-(d-6))).exp
  have ha := hasDerivAt_atomTransferNumerator q d
  have hp := dominantPairPolynomial_pos hq
  have h := (((he.mul (hasDerivAt_id q)).mul ha).div
    (hasDerivAt_dominantPairPolynomial q) hp.ne')
  exact h.congr_deriv (by
    unfold atomPairTransferWronskian
    simp only [Pi.mul_apply,id_eq,mul_one]
    ring)

def atomEightShiftCoeff : ℕ → ℝ
  | 0 => 225323890614320135043825/8192
  | 1 => 7456294099781558365586445/16384
  | 2 => 60100430620053156735401685/16384
  | 3 => 317530715589975476963331045/16384
  | 4 => 1242627233324102139012863535/16384
  | 5 => 240087822861288585359195505/1024
  | 6 => 304128969334783407587099655/512
  | 7 => 645360879061440557831677815/512
  | 8 => 1162552975055838193997181825/512
  | 9 => 224213881650743882851602435/64
  | 10 => 298209213478884226080911535/64
  | 11 => 171802931847931714132610235/32
  | 12 => 172181155603999912241711265/32
  | 13 => 4705325159551779492771480
  | 14 => 7198233530938142657844825/2
  | 15 => 2411991313767156629902230
  | 16 => 1417443125592304172839050
  | 17 => 730462616151357885013620
  | 18 => 329816992923126340318260
  | 19 => 130232476381582694825460
  | 20 => 44837063800060285083420
  | 21 => 13401627455525190045120
  | 22 => 3457197177297200363520
  | 23 => 763695616647081306240
  | 24 => 142957841705033857920
  | 25 => 22362546645828725760
  | 26 => 2868148960333839360
  | 27 => 293656591463546880
  | 28 => 23070909942743040
  | 29 => 1305398630154240
  | 30 => 47332385095680
  | 31 => 825564856320
  | _ => 0

theorem atomTransferNumerator_eight_shift_eq (y : ℝ) :
    atomTransferNumerator (3/2+y) 8=pairShiftEval atomEightShiftCoeff y := by
  unfold atomTransferNumerator growthNumerator slopeNumerator pairShiftEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [atomEightShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem atomTransferNumeratorJet_eight_shift_eq (y : ℝ) :
    atomTransferNumeratorJet (3/2+y) 8=pairShiftJet atomEightShiftCoeff y := by
  have h := (hasDerivAt_atomTransferNumerator (3/2+y) 8).comp y
    ((hasDerivAt_id y).const_add (3/2))
  have he : (fun r : ℝ => atomTransferNumerator (3/2+r) 8)=pairShiftEval atomEightShiftCoeff := by
    funext r
    exact atomTransferNumerator_eight_shift_eq r
  simp only [Function.comp_def,mul_one] at h
  rw [he] at h
  have hp : HasDerivAt (pairShiftEval atomEightShiftCoeff) (pairShiftJet atomEightShiftCoeff y) y := by
    unfold pairShiftEval pairShiftJet
    apply HasDerivAt.fun_sum
    intro j hj
    simpa only [mul_assoc] using (hasDerivAt_pow j y).const_mul (atomEightShiftCoeff j)
  exact h.unique hp

private def atomEightCacheA (y : ℝ) : ℝ :=
  (225323890614320135043825/8192)*y^0+
    (7456294099781558365586445/16384)*y^1+
    (60100430620053156735401685/16384)*y^2+
    (317530715589975476963331045/16384)*y^3+
    (1242627233324102139012863535/16384)*y^4+
    (240087822861288585359195505/1024)*y^5+
    (304128969334783407587099655/512)*y^6+
    (645360879061440557831677815/512)*y^7+
    (1162552975055838193997181825/512)*y^8+
    (224213881650743882851602435/64)*y^9+
    (298209213478884226080911535/64)*y^10+
    (171802931847931714132610235/32)*y^11+
    (172181155603999912241711265/32)*y^12+
    (4705325159551779492771480)*y^13+
    (7198233530938142657844825/2)*y^14+
    (2411991313767156629902230)*y^15+
    (1417443125592304172839050)*y^16+
    (730462616151357885013620)*y^17+
    (329816992923126340318260)*y^18+
    (130232476381582694825460)*y^19+
    (44837063800060285083420)*y^20+
    (13401627455525190045120)*y^21+
    (3457197177297200363520)*y^22+
    (763695616647081306240)*y^23+
    (142957841705033857920)*y^24+
    (22362546645828725760)*y^25+
    (2868148960333839360)*y^26+
    (293656591463546880)*y^27+
    (23070909942743040)*y^28+
    (1305398630154240)*y^29+
    (47332385095680)*y^30+
    (825564856320)*y^31

private theorem atomEightCacheA_eq (y : ℝ) : pairShiftEval atomEightShiftCoeff y=atomEightCacheA y := by
  norm_num [pairShiftEval,atomEightShiftCoeff,atomEightCacheA,Finset.sum_range_succ]

private def atomEightCacheAJet (y : ℝ) : ℝ :=
  (7456294099781558365586445/16384)*(1:ℝ)*y^(1-1)+
    (60100430620053156735401685/16384)*(2:ℝ)*y^(2-1)+
    (317530715589975476963331045/16384)*(3:ℝ)*y^(3-1)+
    (1242627233324102139012863535/16384)*(4:ℝ)*y^(4-1)+
    (240087822861288585359195505/1024)*(5:ℝ)*y^(5-1)+
    (304128969334783407587099655/512)*(6:ℝ)*y^(6-1)+
    (645360879061440557831677815/512)*(7:ℝ)*y^(7-1)+
    (1162552975055838193997181825/512)*(8:ℝ)*y^(8-1)+
    (224213881650743882851602435/64)*(9:ℝ)*y^(9-1)+
    (298209213478884226080911535/64)*(10:ℝ)*y^(10-1)+
    (171802931847931714132610235/32)*(11:ℝ)*y^(11-1)+
    (172181155603999912241711265/32)*(12:ℝ)*y^(12-1)+
    (4705325159551779492771480)*(13:ℝ)*y^(13-1)+
    (7198233530938142657844825/2)*(14:ℝ)*y^(14-1)+
    (2411991313767156629902230)*(15:ℝ)*y^(15-1)+
    (1417443125592304172839050)*(16:ℝ)*y^(16-1)+
    (730462616151357885013620)*(17:ℝ)*y^(17-1)+
    (329816992923126340318260)*(18:ℝ)*y^(18-1)+
    (130232476381582694825460)*(19:ℝ)*y^(19-1)+
    (44837063800060285083420)*(20:ℝ)*y^(20-1)+
    (13401627455525190045120)*(21:ℝ)*y^(21-1)+
    (3457197177297200363520)*(22:ℝ)*y^(22-1)+
    (763695616647081306240)*(23:ℝ)*y^(23-1)+
    (142957841705033857920)*(24:ℝ)*y^(24-1)+
    (22362546645828725760)*(25:ℝ)*y^(25-1)+
    (2868148960333839360)*(26:ℝ)*y^(26-1)+
    (293656591463546880)*(27:ℝ)*y^(27-1)+
    (23070909942743040)*(28:ℝ)*y^(28-1)+
    (1305398630154240)*(29:ℝ)*y^(29-1)+
    (47332385095680)*(30:ℝ)*y^(30-1)+
    (825564856320)*(31:ℝ)*y^(31-1)

private theorem atomEightCacheAJet_eq (y : ℝ) : pairShiftJet atomEightShiftCoeff y=atomEightCacheAJet y := by
  norm_num [pairShiftJet,atomEightShiftCoeff,atomEightCacheAJet,Finset.sum_range_succ]

private def atomEightCacheP (y : ℝ) : ℝ :=
  (1861439671925411064321195/262144)*y^0+
    (17029102555455663849163083/131072)*y^1+
    (322103250906652692527224995/262144)*y^2+
    (3986068609578601786146770907/524288)*y^3+
    (17747426224968762775188708801/524288)*y^4+
    (60205290770051699808697176159/524288)*y^5+
    (161889339980151795383364100185/524288)*y^6+
    (88783224129787319215420379949/131072)*y^7+
    (40584482588850241239154879101/32768)*y^8+
    (125732997201449447835433962975/65536)*y^9+
    (83526071203783400209001293023/32768)*y^10+
    (24021870812074579694285775753/8192)*y^11+
    (3012388545381711954421912695/1024)*y^12+
    (10598204705085701542133692191/4096)*y^13+
    (2051032002969296969786490399/1024)*y^14+
    (350249683977929583797321241/256)*y^15+
    (52856430502952134902727413/64)*y^16+
    (56420609017661702586319923/128)*y^17+
    (13306021597836988576698663/64)*y^18+
    (1384664906267936886187899/16)*y^19+
    (253708974997061236411869/8)*y^20+
    (40781033052359698188063/4)*y^21+
    (22891888988441303827797/8)*y^22+
    (1393460938024037275545/2)*y^23+
    (145953189487990653714)*y^24+
    (26021377372028465547)*y^25+
    (3892209828844085190)*y^26+
    (479089069751214504)*y^27+
    (47234407851478656)*y^28+
    (3584618003916144)*y^29+
    (196488958170240)*y^30+
    (6920535241728)*y^31+
    (117546246144)*y^32

private theorem atomEightCacheP_eq (y : ℝ) : pairShiftEval pairShiftPCoeff y=atomEightCacheP y := by
  norm_num [pairShiftEval,pairShiftPCoeff,atomEightCacheP,Finset.sum_range_succ]

private def atomEightCachePJet (y : ℝ) : ℝ :=
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
    (145953189487990653714)*(24:ℝ)*y^(24-1)+
    (26021377372028465547)*(25:ℝ)*y^(25-1)+
    (3892209828844085190)*(26:ℝ)*y^(26-1)+
    (479089069751214504)*(27:ℝ)*y^(27-1)+
    (47234407851478656)*(28:ℝ)*y^(28-1)+
    (3584618003916144)*(29:ℝ)*y^(29-1)+
    (196488958170240)*(30:ℝ)*y^(30-1)+
    (6920535241728)*(31:ℝ)*y^(31-1)+
    (117546246144)*(32:ℝ)*y^(32-1)

private theorem atomEightCachePJet_eq (y : ℝ) : pairShiftJet pairShiftPCoeff y=atomEightCachePJet y := by
  norm_num [pairShiftJet,pairShiftPCoeff,atomEightCachePJet,Finset.sum_range_succ]

theorem atomPairTransferWronskian_eight_shift_pos (y : ℝ) (hy : 0 ≤ y) : 0 < atomPairTransferWronskian (3/2+y) 8 := by
  unfold atomPairTransferWronskian
  rw [dominantPairPolynomial_shift_eq,atomTransferNumerator_eight_shift_eq,
    atomTransferNumeratorJet_eight_shift_eq]
  unfold dominantPairPolynomialJet
  rw [show (3/2:ℝ)+y-3/2=y by ring]
  rw [atomEightCacheA_eq,atomEightCacheAJet_eq,atomEightCacheP_eq,atomEightCachePJet_eq]
  unfold atomEightCacheA atomEightCacheAJet atomEightCacheP atomEightCachePJet
  norm_num only [Nat.reduceSub,Nat.cast_ofNat]
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,
    Mathlib.Tactic.RingNF.nat_rawCast_1,Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

open Filter Set Topology

theorem atomPairTransferWronskian_eight_pos {q : ℝ} (hq : 3/2 ≤ q) :
    0 < atomPairTransferWronskian q 8 := by
  have h := atomPairTransferWronskian_eight_shift_pos (q-3/2) (by linarith)
  simpa only [show (3/2:ℝ)+(q-3/2)=q by ring] using h

theorem atomPairPolynomialRatio_eight_strictAntiOn :
    StrictAntiOn (fun q => atomPairPolynomialRatio q 8) (Ici (3/2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro q hq
    exact (hasDerivAt_atomPairPolynomialRatio hq 8).continuousAt.continuousWithinAt
  · intro q hq
    have hq' : 3/2 < q := by simpa only [interior_Ici,mem_Ioi] using hq
    rw [(hasDerivAt_atomPairPolynomialRatio hq'.le 8).deriv]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _))
        (atomPairTransferWronskian_eight_pos hq'.le))
      (pow_pos (dominantPairPolynomial_pos hq'.le) 2)

theorem thirdAtomTransfer_relative_eq {q : ℝ} (hq : 3/2 ≤ q) :
    growthTransferFunctional q (atomMoment 3 q)/dominantPairTransfer q =
      (9*Real.exp (-3)/16)*atomPairPolynomialRatio q 8 := by
  have hq0 : 0 < q := by linarith
  have ham : atomMoment 3 q=(fun j => Real.exp (-12)*Real.exp (-8*q)*9*bareMoment q 8 j) := by
    funext j
    rw [atomMoment_eq_bare (by omega : 2 ≤ (3:ℕ)) hq0,
      show thetaCuspLikelihoodGap 3=(8:ℝ) by norm_num [thetaCuspLikelihoodGap],
      show -(3/2)*(8:ℝ)=-12 by ring,show -q*(8:ℝ)=-8*q by ring]
    ring
  have he : Real.exp (-12)*Real.exp (-8*q)=
      Real.exp (-3)*Real.exp (-(8-6)*q)*(Real.exp (-(9/2))*Real.exp (-3*q))^2 := by
    rw [pow_two]
    simp only [← Real.exp_add]
    congr 1
    ring
  have hs : Real.exp (-12)*Real.exp (-8*q)*9=
      (9*Real.exp (-3)/16)*Real.exp (-(8-6)*q)*dominantAtomScale q^2 := by
    rw [he]
    unfold dominantAtomScale
    ring
  rw [ham,growthTransferFunctional_smul,growthTransferFunctional_bare_atom hq0,
    dominantPairTransfer_eq hq0,hs]
  unfold atomPairPolynomialRatio
  field_simp [hq0.ne',(dominantAtomScale_pos q).ne',(dominantPairPolynomial_pos hq).ne']

theorem thirdAtomTransfer_relative_strictAntiOn :
    StrictAntiOn (fun q => growthTransferFunctional q (atomMoment 3 q)/dominantPairTransfer q)
      (Ici (3/2)) := by
  intro q hq r hr hqr
  dsimp only
  rw [thirdAtomTransfer_relative_eq hq,thirdAtomTransfer_relative_eq hr]
  exact mul_lt_mul_of_pos_left (atomPairPolynomialRatio_eight_strictAntiOn hq hr hqr)
    (by positivity)

end
end RHTower.ThetaCuspDefect
