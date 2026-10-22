import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthResidualCenterObstruction
/-!
# Exact dominant cubic absorption for the growth transfer

Retaining the literal point-and-ray cubic kernel gives
J3 <= 2^8 * atomMass * J2 on q >= 3/2. The actual source calibration
399*M0 < 1 then places the normalized cubic contribution strictly below
one quarter of the unweighted dominant pair for every x >= 0.

This repairs the pure cubic estimate responsible for the coarse residual's
actual-center failure. Mixed deep-tail terms and other odd sectors remain
separate obligations. All polynomial identities use default proof limits.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section

/-- Exact numerator for three copies of the dominant point-and-ray component. -/
def tripleMomentPolynomial (q : ℝ) (j : ℕ) : ℝ :=
  64*9^j*q^(j+3)+
    216*q^2*(∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*9^(j-i)*(i.factorial:ℝ)*q^(j-i))+
    243*q*(∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*9^(j-i)*((i+1).factorial:ℝ)*q^(j-i))+
    (729/16)*∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*9^(j-i)*((i+2).factorial:ℝ)*q^(j-i)

private theorem tripleMomentPolynomial_0 (q : ℝ) :
    momentConvolution (polynomialMoment q 3)
      (momentConvolution (polynomialMoment q 3) (polynomialMoment q 3)) 0=
      tripleMomentPolynomial q 0 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

private theorem tripleMomentPolynomial_1 (q : ℝ) :
    momentConvolution (polynomialMoment q 3)
      (momentConvolution (polynomialMoment q 3) (polynomialMoment q 3)) 1=
      tripleMomentPolynomial q 1 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

private theorem tripleMomentPolynomial_2 (q : ℝ) :
    momentConvolution (polynomialMoment q 3)
      (momentConvolution (polynomialMoment q 3) (polynomialMoment q 3)) 2=
      tripleMomentPolynomial q 2 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

private theorem tripleMomentPolynomial_3 (q : ℝ) :
    momentConvolution (polynomialMoment q 3)
      (momentConvolution (polynomialMoment q 3) (polynomialMoment q 3)) 3=
      tripleMomentPolynomial q 3 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

private theorem tripleMomentPolynomial_4 (q : ℝ) :
    momentConvolution (polynomialMoment q 3)
      (momentConvolution (polynomialMoment q 3) (polynomialMoment q 3)) 4=
      tripleMomentPolynomial q 4 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

private theorem tripleMomentPolynomial_5 (q : ℝ) :
    momentConvolution (polynomialMoment q 3)
      (momentConvolution (polynomialMoment q 3) (polynomialMoment q 3)) 5=
      tripleMomentPolynomial q 5 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

private theorem tripleMomentPolynomial_6 (q : ℝ) :
    momentConvolution (polynomialMoment q 3)
      (momentConvolution (polynomialMoment q 3) (polynomialMoment q 3)) 6=
      tripleMomentPolynomial q 6 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

private theorem tripleMomentPolynomial_7 (q : ℝ) :
    momentConvolution (polynomialMoment q 3)
      (momentConvolution (polynomialMoment q 3) (polynomialMoment q 3)) 7=
      tripleMomentPolynomial q 7 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

private theorem tripleMomentPolynomial_8 (q : ℝ) :
    momentConvolution (polynomialMoment q 3)
      (momentConvolution (polynomialMoment q 3) (polynomialMoment q 3)) 8=
      tripleMomentPolynomial q 8 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem tripleMomentPolynomial_eq (q : ℝ) {j : ℕ} (hj : j ≤ 8) :
    momentConvolution (polynomialMoment q 3)
      (momentConvolution (polynomialMoment q 3) (polynomialMoment q 3)) j=
      tripleMomentPolynomial q j := by
  interval_cases j
  · exact tripleMomentPolynomial_0 q
  · exact tripleMomentPolynomial_1 q
  · exact tripleMomentPolynomial_2 q
  · exact tripleMomentPolynomial_3 q
  · exact tripleMomentPolynomial_4 q
  · exact tripleMomentPolynomial_5 q
  · exact tripleMomentPolynomial_6 q
  · exact tripleMomentPolynomial_7 q
  · exact tripleMomentPolynomial_8 q

def dominantTriplePolynomial (q : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 6,
    ((growthCoefficient q (i+2)*slopeNumerator q 3-
      q*growthCoefficientJet q (i+2)*growthNumerator q 3)*q^(5-i)*tripleMomentPolynomial q (i+2)+
      growthCoefficient q (i+2)*growthNumerator q 3*q^(5-i)*tripleMomentPolynomial q (i+3))

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

/-- The shifted dominant pair polynomial as an explicit polynomial in `y`. -/
private theorem dominantPairPolynomial_shift_eq_explicit (y : ℝ) :
    dominantPairPolynomial (3/2+y)=pairShiftP y := by
  unfold pairShiftP
  unfold dominantPairPolynomial anchorCoolingNumerator binaryGrowthNumerator binarySlopeNumerator
    growthNumerator slopeNumerator
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo,binaryMoment]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem exactCubic_pair_reserve_shift (y : ℝ) (hy : 0 ≤ y) :
    dominantTriplePolynomial (3/2+y) ≤
      (2:ℝ)^8*polynomialMoment (3/2+y) 3 0*dominantPairPolynomial (3/2+y) := by
  rw [dominantPairPolynomial_shift_eq_explicit]
  unfold dominantTriplePolynomial growthNumerator slopeNumerator
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo,binaryMoment]
  unfold polynomialMoment tripleMomentPolynomial
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold pairShiftP
  apply sub_nonneg.mp
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity
theorem momentConvolution_powerScale (q : ℝ) (a b : ℕ) (m n : ℕ → ℝ) (j : ℕ) :
    momentConvolution (fun i => q^(i+a)*m i) (fun i => q^(i+b)*n i) j=
      q^(j+a+b)*momentConvolution m n j := by
  unfold momentConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
  have hp : q^(i+a)*q^(j-i+b)=q^(j+a+b) := by
    rw [←pow_add]
    congr 1
    omega
  calc
    _=(q^(i+a)*q^(j-i+b))*((j.choose i:ℝ)*m i*n (j-i)) := by ring
    _=_ := by rw [hp]

theorem spectralPowerMoment_three (m : ℕ → ℝ) {j : ℕ} (hj : j ≤ 8) :
    spectralPowerMoment m 3 j=momentConvolution m (momentConvolution m m) j := by
  rw [show 3=2+1 by rfl,spectralPowerMoment_succ m 2 hj]
  unfold momentConvolution
  apply Finset.sum_congr rfl
  intro i hi
  rw [spectralPowerMoment_two m (by omega : j-i ≤ 8)]
  rfl

theorem spectralPowerMoment_bare_three {q : ℝ} (hq : 0 < q) {j : ℕ} (hj : j ≤ 8) :
    spectralPowerMoment (bareMoment q 3) 3 j=tripleMomentPolynomial q j/q^(j+3) := by
  rw [spectralPowerMoment_three _ hj]
  have he : polynomialMoment q 3=fun i => q^(i+1)*bareMoment q 3 i := by
    funext i
    rw [bareMoment_eq_polynomial hq.ne']
    field_simp [hq.ne']
  have hpair : momentConvolution (polynomialMoment q 3) (polynomialMoment q 3)=
      fun i => q^(i+2)*momentConvolution (bareMoment q 3) (bareMoment q 3) i := by
    rw [he]
    funext i
    simpa only [Nat.add_assoc,show (1:ℕ)+1=2 by rfl] using
      momentConvolution_powerScale q 1 1 (bareMoment q 3) (bareMoment q 3) i
  have hp := tripleMomentPolynomial_eq q hj
  rw [hpair,he,momentConvolution_powerScale] at hp
  apply (eq_div_iff (pow_ne_zero _ hq.ne')).mpr
  simpa only [Nat.add_assoc,show (1:ℕ)+2=3 by rfl,mul_comm] using hp

theorem growthTransferFunctional_bare_three {q : ℝ} (hq : 0 < q) :
    growthTransferFunctional q (spectralPowerMoment (bareMoment q 3) 3)=
      dominantTriplePolynomial q/q^10 := by
  unfold growthTransferFunctional dominantTriplePolynomial
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi5 : i ≤ 5 := by have := Finset.mem_range.mp hi; omega
  rw [spectralPowerMoment_bare_three hq (by omega : i+2 ≤ 8),
    spectralPowerMoment_bare_three hq (by omega : i+3 ≤ 8)]
  interval_cases i <;> norm_num only [Nat.reduceAdd,Nat.reduceSub] <;>
    field_simp [hq.ne']

theorem exactCubic_pair_reserve {q : ℝ} (hq : 3/2 ≤ q) :
    growthTransferFunctional q (spectralPowerMoment (bareMoment q 3) 3) ≤
      (2:ℝ)^8*bareMoment q 3 0*
        growthTransferFunctional q (spectralPowerMoment (bareMoment q 3) 2) := by
  have hq0 : 0 < q := by linarith
  have hs := exactCubic_pair_reserve_shift (q-3/2) (by linarith)
  rw [show (3/2:ℝ)+(q-3/2)=q by ring] at hs
  rw [growthTransferFunctional_bare_three hq0,growthTransferFunctional_bare_pair hq0,
    bareMoment_eq_polynomial hq0.ne']
  calc
    _ ≤ ((2:ℝ)^8*polynomialMoment q 3 0*dominantPairPolynomial q)/q^10 :=
      div_le_div_of_nonneg_right hs (pow_pos hq0 10).le
    _ = _ := by norm_num only [Nat.zero_add,pow_one]; field_simp [hq0.ne']

theorem dominantCubic_transfer_le_pair {q : ℝ} (hq : 3/2 ≤ q) :
    growthTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 3) ≤
      (2:ℝ)^8*atomMoment 2 q 0*dominantPairTransfer q := by
  have hq0 : 0 < q := by linarith
  have ham : atomMoment 2 q=fun j => dominantAtomScale q*bareMoment q 3 j := by
    funext j
    exact atomMoment_two_eq_scale hq0 j
  have ht : spectralPowerMoment (atomMoment 2 q) 3=
      fun j => dominantAtomScale q^3*spectralPowerMoment (bareMoment q 3) 3 j := by
    rw [ham]
    funext j
    exact spectralPowerMoment_smul _ _ _ _
  have hp : spectralPowerMoment (atomMoment 2 q) 2=
      fun j => dominantAtomScale q^2*spectralPowerMoment (bareMoment q 3) 2 j := by
    rw [ham]
    funext j
    exact spectralPowerMoment_smul _ _ _ _
  unfold dominantPairTransfer
  rw [ht,hp,growthTransferFunctional_smul,growthTransferFunctional_smul,ham]
  have h := mul_le_mul_of_nonneg_left (exactCubic_pair_reserve hq)
    (pow_pos (dominantAtomScale_pos q) 3).le
  nlinarith only [h]

/-- Exact cubic absorption leaves at least one quarter of the unweighted literal pair. -/
theorem dominantCubic_weighted_lt_quarter_pair {x : ℝ} (hx : 0 ≤ x) :
    normalizedTransferWeight (thetaCuspLikelihoodCoordinate x) 3*
      growthTransferFunctional (thetaCuspLikelihoodCoordinate x)
        (spectralPowerMoment (atomMoment 2 (thetaCuspLikelihoodCoordinate x)) 3) <
      dominantPairTransfer (thetaCuspLikelihoodCoordinate x)/4 := by
  let q := thetaCuspLikelihoodCoordinate x
  have hq0 : 0 < q := thetaCuspLikelihoodCoordinate_pos hx
  have hq : (3/2:ℝ) ≤ q := by
    have hexp : 1 ≤ Real.exp x := Real.one_le_exp hx
    have hsq : 1 ≤ Real.exp x^2 := by nlinarith [Real.exp_pos x]
    dsimp only [q,thetaCuspLikelihoodCoordinate]
    nlinarith [Real.pi_gt_three,Real.pi_pos]
  have hpair : 0 < dominantPairTransfer q := growthTransferFunctional_dominant_pair_pos hq
  have ha0 : 0 ≤ atomMoment 2 q 0 := by
    simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      thetaCuspSecondAtomMoment_nonneg q 0
  have hM : atomMoment 2 q 0 ≤ thetaCuspHigherLikelihoodSpectralMoment q 0 := by
    have he : thetaCuspHigherLikelihoodSpectralMoment q 0=
        atomMoment 2 q 0+thetaCuspDeepTailMoment q 0 := by
      simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
        thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep hq0 0
    rw [he]
    exact le_add_of_nonneg_right (thetaCuspDeepTailMoment_nonneg q 0)
  have hactivity := three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one hx
  change 399*thetaCuspHigherLikelihoodSpectralResponse q < 1 at hactivity
  rw [←thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hq0] at hactivity
  have hmass : 399*atomMoment 2 q 0 < 1 := by linarith
  have hJ := dominantCubic_transfer_le_pair hq
  have hW := normalizedTransferWeight_le hq0 (k:=3) (by omega)
  have hw0 := (normalizedTransferWeight_pos hq0 (k:=3) (by omega)).le
  have hu : 0 ≤ (2:ℝ)^8*atomMoment 2 q 0*dominantPairTransfer q := by positivity
  have h1 := mul_le_mul_of_nonneg_left hJ hw0
  have h2 := mul_le_mul_of_nonneg_right hW hu
  have h3 := mul_lt_mul_of_pos_right hmass hpair
  change normalizedTransferWeight q 3*
    growthTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 3)<dominantPairTransfer q/4
  norm_num at h1 h2
  nlinarith only [h1,h2,h3,hpair]

end
end RHTower.ThetaCuspDefect


