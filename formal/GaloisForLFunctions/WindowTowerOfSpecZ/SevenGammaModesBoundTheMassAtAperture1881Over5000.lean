import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaRemainderRetainsHigherLags
import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstFoldRetainsTwoMomentCharges

/-!
# Gamma mass at the first-overlap aperture

Seven positive Laplace modes bound the Gamma tail. Rational Taylor bounds
for the exponential and logarithm give the retained local mass constant.
-/

noncomputable section
open Real MeasureTheory Set Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilLevyPoleGauss _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticCriticalityTheory ArithmeticIncidencePositivity BiScaleUncertainty

private theorem gamma_tail_finite_modes {r : ℝ} (hr : 0 < r) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      2 * Real.exp (-r / 2) ^ (4 * n + 1) / (4 * (n : ℝ) + 1)) ≤ archLevyAntideriv r := by
  let f (n : ℕ) (t : ℝ) := Real.exp (-(2 * (n : ℝ) + 1 / 2) * t)
  have hi (n : ℕ) : IntegrableOn (f n) (Ioi r) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos (by positivity)) r
  have hpoint {t : ℝ} (ht : 0 < t) : (∑ n ∈ Finset.range N, f n t) ≤ archLevyDensity t := by
    have h := Summable.sum_le_tsum (Finset.range N)
      (fun n _ => (Real.exp_pos (-(2 * (n : ℝ) + 1 / 2) * t)).le)
      (hasSum_archLevyDensity ht).summable
    rw [← _root_.RHTower.ArchimedeanAnomaly.archLevyDensity_eq_tsum ht] at h
    simpa only [f, neg_mul] using h
  have h := setIntegral_mono_on (integrable_finsetSum _ (fun n _ => hi n))
    (WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hr) measurableSet_Ioi
    (fun t ht => hpoint (hr.trans ht))
  rw [integral_finsetSum _ (fun n _ => hi n),
    WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hr] at h
  have heq : (∑ n ∈ Finset.range N,
      2 * Real.exp (-r / 2) ^ (4 * n + 1) / (4 * (n : ℝ) + 1)) =
      ∑ n ∈ Finset.range N, ∫ t in Ioi r, f n t := by
    apply Finset.sum_congr rfl
    intro n _
    have he : Real.exp (-r / 2) ^ (4 * n + 1) = Real.exp (-(2 * (n : ℝ) + 1 / 2) * r) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [he]
    dsimp only [f]
    rw [integral_exp_mul_Ioi (neg_neg_of_pos (by positivity))]
    field_simp [show (4 * (n : ℝ) + 1) ≠ 0 by positivity,
      show (2 * (n : ℝ) + 1 / 2) ≠ 0 by positivity]
    ring
  exact heq.le.trans h

private theorem exp_neg_aperture_lower :
    (686464 / 1000000 : ℝ) ≤ Real.exp (-(1881 / 5000 : ℝ)) := by
  have h := taylor_seven_le_exp (x := -(1881 / 5000 : ℝ)) (by norm_num)
  norm_num at h
  linarith only [h]

private theorem log_pi_upper : Real.log Real.pi ≤ (1144731 / 1000000 : ℝ) := by
  let x : ℝ := (1144731 / 1000000) / 4
  let q : ℝ := 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 +
    x ^ 6 / 720 - x ^ 7 / 4410
  have hx : 0 ≤ x := by norm_num [x]
  have hq : q ≤ Real.exp x := by
    have h := taylor_seven_le_exp (x := x) (by norm_num [x])
    simpa only [abs_of_nonneg hx] using h
  have hp := pow_le_pow_left₀ (by norm_num [q, x] : 0 ≤ q) hq 4
  have he : Real.exp x ^ 4 = Real.exp (1144731 / 1000000 : ℝ) := by
    rw [← Real.exp_nat_mul]
    norm_num [x]
  rw [he] at hp
  have hpi : Real.pi ≤ Real.exp (1144731 / 1000000 : ℝ) := by
    have hu := Real.pi_lt_d6
    norm_num [q, x] at hp
    linarith only [hu, hp]
  have h := Real.log_le_log Real.pi_pos hpi
  simpa only [Real.log_exp] using h

/-- At the first-overlap aperture, seven Gamma modes retain the local mass constant. -/
theorem gamma_mass_constant_at_aperture_1881_over_5000 :
    -(14379 / 10000 : ℝ) ≤ EF.gammaBracket 0 + Real.log 2 + (1881 / 2500 : ℝ) / 2 -
      (1881 / 2500 : ℝ) ^ 2 / 48 - (1881 / 2500 : ℝ) ^ 3 / 48 +
      2 * archLevyAntideriv (1881 / 2500) := by
  have htail := gamma_tail_finite_modes (r := (1881 / 2500 : ℝ)) (by norm_num) 7
  have hq : (686464 / 1000000 : ℝ) ≤ Real.exp (-(1881 / 2500 : ℝ) / 2) := by
    convert exp_neg_aperture_lower using 1
    norm_num
  have hsum : (∑ n ∈ Finset.range 7,
      2 * (686464 / 1000000 : ℝ) ^ (4 * n + 1) / (4 * (n : ℝ) + 1)) ≤
      ∑ n ∈ Finset.range 7,
        2 * Real.exp (-(1881 / 2500 : ℝ) / 2) ^ (4 * n + 1) / (4 * (n : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro n _
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hq _) (by norm_num))
      (by positivity)
  have hA := hsum.trans htail
  norm_num [Finset.sum_range_succ] at hA
  have hg := _root_.RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hbr := neg_gammaBracket_zero_eq
  have hl := Real.log_two_lt_d9
  have hp := Real.pi_lt_d6
  norm_num at hl hp
  linarith only [hA, hg, hbr, hl, hp, log_pi_upper]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.gamma_mass_constant_at_aperture_1881_over_5000
