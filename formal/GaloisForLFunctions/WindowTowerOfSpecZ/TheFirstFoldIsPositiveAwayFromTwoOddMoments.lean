import GaloisForLFunctions.WindowTowerOfSpecZ.TheCubicMomentPaysTheFrozenOddComplement
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicLagGap
import GaloisForLFunctions.ArithmeticIncidencePositivity.SharedDerivativeEnergyAndGlobalAllocationSynthesis

/-!
# The complete first fold away from two odd moments

The fifth regional harmonic level pays the Gamma term and the signed prime-2
cost on the unit support window. Vanishing first moment also removes the linear
part of the sinh pole. The remaining two low moments retain the sign problem.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilMarkovPole _root_.RHTower.WeilLevyPoleGauss
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory ArithmeticIncidencePositivity ArithmeticCriticalityTheory
open BiScaleUncertainty SpacingScaleHarmonicAnalysis

private theorem two_moment_autocorr_half (F : ℝ → ℝ) (t : ℝ) :
    autocorr (fun x => F ((1 / 2) * x)) t = 2 * autocorr F ((1 / 2) * t) := by
  unfold autocorr
  have h := Measure.integral_comp_mul_left (fun x => F x * F (x + (1 / 2) * t)) (1 / 2 : ℝ)
  norm_num [smul_eq_mul] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with x
  rw [mul_add]

private theorem odd_two_moment_logarithmic_gap_half {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hs : ∀ x, (1 / 2 : ℝ) ≤ |x| → F x = 0) (ho : ∀ x, F (-x) = -F x)
    (h1 : (∫ x, F x * x) = 0) (h3 : (∫ x, F x * x ^ 3) = 0) :
    (137 / 60 + Real.log 2) * (∫ x, F x ^ 2) ≤
      ∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t := by
  let U : ℝ → ℝ := fun x => F ((1 / 2) * x)
  have hU : ContDiff ℝ 1 U := hF.comp (contDiff_const.mul contDiff_id)
  have hUL : ∀ x y, |U x - U y| ≤ (K / 2) * |x - y| := by
    intro x y
    have h := hFL ((1 / 2) * x) ((1 / 2) * y)
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    dsimp [U]
    linarith only [h]
  have hUs : ∀ x, 1 ≤ |x| → U x = 0 := by
    intro x hx
    apply hs
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith only [hx]
  have hUo : ∀ x, U (-x) = -U x := by intro x; dsimp [U]; rw [mul_neg, ho]
  have hmoment (k : ℕ) (hk : (∫ x, F x * x ^ k) = 0) : (∫ x, U x * x ^ k) = 0 := by
    have h := Measure.integral_comp_mul_left (fun x => F x * x ^ k) (1 / 2 : ℝ)
    norm_num [smul_eq_mul, hk] at h
    have he : (fun x => F ((1 / 2) * x) * (((1 / 2) * x) ^ k)) =
        fun x => (1 / 2 : ℝ) ^ k * (U x * x ^ k) := by
      funext x
      dsimp [U]
      rw [mul_pow]
      ring
    rw [he, integral_const_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (by positivity)
  have hU1 : (∫ x, U x * x) = 0 := by
    simpa only [pow_one] using hmoment 1 (by simpa only [pow_one] using h1)
  have hU3 := hmoment 3 h3
  have hgap := odd_two_moment_logarithmic_gap_unit hU hUL hUs hUo hU1 hU3
  have hmass : (∫ x, U x ^ 2) = 2 * ∫ x, F x ^ 2 := by
    have h := Measure.integral_comp_mul_left (fun x => F x ^ 2) (1 / 2 : ℝ)
    norm_num [smul_eq_mul] at h
    exact h
  have hlag : (∫ t in Ioc (0 : ℝ) 2, (autocorr U 0 - autocorr U t) / t) =
      2 * ∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t := by
    have he : ∀ t, (autocorr U 0 - autocorr U t) / t =
        (autocorr F 0 - autocorr F ((1 / 2) * t)) / ((1 / 2) * t) := by
      intro t
      dsimp [U]
      rw [two_moment_autocorr_half F 0, two_moment_autocorr_half F t, mul_zero]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc (fun t _ => he t),
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    have h := intervalIntegral.integral_comp_mul_left
      (fun t => (autocorr F 0 - autocorr F t) / t) (a := 0) (b := 2)
      (by norm_num : (1 / 2 : ℝ) ≠ 0)
    norm_num [smul_eq_mul] at h
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
    exact h
  rw [hmass, hlag] at hgap
  nlinarith only [hgap]

/-- Killing the first moment leaves only the cubic remainder of the sinh pole. -/
private theorem linear_moment_zero_pole_cost {F : ℝ → ℝ} (hFc : Continuous F)
    (hcs : HasCompactSupport F) (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (h1 : (∫ x, F x * x) = 0) :
    sinhPairing F ^ 2 / 2 ≤ (1 / 483840 : ℝ) * (∫ x, F x ^ 2) := by
  let R : ℝ → ℝ := (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
    (fun x => 2 * Real.sinh (x / 2) - x)
  have hc : Continuous (fun x : ℝ => 2 * Real.sinh (x / 2) - x) := by fun_prop
  have hRm : AEStronglyMeasurable R := hc.aestronglyMeasurable.indicator measurableSet_Icc
  have hRsq : (fun x => R x ^ 2) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun x => (2 * Real.sinh (x / 2) - x) ^ 2) := by
    funext x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) <;>
      simp only [R, Set.indicator_apply, hx, if_true, if_false, zero_pow two_ne_zero]
  have hRi : Integrable (fun x => R x ^ 2) := by
    rw [hRsq]
    exact (integrable_indicator_iff measurableSet_Icc).mpr (hc.pow 2).integrableOn_Icc
  have hFi : Integrable (fun x => F x ^ 2) := (hFc.pow 2).integrable_of_hasCompactSupport
    (_root_.RHTower.CHMDPolar.hasCompactSupport_sq hcs)
  have hCS := GaloisForLFunctions.HTGeometry.sq_integral_mul_le hFc.aestronglyMeasurable hRm hFi hRi
  have hRbound : (∫ x, R x ^ 2) ≤ (1 / 241920 : ℝ) := by
    rw [hRsq, integral_indicator measurableSet_Icc]
    have h6 : (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), x ^ 6) = (1 / 448 : ℝ) := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2), integral_pow]
      norm_num
    have hiR : IntegrableOn (fun x : ℝ => (2 * Real.sinh (x / 2) - x) ^ 2)
        (Icc (-(1 / 2 : ℝ)) (1 / 2)) := (hc.pow 2).integrableOn_Icc
    have hi6 : IntegrableOn (fun x : ℝ => x ^ 6)
        (Icc (-(1 / 2 : ℝ)) (1 / 2)) := (continuous_pow 6).integrableOn_Icc
    have h := setIntegral_mono_on (s := Icc (-(1 / 2 : ℝ)) (1 / 2))
      (f := fun x => (2 * Real.sinh (x / 2) - x) ^ 2) (g := fun x => x ^ 6 / 540)
      hiR (hi6.div_const 540) measurableSet_Icc
      (fun _x hx => unit_sinh_linear_residual_square_le (abs_le.mpr hx))
    rw [integral_div, h6] at h
    norm_num at h
    exact h
  have hpoint : (fun x => F x * R x) = (fun x => F x * (2 * Real.sinh (x / 2) - x)) := by
    funext x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
    · simp only [R, Set.indicator_of_mem hx]
    · have hz : F x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      rw [hz, zero_mul, zero_mul]
  have hI1 : Integrable (fun x => F x * (2 * Real.sinh (x / 2))) :=
    (hFc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have hIx : Integrable (fun x => F x * x) :=
    (hFc.mul continuous_id).integrable_of_hasCompactSupport hcs.mul_right
  have hsplit : (∫ x, F x * R x) = sinhPairing F := by
    rw [hpoint]
    simp_rw [mul_sub]
    rw [integral_sub hI1 hIx, h1, sub_zero]
    rfl
  rw [hsplit] at hCS
  have hE : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hm := mul_le_mul_of_nonneg_left hRbound hE
  nlinarith only [hCS, hm]

private theorem unit_window_compact {F : ℝ → ℝ}
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) : HasCompactSupport F :=
  HasCompactSupport.intro isCompact_Icc
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)))

private theorem unit_window_vanish {F : ℝ → ℝ} (hFc : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    ∀ x, (1 / 2 : ℝ) ≤ |x| → F x = 0 := by
  have hz : Ioi (1 / 2 : ℝ) ⊆ {x | F x = 0} := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport fun h => not_le_of_gt hx (hs h).2
  have hzr : ∀ x, (1 / 2 : ℝ) ≤ x → F x = 0 := by
    have h := closure_minimal hz (isClosed_eq hFc continuous_const)
    rw [closure_Ioi] at h
    exact fun x hx => h hx
  intro x hx
  rcases le_total 0 x with hx0 | hx0
  · exact hzr x (by rwa [abs_of_nonneg hx0] at hx)
  · have hneg := hzr (-x) (by rwa [abs_of_nonpos hx0] at hx)
    rw [ho] at hneg
    exact neg_eq_zero.mp hneg

private theorem unit_prime_two_cost_le {F : ℝ → ℝ} (hFc : Continuous F)
    (hcs : HasCompactSupport F) (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ho : ∀ x, F (-x) = -F x) :
    2 * primeJumpWeight 2 * autocorr F (Real.log 2) ≤
      (4902 / 10000 : ℝ) * (∫ x, F x ^ 2) := by
  have hzero : ∀ x, (1 / 2 : ℝ) < |x| → F x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport fun h => not_le_of_gt hx (abs_le.mpr (hs h))
  have hhalf := abs_autoCorrelation_le_half_of_le hFc hcs ho hzero
    (t := Real.log 2) (by linarith only [Real.log_two_gt_d9])
  change |autocorr F (Real.log 2)| ≤ (1 / 2) * (∫ x, F x ^ 2) at hhalf
  have hw : 0 ≤ primeJumpWeight 2 ∧ primeJumpWeight 2 ≤ (4902 / 10000 : ℝ) := by
    simpa only [vonMangoldtAtom, primeJumpWeight, if_pos le_rfl] using vonMangoldtAtom_two_bounds
  have hE : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hc := (le_abs_self (autocorr F (Real.log 2))).trans hhalf
  have hcost := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hw.1)
  have hcost' := mul_le_mul_of_nonneg_right hw.2 hE
  nlinarith only [hcost, hcost']

private theorem complete_two_moment_margin :
    (1 / 100 : ℝ) ≤ 137 / 60 - Real.eulerMascheroniConstant - Real.log Real.pi -
      5 / 96 - 4902 / 10000 - 1 / 483840 := by
  have hu : Real.log Real.pi ≤ Real.log 3 + Real.pi / 3 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.pi / 3 by positivity)
    rw [Real.log_div Real.pi_ne_zero (by norm_num)] at h
    linarith only [h]
  have hg := _root_.RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith only [hu, hg, Real.log_three_lt_d9, Real.pi_lt_d4]

private theorem stageForm_two_arch_lower {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hcs : HasCompactSupport F) :
    EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F -
      2 * primeJumpWeight 2 * autocorr F (Real.log 2) - sinhPairing F ^ 2 / 2 ≤
        stageForm 2 F := by
  have hJ := levyJump_eq_biScale hF hcs
  have hstage : stageForm 1 F = EF.gammaBracket 0 * (∫ x, F x ^ 2) +
      biScaleLevyEnergy F + coshPairing F ^ 2 / 2 - sinhPairing F ^ 2 / 2 := by
    norm_num [stageForm, markovForm, creationPotential, primeJump]
    rw [hJ]
    ring
  have hstep : stageForm 2 F = stageForm 1 F -
      2 * primeJumpWeight 2 * autocorr F (Real.log 2) := by
    have h := markovForm_succ hF.continuous hcs (N := 1) le_rfl
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at h
    unfold stageForm autocorr
    linarith only [h]
  rw [hstep, hstage]
  nlinarith only [sq_nonneg (coshPairing F)]

private theorem weilQuad_eq_stageForm_two_unit {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    weilQuad F = stageForm 2 F := by
  have hcs := unit_window_compact hs
  have hN : ∀ n : ℕ, 2 < n → ∀ u, F u * F (u + Real.log n) = 0 := by
    intro n hn u
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
    have hlog : 1 < Real.log n :=
      lt_of_lt_of_le (by linarith only [Real.log_three_gt_d9])
        (Real.log_le_log (by norm_num) hn3)
    by_cases hu : F u = 0
    · rw [hu, zero_mul]
    · have huI : u ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
        by_contra hnot
        exact hu (image_eq_zero_of_notMem_tsupport fun h => hnot (hs h))
      have hz : F (u + Real.log n) = 0 := image_eq_zero_of_notMem_tsupport fun h => by
        have hbound := (hs h).2
        linarith only [huI.1, hlog, hbound]
      rw [hz, mul_zero]
  have h := weil_eq_markovForm_add_pole hF hcs hN
  change weilQuad F = markovForm 2 F + coshPairing F ^ 2 / 2 - sinhPairing F ^ 2 / 2 at h
  unfold stageForm
  linarith only [h]

private theorem unit_two_moment_arch_lower {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x)
    (h1 : (∫ x, F x * x) = 0) (h3 : (∫ x, F x * x ^ 3) = 0) :
    (137 / 60 - Real.eulerMascheroniConstant - Real.log Real.pi - 5 / 96) *
      (∫ x, F x ^ 2) ≤ EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F := by
  have hcs := unit_window_compact hs
  obtain ⟨K, hK⟩ := _root_.RHTower.CHMDDoobGraph.compact_source_lipschitz hF hcs
  have hFL : ∀ x y, |F x - F y| ≤ (K : ℝ) * |x - y| := by
    intro x y
    simpa only [Real.dist_eq] using hK.dist_le_mul x y
  have hlag := odd_two_moment_logarithmic_gap_half (hF.of_le (by norm_num)) hFL
    (unit_window_vanish hF.continuous hs ho) ho h1 h3
  have hgamma := unit_odd_gamma_jump_lower hF hcs hs ho
  nlinarith only [hlag, hgamma]

/-- The first prime stage is coercive after its first and third odd moments vanish. -/
theorem stageForm_two_ge_of_odd_two_moments_zero {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x)
    (h1 : (∫ x, F x * x) = 0) (h3 : (∫ x, F x * x ^ 3) = 0) :
    (1 / 100 : ℝ) * (∫ x, F x ^ 2) ≤ stageForm 2 F := by
  have hcs := unit_window_compact hs
  have harch := unit_two_moment_arch_lower hF hs ho h1 h3
  have hprime := unit_prime_two_cost_le hF.continuous hcs hs ho
  have hpole := linear_moment_zero_pole_cost hF.continuous hcs hs h1
  have hstage := stageForm_two_arch_lower hF hcs
  have hE : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hmargin := mul_le_mul_of_nonneg_right complete_two_moment_margin hE
  nlinarith only [harch, hprime, hpole, hstage, hmargin]

/-- Complete Weil positivity on the unit odd window away from two polynomial moments. -/
theorem weilQuad_ge_of_odd_two_moments_zero {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x)
    (h1 : (∫ x, F x * x) = 0) (h3 : (∫ x, F x * x ^ 3) = 0) :
    (1 / 100 : ℝ) * (∫ x, F x ^ 2) ≤ weilQuad F := by
  rw [weilQuad_eq_stageForm_two_unit hF hs]
  exact stageForm_two_ge_of_odd_two_moments_zero hF hs ho h1 h3

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.stageForm_two_ge_of_odd_two_moments_zero
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.weilQuad_ge_of_odd_two_moments_zero
