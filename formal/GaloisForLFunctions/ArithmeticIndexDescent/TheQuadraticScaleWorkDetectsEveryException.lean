import GaloisForLFunctions.ArithmeticIndexDescent.EveryOffLineQuartetCostsAStrictScaleQuantum
import GaloisForLFunctions.RHTower.PrimeArchLogHeightDefectOrderTwentyThreeEndpointOptimization

/-!
# Quadratic scale work detects every off-line exception

The rational damping difference has exact critical decay R⁻². Every actual
conjugate/reflection quartet therefore forces a positive asymptotic quantum
in R² times the completed source-work increment. The certified arithmetic
off-line height floor supplies its closed exclusion threshold. Infinite off-line
support forces the rescaled work to infinity, even if escape is sparse.
No arithmetic upper estimate is assumed or supplied.
-/

noncomputable section

open Filter Set RHTower
open GaloisForLFunctions.ArithmeticElectrostatics
open GaloisForLFunctions.ArithmeticCorrespondencePositivity
open scoped Topology

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- Critical-rate cost per right copy from the certified arithmetic off-line height floor. -/
def quadraticIndexUnit : ℝ := (3 / 2 : ℝ) * xiOrderTwentyThreeOptimizedHeightSq

/-- A full conjugate pair costs twice the single-copy index unit. -/
def quadraticExclusionQuantum : ℝ := 2 * quadraticIndexUnit

theorem quadraticIndexUnit_pos : 0 < quadraticIndexUnit := by
  norm_num [quadraticIndexUnit, xiOrderTwentyThreeOptimizedHeightSq]

theorem quadraticExclusionQuantum_pos : 0 < quadraticExclusionQuantum :=
  mul_pos (by norm_num) quadraticIndexUnit_pos

private theorem normalized_damping_gap (t R : ℝ) (hR : 0 < R) :
    R ^ 2 * (heightDamping (2 * R) t - heightDamping R t) =
      t ^ 2 * (24 + 15 * (t / R) ^ 2) /
        ((4 + (t / R) ^ 2) ^ 2 * (1 + (t / R) ^ 2) ^ 2) := by
  have h0 := hR.ne'
  have hA : R ^ 2 + t ^ 2 ≠ 0 := by positivity
  have hB : (2 * R) ^ 2 + t ^ 2 ≠ 0 := by positivity
  have hC : 4 + (t / R) ^ 2 ≠ 0 := by positivity
  have hD : 1 + (t / R) ^ 2 ≠ 0 := by positivity
  unfold heightDamping
  field_simp [h0, hA, hB, hC, hD]
  ring

private theorem normalized_damping_gap_limit (t : ℝ) :
    Tendsto (fun R : ℝ => t ^ 2 * (24 + 15 * (t / R) ^ 2) /
      ((4 + (t / R) ^ 2) ^ 2 * (1 + (t / R) ^ 2) ^ 2)) atTop
        (𝓝 ((3 / 2 : ℝ) * t ^ 2)) := by
  have hq : Tendsto (fun R : ℝ => (t / R) ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_pow (by decide : 2 ≠ 0)] using
      (((tendsto_const_nhds : Tendsto (fun _ : ℝ => t) atTop (𝓝 t)).mul
        (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))).pow 2)
  have hnum : Tendsto (fun R : ℝ => t ^ 2 * (24 + 15 * (t / R) ^ 2)) atTop
      (𝓝 (t ^ 2 * 24)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul hq)))
  have hden : Tendsto (fun R : ℝ =>
      (4 + (t / R) ^ 2) ^ 2 * (1 + (t / R) ^ 2) ^ 2) atTop (𝓝 16) := by
    convert ((tendsto_const_nhds.add hq).pow 2).mul
      ((tendsto_const_nhds.add hq).pow 2) using 1 <;> norm_num
  convert hnum.div hden (by norm_num : (16 : ℝ) ≠ 0) using 1 <;> try rfl
  congr 1
  ring

/-- The scale-square normalization retains a fixed positive height quantum. -/
theorem heightDamping_quadraticGap_tendsto (t : ℝ) :
    Tendsto (fun R : ℝ => R ^ 2 * (heightDamping (2 * R) t - heightDamping R t))
      atTop (𝓝 ((3 / 2 : ℝ) * t ^ 2)) := by
  apply (normalized_damping_gap_limit t).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (normalized_damping_gap t R hR).symm

/-- Completed arithmetic work at the critical quadratic decay scale. -/
def quadraticWorkIncrement (R : ℝ) : ℝ := R ^ 2 * doubledSourceWorkIncrement R

theorem quadraticWorkIncrement_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis)
    (R : ℝ) : quadraticWorkIncrement R = 0 := by
  rw [quadraticWorkIncrement, doubledSourceWorkIncrement,
    xiDampedSourceWork_eq_zero_of_riemannHypothesis hRH,
    xiDampedSourceWork_eq_zero_of_riemannHypothesis hRH]
  ring

theorem quadraticWorkIncrement_nonneg {R : ℝ} (hR : 4 ≤ R) :
    0 ≤ quadraticWorkIncrement R :=
  mul_nonneg (sq_nonneg R) (doubledSourceWorkIncrement_nonneg hR)

/-- Removing the compact height taper retains the critically rescaled source increment. -/
theorem quadraticTaperedSourceWork_tendsto {R : ℝ} (hR : 4 ≤ R) :
    Tendsto (fun N : ℕ => R ^ 2 *
      (xiTaperedSourceWork (2 * R) N - xiTaperedSourceWork R N)) atTop
        (𝓝 (quadraticWorkIncrement R)) := by
  change Tendsto (fun N : ℕ => R ^ 2 *
    (xiTaperedSourceWork (2 * R) N - xiTaperedSourceWork R N)) atTop
      (𝓝 (R ^ 2 * (xiDampedSourceWork (2 * R) - xiDampedSourceWork R)))
  exact tendsto_const_nhds.mul (xiTaperedSourceWork_increment_tendsto hR
    (show 4 ≤ 2 * R by linarith only [hR]))

/-- The exact quartet payment survives multiplication by the scale square. -/
theorem quartet_le_quadraticWorkIncrement {j : XiDivisorSupport}
    (hj : (j : ℂ).re ≠ 1 / 2) {R : ℝ} (hR : 4 ≤ R) :
    2 * (R ^ 2 * (heightDamping (2 * R) (j : ℂ).im - heightDamping R (j : ℂ).im)) *
      (1 + reflectionDiagonalAngle j) ≤ quadraticWorkIncrement R := by
  have h := mul_le_mul_of_nonneg_left
    (offLineQuartet_increment_payment hj hR (show R ≤ 2 * R by linarith only [hR]))
    (sq_nonneg R)
  unfold quadraticWorkIncrement doubledSourceWorkIncrement
  nlinarith only [h]

/-- A single fixed off-line quartet supplies an eventual lower bound at every sufficiently large scale. -/
theorem eventually_lt_quadraticIncrement_of_lt_quartetCharge {j : XiDivisorSupport}
    (hj : (j : ℂ).re ≠ 1 / 2) {b : ℝ}
    (hb : b < 3 * (j : ℂ).im ^ 2 * (1 + reflectionDiagonalAngle j)) :
    ∀ᶠ R : ℝ in atTop, b < quadraticWorkIncrement R := by
  have hlim : Tendsto (fun R : ℝ =>
      2 * (R ^ 2 * (heightDamping (2 * R) (j : ℂ).im - heightDamping R (j : ℂ).im)) *
        (1 + reflectionDiagonalAngle j)) atTop
      (𝓝 (3 * (j : ℂ).im ^ 2 * (1 + reflectionDiagonalAngle j))) := by
    convert (tendsto_const_nhds.mul (heightDamping_quadraticGap_tendsto (j : ℂ).im)).mul_const
      (1 + reflectionDiagonalAngle j) using 1
    first | rfl | ring
  filter_upwards [eventually_ge_atTop (4 : ℝ), hlim.eventually (lt_mem_nhds hb)] with R hR h
  exact h.trans_le (quartet_le_quadraticWorkIncrement hj hR)

/-- The arithmetic height floor and positive diagonal angle give a strict quartet threshold. -/
theorem quartetCharge_gt_exclusionQuantum {j : XiDivisorSupport}
    (hj : (j : ℂ).re ≠ 1 / 2) :
    quadraticExclusionQuantum < 3 * (j : ℂ).im ^ 2 * (1 + reflectionDiagonalAngle j) := by
  have hsq := orderTwentyThreeOptimizedHeightSq_le_im_sq_of_xiZeroCopy_offLine
    (firstZeroCopy j) hj
  change xiOrderTwentyThreeOptimizedHeightSq ≤ (j : ℂ).im ^ 2 at hsq
  have hfloor : 0 < xiOrderTwentyThreeOptimizedHeightSq := by
    norm_num [xiOrderTwentyThreeOptimizedHeightSq]
  have hprod := mul_pos (hfloor.trans_le hsq)
    (reflectionDiagonalAngle_pos hj)
  unfold quadraticExclusionQuantum quadraticIndexUnit
  nlinarith only [hsq, hprod]

/-- Every exception, including a lone finite quartet, crosses the closed asymptotic quantum. -/
theorem riemannHypothesis_or_eventually_quadraticIncrement_gt_exclusionQuantum :
    RiemannHypothesis ∨ ∀ᶠ R : ℝ in atTop,
      quadraticExclusionQuantum < quadraticWorkIncrement R := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  right
  obtain ⟨j, hj⟩ : ∃ j : XiDivisorSupport, (j : ℂ).re ≠ 1 / 2 := by
    by_contra! hall
    exact hRH (riemannHypothesis_of_forall_re_eq (c := 1 / 2) hall)
  exact eventually_lt_quadraticIncrement_of_lt_quartetCharge hj
    (quartetCharge_gt_exclusionQuantum hj)

/-- Every exception is detected by finite Laurent-source readings, in damping-then-taper order. -/
theorem riemannHypothesis_or_eventually_finite_quadraticSourceWork_gt_exclusionQuantum :
    RiemannHypothesis ∨ ∀ᶠ R : ℝ in atTop, ∀ᶠ N : ℕ in atTop,
      quadraticExclusionQuantum <
        R ^ 2 * (xiTaperedSourceWork (2 * R) N - xiTaperedSourceWork R N) := by
  rcases riemannHypothesis_or_eventually_quadraticIncrement_gt_exclusionQuantum with hRH | h
  · exact Or.inl hRH
  right
  filter_upwards [h, eventually_ge_atTop (4 : ℝ)] with R hQ hR
  exact (quadraticTaperedSourceWork_tendsto hR).eventually (lt_mem_nhds hQ)

/-- Cofinal control at the critical-rate quantum excludes both finite and infinite exceptions. -/
theorem riemannHypothesis_iff_cofinally_quadraticIncrement_le_exclusionQuantum :
    RiemannHypothesis ↔ ∀ T : ℝ, ∃ R : ℝ, T ≤ R ∧ 4 ≤ R ∧
      quadraticWorkIncrement R ≤ quadraticExclusionQuantum := by
  constructor
  · intro hRH T
    refine ⟨max T 4, le_max_left _ _, le_max_right _ _, ?_⟩
    rw [quadraticWorkIncrement_eq_zero_of_riemannHypothesis hRH]
    exact quadraticExclusionQuantum_pos.le
  · intro h
    rcases riemannHypothesis_or_eventually_quadraticIncrement_gt_exclusionQuantum with hRH | hhigh
    · exact hRH
    obtain ⟨T, hT⟩ := eventually_atTop.mp hhigh
    obtain ⟨R, hR, _, hbound⟩ := h T
    exact False.elim ((not_lt_of_ge hbound) (hT R hR))

/-- Arbitrarily high fixed quartets force divergence at the critical quadratic scale. -/
theorem quadraticWorkIncrement_tendsto_atTop_of_infinite (hinf : offLineSupport.Infinite) :
    Tendsto quadraticWorkIncrement atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  let T := max 4 (|b| + 1)
  have hT : 0 ≤ T := le_trans (by norm_num) (le_max_left _ _)
  obtain ⟨j, hj, hhigh⟩ : ∃ j ∈ offLineSupport, T < |(j : ℂ).im| := by
    by_contra! h
    apply hinf
    apply (finite_xiDivisorSupport_band 0 hT).subset
    intro j hj
    simpa only [Set.mem_setOf_eq, sub_zero] using h j hj
  have hjoff : (j : ℂ).re ≠ 1 / 2 := hj
  have hgt : 4 < |(j : ℂ).im| := (le_max_left _ _).trans_lt hhigh
  have hhb : |b| + 1 < |(j : ℂ).im| := (le_max_right _ _).trans_lt hhigh
  have hsq : |(j : ℂ).im| ≤ (j : ℂ).im ^ 2 := by
    have hp := mul_nonneg (abs_nonneg (j : ℂ).im)
      (show 0 ≤ |(j : ℂ).im| - 1 by linarith only [hgt])
    nlinarith only [hp, sq_abs (j : ℂ).im]
  have hangle := mul_nonneg (sq_nonneg (j : ℂ).im) (reflectionDiagonalAngle_pos hjoff).le
  have hb : b < 3 * (j : ℂ).im ^ 2 * (1 + reflectionDiagonalAngle j) := by
    nlinarith only [hsq, hhb, le_abs_self b, hangle, abs_nonneg b]
  exact (eventually_lt_quadraticIncrement_of_lt_quartetCharge hjoff hb).mono fun _ h => h.le

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.heightDamping_quadraticGap_tendsto
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.riemannHypothesis_iff_cofinally_quadraticIncrement_le_exclusionQuantum
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.riemannHypothesis_or_eventually_finite_quadraticSourceWork_gt_exclusionQuantum
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.quadraticWorkIncrement_tendsto_atTop_of_infinite
