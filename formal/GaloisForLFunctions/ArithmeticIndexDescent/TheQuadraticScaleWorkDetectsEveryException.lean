import GaloisForLFunctions.ArithmeticIndexDescent.EveryOffLineQuartetCostsAStrictScaleQuantum

/-!
# Quadratic scale work detects every off-line exception

The rational damping difference has exact critical decay R⁻². Every actual
conjugate/reflection quartet therefore forces a positive asymptotic quantum
in R² times the completed source-work increment. The zero-free height gap
makes that quantum strictly greater than forty-eight. Infinite off-line
support forces the rescaled work to infinity, even if escape is sparse.
No arithmetic upper estimate is assumed or supplied.
-/

noncomputable section

open Filter Set RHTower
open GaloisForLFunctions.ArithmeticElectrostatics
open GaloisForLFunctions.ArithmeticCorrespondencePositivity
open scoped Topology

namespace GaloisForLFunctions.ArithmeticIndexDescent

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
  convert hnum.div hden (by norm_num : (16 : ℝ) ≠ 0) using 1 <;> first | rfl | ring

/-- The scale-square normalization retains a fixed positive height quantum. -/
theorem heightDamping_quadraticGap_tendsto (t : ℝ) :
    Tendsto (fun R : ℝ => R ^ 2 * (heightDamping (2 * R) t - heightDamping R t))
      atTop (𝓝 ((3 / 2 : ℝ) * t ^ 2)) := by
  apply (normalized_damping_gap_limit t).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (normalized_damping_gap t R hR).symm

/-- Completed arithmetic work at the critical quadratic decay scale. -/
def quadraticWorkIncrement (R : ℝ) : ℝ := R ^ 2 * doubledSourceWorkIncrement R

theorem quadraticWorkIncrement_nonneg {R : ℝ} (hR : 4 ≤ R) :
    0 ≤ quadraticWorkIncrement R :=
  mul_nonneg (sq_nonneg R) (doubledSourceWorkIncrement_nonneg hR)

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
      (1 + reflectionDiagonalAngle j) using 1 <;> first | rfl | ring
  filter_upwards [eventually_ge_atTop (4 : ℝ), hlim.eventually (lt_mem_nhds hb)] with R hR h
  exact h.trans_le (quartet_le_quadraticWorkIncrement hj hR)

private theorem quartetCharge_gt_fortyEight {j : XiDivisorSupport}
    (hj : (j : ℂ).re ≠ 1 / 2) :
    (48 : ℝ) < 3 * (j : ℂ).im ^ 2 * (1 + reflectionDiagonalAngle j) := by
  have hheight : 4 ≤ |(j : ℂ).im| := four_le_abs_xiZeroHeight (firstZeroCopy j)
  have hsq : (16 : ℝ) ≤ (j : ℂ).im ^ 2 := by
    nlinarith only [hheight, sq_abs (j : ℂ).im, sq_nonneg (|(j : ℂ).im| - 4)]
  have hprod := mul_pos (show 0 < (j : ℂ).im ^ 2 by linarith only [hsq])
    (reflectionDiagonalAngle_pos hj)
  nlinarith only [hsq, hprod]

/-- Every exception, including a lone finite quartet, crosses the closed asymptotic quantum. -/
theorem riemannHypothesis_or_eventually_quadraticIncrement_gt_fortyEight :
    RiemannHypothesis ∨ ∀ᶠ R : ℝ in atTop, 48 < quadraticWorkIncrement R := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  right
  obtain ⟨j, hj⟩ : ∃ j : XiDivisorSupport, (j : ℂ).re ≠ 1 / 2 := by
    by_contra! hall
    exact hRH (riemannHypothesis_of_forall_re_eq (c := 1 / 2) hall)
  exact eventually_lt_quadraticIncrement_of_lt_quartetCharge hj
    (quartetCharge_gt_fortyEight hj)

/-- Cofinal control at the critical-rate quantum excludes both finite and infinite exceptions. -/
theorem riemannHypothesis_iff_cofinally_quadraticIncrement_le_fortyEight :
    RiemannHypothesis ↔ ∀ T : ℝ, ∃ R : ℝ, T ≤ R ∧ 4 ≤ R ∧
      quadraticWorkIncrement R ≤ 48 := by
  constructor
  · intro hRH T
    refine ⟨max T 4, le_max_left _ _, le_max_right _ _, ?_⟩
    rw [quadraticWorkIncrement, doubledSourceWorkIncrement,
      xiDampedSourceWork_eq_zero_of_riemannHypothesis hRH,
      xiDampedSourceWork_eq_zero_of_riemannHypothesis hRH]
    norm_num
  · intro h
    rcases riemannHypothesis_or_eventually_quadraticIncrement_gt_fortyEight with hRH | hhigh
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
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.riemannHypothesis_iff_cofinally_quadraticIncrement_le_fortyEight
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.quadraticWorkIncrement_tendsto_atTop_of_infinite
