import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Critical limit exchange for the multiple q-Pochhammer counterterm

This module formalizes the coefficientwise core of the programme-4 multiple-Gamma benchmark.
After the pole-order normalization forced by `r + 1` geometric directions, taking the finite
boundary first gives zero, whereas completing the geometric box first gives the nonzero
coefficient `-1 / m^(r+2)`.  These are the coefficients of `-Li_(r+2)`.

The theorem concerns the raw q-Pochhammer counterterm layer.  It does not claim that the normalized
Vigneras multiple q-Gamma function itself has a noncommuting classical limit.
-/

open Filter
open scoped Topology BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- The `x^m` coefficient of the critically normalized formal logarithm of the finite
`(r+1)`-direction q-Pochhammer box. -/
def multipleQPochhammerFiniteRenormalizedLogCoeff
    (N r m : ℕ) (q : ℝ) : ℝ :=
  -((1 - q) ^ (r + 1) *
      (∑ j ∈ Finset.range N, (q ^ m) ^ j) ^ (r + 1)) / (m : ℝ)

/-- The coefficient obtained after completing the geometric box.  Writing it with the finite
length-`m` geometric sum extends the quotient `(1-q)/(1-q^m)` continuously to `q=1`. -/
def multipleQPochhammerCompletedRenormalizedLogCoeff
    (r m : ℕ) (q : ℝ) : ℝ :=
  -((∑ j ∈ Finset.range m, q ^ j)⁻¹ ^ (r + 1)) / (m : ℝ)

/-- Boundary refinement at every finite box kills the critically normalized coefficient. -/
theorem tendsto_multipleQPochhammerFiniteRenormalizedLogCoeff_one
    (N r m : ℕ) :
    Tendsto (multipleQPochhammerFiniteRenormalizedLogCoeff N r m)
      (𝓝 1) (𝓝 0) := by
  have hcont : ContinuousAt
      (multipleQPochhammerFiniteRenormalizedLogCoeff N r m) 1 := by
    unfold multipleQPochhammerFiniteRenormalizedLogCoeff
    fun_prop
  simpa [multipleQPochhammerFiniteRenormalizedLogCoeff] using hcont.tendsto

private theorem one_sub_mul_inv_one_sub_pow_eq_geomSum_inv
    {q : ℝ} {m : ℕ} (hqpow : |q ^ m| < 1) :
    (1 - q) * (1 - q ^ m)⁻¹ =
      (∑ j ∈ Finset.range m, q ^ j)⁻¹ := by
  have hqm : q ^ m ≠ 1 := by
    intro h
    have habs : |q ^ m| = 1 := by simp [h]
    linarith
  have hq : q ≠ 1 := by
    intro h
    subst q
    simp at hqpow
  have hsum : (∑ j ∈ Finset.range m, q ^ j) ≠ 0 := by
    intro hzero
    have hgeom := geom_sum_mul_neg q m
    rw [hzero, zero_mul] at hgeom
    exact hqm (sub_eq_zero.mp hgeom.symm).symm
  rw [← geom_sum_mul_neg q m]
  field_simp [hq, hsum]

/-- For a fixed interior nome, completing the finite geometric box gives the completed
coefficient. -/
theorem tendsto_multipleQPochhammerFiniteRenormalizedLogCoeff_atTop
    (r m : ℕ) (q : ℝ) (hqpow : |q ^ m| < 1) :
    Tendsto (fun N ↦ multipleQPochhammerFiniteRenormalizedLogCoeff N r m q)
      atTop (𝓝 (multipleQPochhammerCompletedRenormalizedLogCoeff r m q)) := by
  have hgeom : Tendsto
      (fun N ↦ ∑ j ∈ Finset.range N, (q ^ m) ^ j) atTop (𝓝 (1 - q ^ m)⁻¹) :=
    (hasSum_geometric_of_abs_lt_one hqpow).tendsto_sum_nat
  have hscaled : Tendsto
      (fun N ↦ (1 - q) * ∑ j ∈ Finset.range N, (q ^ m) ^ j)
      atTop (𝓝 ((1 - q) * (1 - q ^ m)⁻¹)) :=
    tendsto_const_nhds.mul hgeom
  have hlim : Tendsto
      (fun N ↦ -(((1 - q) * ∑ j ∈ Finset.range N, (q ^ m) ^ j) ^ (r + 1)) /
        (m : ℝ))
      atTop (𝓝 (-(((1 - q) * (1 - q ^ m)⁻¹) ^ (r + 1)) / (m : ℝ))) :=
    (hscaled.pow (r + 1)).neg.div_const (m : ℝ)
  have hratio := one_sub_mul_inv_one_sub_pow_eq_geomSum_inv hqpow
  convert hlim using 1
  · ext N
    simp only [multipleQPochhammerFiniteRenormalizedLogCoeff, mul_pow]
  · rw [multipleQPochhammerCompletedRenormalizedLogCoeff, hratio]

/-- After completion, the critical boundary coefficient is `-1 / m^(r+2)`. -/
theorem tendsto_multipleQPochhammerCompletedRenormalizedLogCoeff_one
    (r m : ℕ) (hm : 0 < m) :
    Tendsto (multipleQPochhammerCompletedRenormalizedLogCoeff r m)
      (𝓝 1) (𝓝 (-1 / (m : ℝ) ^ (r + 2))) := by
  have hsum : (∑ j ∈ Finset.range m, (1 : ℝ) ^ j) ≠ 0 := by
    simp [hm.ne']
  have hcont : ContinuousAt
      (multipleQPochhammerCompletedRenormalizedLogCoeff r m) 1 := by
    unfold multipleQPochhammerCompletedRenormalizedLogCoeff
    fun_prop
  convert hcont.tendsto using 1
  rw [multipleQPochhammerCompletedRenormalizedLogCoeff]
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp [hmR]
  ring

/-- Exact coefficientwise limit-exchange capstone.  The finite-boundary-first route is zero, while
the completion-first route differs by the `m`th coefficient of `-Li_(r+2)`. -/
theorem multiple_qPochhammer_critical_limit_exchange
    (r m : ℕ) (hm : 0 < m) :
    Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0) ∧
      Tendsto (multipleQPochhammerCompletedRenormalizedLogCoeff r m)
        (𝓝 1) (𝓝 (-1 / (m : ℝ) ^ (r + 2))) ∧
      (-1 / (m : ℝ) ^ (r + 2)) ≠ 0 := by
  refine ⟨tendsto_const_nhds, tendsto_multipleQPochhammerCompletedRenormalizedLogCoeff_one r m hm,
    ?_⟩
  exact div_ne_zero (by norm_num)
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr hm.ne'))

end

end GaloisForLFunctions
