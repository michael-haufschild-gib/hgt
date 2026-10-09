import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Hardy inequality of a cusp

On a cusp `{y > Y}` of a hyperbolic surface, a function of `y` alone (the constant term of a Fourier
expansion) has hyperbolic mass `∫ |f|² dy / y²` and Dirichlet energy `∫ |f'|² dy`.  The Hardy inequality

`∫_Y^T |f|² / y² + 2|f(T)|²/T ≤ 2|f(Y)|²/Y + 4 ∫_Y^T |f'|²`

says the energy is at least a quarter of the mass up to boundary terms: the constant terms of the
cusps never carry Rayleigh quotient below `1/4`.  Proof: integrate `|f|²` against `d(-1/y)` by parts
and absorb `2|f||f'|/y ≤ |f|²/(2y²) + 2|f'|²`.

* `HTGeometry.cusp_hardy`.
-/

namespace GaloisForLFunctions.HTGeometry

open intervalIntegral

/-- **The cusp Hardy inequality.** -/
theorem cusp_hardy {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {f f' : ℝ → F}
    {Y T : ℝ} (hY : 0 < Y) (hYT : Y ≤ T) (hf : ∀ y ∈ Set.Icc Y T, HasDerivAt f (f' y) y)
    (hf' : ContinuousOn f' (Set.Icc Y T)) :
    (∫ y in Y..T, ‖f y‖ ^ 2 / y ^ 2) + 2 * ‖f T‖ ^ 2 / T
      ≤ 2 * ‖f Y‖ ^ 2 / Y + 4 * ∫ y in Y..T, ‖f' y‖ ^ 2 := by
  have hpos : ∀ y ∈ Set.uIcc Y T, 0 < y := fun y hy => by
    rw [Set.uIcc_of_le hYT] at hy; exact hY.trans_le hy.1
  have hIcc : Set.uIcc Y T = Set.Icc Y T := Set.uIcc_of_le hYT
  have hfc : ContinuousOn f (Set.Icc Y T) := fun y hy => (hf y hy).continuousAt.continuousWithinAt
  -- integration by parts: `∫ |f|²/y² = |f(Y)|²/Y - |f(T)|²/T + ∫ 2⟨f, f'⟩/y`
  have hu : ∀ y ∈ Set.uIcc Y T, HasDerivAt (fun y => ‖f y‖ ^ 2) (2 * inner ℝ (f y) (f' y)) y :=
    fun y hy => (hf y (hIcc ▸ hy)).norm_sq
  have hv : ∀ y ∈ Set.uIcc Y T, HasDerivAt (fun y : ℝ => -y⁻¹) (1 / y ^ 2) y := fun y hy => by
    have := (hasDerivAt_inv (hpos y hy).ne').neg
    rw [neg_neg, ← one_div] at this
    exact this
  have hu' : IntervalIntegrable (fun y => 2 * inner ℝ (f y) (f' y)) MeasureTheory.volume Y T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    exact continuousOn_const.mul (hfc.inner hf')
  have hv' : IntervalIntegrable (fun y : ℝ => 1 / y ^ 2) MeasureTheory.volume Y T := by
    refine ContinuousOn.intervalIntegrable fun y hy => ?_
    exact (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 (hpos y hy).ne')).continuousWithinAt
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have e1 : (∫ y in Y..T, ‖f y‖ ^ 2 / y ^ 2) = ∫ y in Y..T, ‖f y‖ ^ 2 * (1 / y ^ 2) := by
    congr 1; funext y; ring
  rw [← e1] at hibp
  -- the absorption `2⟨f, f'⟩ (-1/y) ≤ |f|²/(2y²) + 2|f'|²`
  have hpt : ∀ y ∈ Set.Icc Y T,
      -(2 * inner ℝ (f y) (f' y) * -y⁻¹) ≤ ‖f y‖ ^ 2 / y ^ 2 / 2 + 2 * ‖f' y‖ ^ 2 := by
    intro y hy
    have hy0 : 0 < y := hY.trans_le hy.1
    have h1 : |inner ℝ (f y) (f' y)| ≤ ‖f y‖ * ‖f' y‖ := abs_real_inner_le_norm _ _
    have h2 : 2 * (‖f y‖ / y) * ‖f' y‖ ≤ (‖f y‖ / y) ^ 2 / 2 + 2 * ‖f' y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖f y‖ / y / 2 - ‖f' y‖ * 1), sq_nonneg (‖f y‖ / y - 2 * ‖f' y‖)]
    have h3 : -(2 * inner ℝ (f y) (f' y) * -y⁻¹) = 2 * inner ℝ (f y) (f' y) / y := by
      field_simp
    rw [h3]
    calc 2 * inner ℝ (f y) (f' y) / y ≤ 2 * (‖f y‖ * ‖f' y‖) / y := by
          gcongr; exact le_of_abs_le h1
      _ = 2 * (‖f y‖ / y) * ‖f' y‖ := by field_simp
      _ ≤ (‖f y‖ / y) ^ 2 / 2 + 2 * ‖f' y‖ ^ 2 := h2
      _ = _ := by rw [div_pow]
  have hint1 : IntervalIntegrable (fun y => ‖f y‖ ^ 2 / y ^ 2) MeasureTheory.volume Y T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    exact (hfc.norm.pow 2).div (continuousOn_id.pow 2) fun y hy =>
      pow_ne_zero 2 (hY.trans_le hy.1).ne'
  have hint2 : IntervalIntegrable (fun y => ‖f' y‖ ^ 2) MeasureTheory.volume Y T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    exact hf'.norm.pow 2
  have hint3 : IntervalIntegrable (fun y => 2 * inner ℝ (f y) (f' y) * -y⁻¹) MeasureTheory.volume Y T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    exact (continuousOn_const.mul (hfc.inner hf')).mul (continuousOn_inv₀.neg.mono fun y hy =>
      (hY.trans_le hy.1).ne')
  have hmono := integral_mono_on hYT hint3.neg ((hint1.div_const 2).add (hint2.const_mul 2)) hpt
  simp only [Pi.neg_apply] at hmono
  rw [intervalIntegral.integral_neg, integral_add (hint1.div_const 2) (hint2.const_mul 2),
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul] at hmono
  have hT0 : 0 < T := hY.trans_le hYT
  have eT : ‖f T‖ ^ 2 * -T⁻¹ = -(‖f T‖ ^ 2 / T) := by field_simp
  have eY : ‖f Y‖ ^ 2 * -Y⁻¹ = -(‖f Y‖ ^ 2 / Y) := by field_simp
  rw [eT, eY] at hibp
  have key : (∫ y in Y..T, ‖f y‖ ^ 2 / y ^ 2) ≤ -(‖f T‖ ^ 2 / T) + ‖f Y‖ ^ 2 / Y
      + ((∫ y in Y..T, ‖f y‖ ^ 2 / y ^ 2) / 2 + 2 * ∫ y in Y..T, ‖f' y‖ ^ 2) := by
    rw [hibp]; linarith
  have h2 : 2 * ‖f T‖ ^ 2 / T = 2 * (‖f T‖ ^ 2 / T) := by ring
  have h3 : 2 * ‖f Y‖ ^ 2 / Y = 2 * (‖f Y‖ ^ 2 / Y) := by ring
  rw [h2, h3]
  linarith

end GaloisForLFunctions.HTGeometry
