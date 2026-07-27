import GaloisForLFunctions.RHTower.DirichletLSubpolynomial
import GaloisForLFunctions.HTGeometry.SmoothWeightShift

/-!
# The reciprocal L-function as a contour-shift datum

`1/L(χ, ·)` is holomorphic on any strip `Θ + δ ≤ Re s ≤ d` and bounded there by
`κ⁻¹ (2+|Im s|)^ε`, for every `ε > 0`.

These are exactly the two hypotheses of `integral_mul_mellin_smoothWeight_shift`, with the growth
exponent `ε` free.  Holomorphy is zero-freeness right of the abscissa; the bound is the
subpolynomial lower bound for `L`, inverted.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- **The shift datum.**  `1/L(χ,·)` is holomorphic and `O((2+|t|)^ε)` on the strip. -/
theorem exists_shift_data {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (d : ℝ) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧
      DifferentiableOn ℂ (fun s : ℂ => (DirichletCharacter.LFunction χ s)⁻¹)
        (verticalStrip (zeroAbscissa χ + δ) d) ∧
      ∀ s ∈ verticalStrip (zeroAbscissa χ + δ) d,
        ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ Kb * (2 + |s.im|) ^ ε := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_lower_bound_subpolynomial hχ hprim hδ hδ1 hε
  have hne : ∀ s ∈ verticalStrip (zeroAbscissa χ + δ) d,
      DirichletCharacter.LFunction χ s ≠ 0 := by
    intro s hs
    refine LFunction_ne_zero_of_zeroAbscissa_lt hχ ?_
    have h1 : zeroAbscissa χ + δ ≤ s.re := hs.1
    linarith
  refine ⟨κ⁻¹, by positivity, ?_, ?_⟩
  · intro s hs
    exact (((DirichletCharacter.differentiable_LFunction hχ) s).inv
      (hne s hs)).differentiableWithinAt
  · intro s hs
    have hlow := hκ s hs.1
    have hbase : (0 : ℝ) < 2 + |s.im| := by linarith [abs_nonneg s.im]
    have hpow : (0 : ℝ) < (2 + |s.im|) ^ (-ε) := Real.rpow_pos_of_pos hbase _
    have hLpos : (0 : ℝ) < ‖DirichletCharacter.LFunction χ s‖ := by
      have : (0 : ℝ) < κ * (2 + |s.im|) ^ (-ε) := by positivity
      linarith
    rw [norm_inv]
    have hinv : (‖DirichletCharacter.LFunction χ s‖)⁻¹ ≤ (κ * (2 + |s.im|) ^ (-ε))⁻¹ :=
      (inv_le_inv₀ hLpos (by positivity)).mpr hlow
    refine le_trans hinv (le_of_eq ?_)
    rw [mul_inv, Real.rpow_neg hbase.le, inv_inv]

end RHTower
