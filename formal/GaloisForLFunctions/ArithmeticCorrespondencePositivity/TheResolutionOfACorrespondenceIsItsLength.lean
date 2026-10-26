import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheLocalGeometryOfAReflectionPair
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The resolution of a correspondence is its length

On the critical line every multiplicative correspondence is a rotation: the Hecke operator at `p`
acts at a critical zero `½ + iγ` by `p^{iγ}`, the archimedean flow by `t` by `e^{iγt}`. To isolate
one zero, a correspondence must separate its symbol from the symbols of its neighbours. This file
measures how well it can.

* **Symbols are Lipschitz in the height with constant the length** (`norm_heckeSymbol_sub_le`). For
  critical points, `|p^{iγ} − p^{iγ'}| ≤ log p · |γ − γ'|`: the Hecke operator at `p`, a
  correspondence of length `log p`, has resolution `1/log p` in height.
* **Separation costs derivative** (`one_le_deriv_bound_mul_length`). If a polynomial in the symbol
  takes values differing by `1` at two critical points at distance `δ`, its derivative exceeds
  `1/(δ log p)` somewhere on the chord. At the zero spacing `δ ≍ 2π/log T`, isolation through a
  correspondence of length `L` costs `≍ log T/L`: it is cheap only when `L ≳ log T`.
* **Modulation translates the spectrum** (`mellinAt_mul_cos`). Multiplying a test by `cos(γu)`
  replaces its transform by `(ĝ(s + iγ) + ĝ(s − iγ))/2`: height localization moves fibres along the
  line instead of acting on them, and its resolution is the inverse aperture.

So an average over heights or along an orbit becomes a point only through a correspondence whose
length reaches the inverse zero spacing — the persistence threshold `1/A` of ACG in the language of
correspondences. Below it, every rotation is too close to the identity to separate neighbours.
-/

open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The Hecke symbol at a critical point is the rotation `p^{iγ}`. -/
theorem heckeSymbol_critical (p γ : ℝ) :
    heckeSymbol p (1 / 2 + γ * I) = Complex.exp (I * ((γ * Real.log p : ℝ) : ℂ)) := by
  rw [heckeSymbol]; congr 1; push_cast; ring

/-- **The resolution of the Hecke operator at `p` is `1/log p`**:
`|p^{iγ} − p^{iγ'}| ≤ log p · |γ − γ'|` for `p ≥ 1`. -/
theorem norm_heckeSymbol_sub_le {p : ℝ} (hp : 1 ≤ p) (γ γ' : ℝ) :
    ‖heckeSymbol p (1 / 2 + γ * I) - heckeSymbol p (1 / 2 + γ' * I)‖ ≤
      Real.log p * |γ - γ'| := by
  rw [heckeSymbol_critical, heckeSymbol_critical]
  have hl : 0 ≤ Real.log p := Real.log_nonneg hp
  have e : Complex.exp (I * ((γ * Real.log p : ℝ) : ℂ)) - Complex.exp (I * ((γ' * Real.log p : ℝ) : ℂ)) =
      Complex.exp (I * ((γ' * Real.log p : ℝ) : ℂ)) *
        (Complex.exp (I * (((γ - γ') * Real.log p : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [e, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hl, mul_comm]

/-- **Separation costs derivative.** If a polynomial `P` separates the symbols of two critical
points by `1`, then `|P′|` exceeds `1/(log p |γ − γ'|)` somewhere on the chord: any bound `C` on
`|P′|` along the chord satisfies `1 ≤ C log p |γ − γ'|`. -/
theorem one_le_deriv_bound_mul_length {p : ℝ} (hp : 1 ≤ p) (γ γ' : ℝ) (P : Polynomial ℂ)
    {C : ℝ} (hC : ∀ z ∈ segment ℝ (heckeSymbol p (1 / 2 + γ * I)) (heckeSymbol p (1 / 2 + γ' * I)),
      ‖P.derivative.eval z‖ ≤ C)
    (hsep : 1 ≤ ‖P.eval (heckeSymbol p (1 / 2 + γ * I)) - P.eval (heckeSymbol p (1 / 2 + γ' * I))‖) :
    1 ≤ C * (Real.log p * |γ - γ'|) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (left_mem_segment ℝ _ _))
  have hmv := (convex_segment (heckeSymbol p (1 / 2 + γ * I)) (heckeSymbol p (1 / 2 + γ' * I))).norm_image_sub_le_of_norm_deriv_le
    (f := fun z => P.eval z) (fun z _ => P.differentiableAt) (fun z hz => by
      rw [Polynomial.deriv]; exact hC z hz)
    (right_mem_segment ℝ _ _) (left_mem_segment ℝ _ _)
  calc 1 ≤ ‖P.eval (heckeSymbol p (1 / 2 + γ * I)) - P.eval (heckeSymbol p (1 / 2 + γ' * I))‖ := hsep
    _ ≤ C * ‖heckeSymbol p (1 / 2 + γ * I) - heckeSymbol p (1 / 2 + γ' * I)‖ := hmv
    _ ≤ C * (Real.log p * |γ - γ'|) :=
        mul_le_mul_of_nonneg_left (norm_heckeSymbol_sub_le hp γ γ') hC0

/-- **Modulation translates the spectrum**: `(g · cos(γ·))^(s) = (ĝ(s + iγ) + ĝ(s − iγ))/2`. -/
theorem mellinAt_mul_cos {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (γ : ℝ)
    (s : ℂ) :
    mellinAt (fun u => g u * Real.cos (γ * u)) s =
      (mellinAt g (s + γ * I) + mellinAt g (s - γ * I)) / 2 := by
  rw [mellinAt, mellinAt, mellinAt, ← integral_add (integrable_mellinAt hg hgc _)
    (integrable_mellinAt hg hgc _), ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  push_cast
  rw [Complex.cos, show s + γ * I - 1 / 2 = (s - 1 / 2) + γ * I by ring,
    show s - γ * I - 1 / 2 = (s - 1 / 2) - γ * I by ring, add_mul, sub_mul, Complex.exp_add,
    Complex.exp_sub]
  field_simp
  ring_nf

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
