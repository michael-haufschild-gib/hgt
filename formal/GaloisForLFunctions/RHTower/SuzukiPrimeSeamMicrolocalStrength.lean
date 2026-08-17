import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Microlocal prime seams have vanishing normalized strength

A packet supported on an interval of length `η` with buffers of length `d` on either side pays a
logarithmic price in the singular Cauchy energy.  The price is the symmetric bracket
`log(1 + d/s) + log(1 + d/(η - s))`, whose minimum over the interval is `2 log(1 + 2d/η)`; the
minimization is an exact algebraic identity,

`(s+d)(η-s+d)η² - (η+2d)² s(η-s) = d(η+d)(η-2s)²`,

so the bracket is bounded below by twice the logarithm of the aspect ratio.  The Hankel response of
the same packet, by contrast, stays bounded: one seam contributes its own weight and the regular
part contributes the measure of the support.  The normalized strength is therefore a bounded
numerator over a logarithmically divergent denominator, and it vanishes as the packet narrows.

The signs of the two reflected directions are exact: an isometric involution acts as `+1` on the
symmetrized vector and `-1` on the antisymmetrized one, so a negative multiple of it is
nonpositive on the first and nonnegative on the second.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-! ## The buffer bracket and its minimum -/

/-- The exact algebraic identity behind the minimization of the buffer bracket. -/
theorem buffer_bracket_identity (d η s : ℝ) :
    (s + d) * (η - s + d) * η ^ 2 - (η + 2 * d) ^ 2 * (s * (η - s))
      = d * (η + d) * (η - 2 * s) ^ 2 := by
  ring

/-- **The buffer product is at least the squared aspect ratio.** -/
theorem buffer_product_ge {d η s : ℝ} (hd : 0 < d) (hη : 0 < η) (hs0 : 0 < s) (hsη : s < η) :
    (1 + 2 * d / η) ^ 2 ≤ (1 + d / s) * (1 + d / (η - s)) := by
  have hs' : (0 : ℝ) < η - s := by linarith
  have hu : (0 : ℝ) < s * (η - s) := by positivity
  have h1 : 1 + d / s = (s + d) / s := by field_simp
  have h2 : 1 + d / (η - s) = (η - s + d) / (η - s) := by field_simp
  have h3 : 1 + 2 * d / η = (η + 2 * d) / η := by field_simp
  rw [h1, h2, h3, div_pow, div_mul_div_comm,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [buffer_bracket_identity d η s,
    mul_nonneg (mul_nonneg hd.le (by linarith : (0:ℝ) ≤ η + d)) (sq_nonneg (η - 2 * s))]

/-- **`(262)`, pointwise core: the buffer bracket is at least twice the log aspect ratio.** -/
theorem log_buffer_bracket_ge {d η s : ℝ} (hd : 0 < d) (hη : 0 < η) (hs0 : 0 < s) (hsη : s < η) :
    2 * Real.log (1 + 2 * d / η) ≤ Real.log (1 + d / s) + Real.log (1 + d / (η - s)) := by
  have hs' : (0 : ℝ) < η - s := by linarith
  have hA : (0 : ℝ) < 1 + d / s := by positivity
  have hB : (0 : ℝ) < 1 + d / (η - s) := by positivity
  have hC : (0 : ℝ) < 1 + 2 * d / η := by positivity
  have hsq : Real.log ((1 + 2 * d / η) ^ 2) ≤ Real.log ((1 + d / s) * (1 + d / (η - s))) :=
    Real.log_le_log (by positivity) (buffer_product_ge hd hη hs0 hsη)
  rw [Real.log_pow, Real.log_mul hA.ne' hB.ne'] at hsq
  simpa using hsq

/-! ## `(264)`: the normalized strength vanishes -/

/-- The buffer denominator diverges as the packet narrows. -/
theorem tendsto_buffer_log_atTop {d B : ℝ} (hd : 0 < d) :
    Tendsto (fun η : ℝ => Real.log (1 + 2 * d / η) - B) (𝓝[>] 0) atTop := by
  have hinv : Tendsto (fun η : ℝ => η⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have hmul : Tendsto (fun η : ℝ => 2 * d * η⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    Tendsto.const_mul_atTop (by linarith) hinv
  have hadd : Tendsto (fun η : ℝ => 1 + 2 * d * η⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_atTop_add_const_left _ 1 hmul
  have hlog : Tendsto (fun η : ℝ => Real.log (1 + 2 * d * η⁻¹)) (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp hadd
  have hsub : Tendsto (fun η : ℝ => Real.log (1 + 2 * d * η⁻¹) - B) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_atTop_add_const_right _ (-B) hlog
  refine hsub.congr fun η => ?_
  rw [div_eq_mul_inv]

/-- **`(264)`: a bounded Hankel response over a logarithmically divergent common energy has
vanishing normalized strength.** -/
theorem tendsto_seamStrength_zero {w c d B : ℝ} (hd : 0 < d) :
    Tendsto (fun η : ℝ => (w + c * η) / (Real.log (1 + 2 * d / η) - B)) (𝓝[>] 0) (𝓝 0) := by
  have hnum : Tendsto (fun η : ℝ => w + c * η) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    have : Tendsto (fun η : ℝ => w + c * η) (𝓝 (0 : ℝ)) (𝓝 (w + c * 0)) :=
      (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  exact hnum.div_atTop (tendsto_buffer_log_atTop hd)

/-! ## `(267)`: the exact signs of the two reflected directions -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- An isometric involution fixes the symmetrized vector. -/
theorem reflection_symmetrize {R : H →ₗ[ℝ] H} (hinv : ∀ x, R (R x) = x) (u : H) :
    R (u + R u) = u + R u := by
  rw [map_add, hinv]
  exact add_comm _ _

/-- An isometric involution negates the antisymmetrized vector. -/
theorem reflection_antisymmetrize {R : H →ₗ[ℝ] H} (hinv : ∀ x, R (R x) = x) (u : H) :
    R (u - R u) = -(u - R u) := by
  rw [map_sub, hinv]
  abel

/-- **`(267)`, even half: a negative multiple of the reflection is nonpositive on the
symmetrized direction.** -/
theorem neg_reflection_quadForm_symmetrize_nonpos {R : H →ₗ[ℝ] H} (hinv : ∀ x, R (R x) = x)
    {w : ℝ} (hw : 0 ≤ w) (u : H) :
    -w * (inner ℝ (R (u + R u)) (u + R u) : ℝ) ≤ 0 := by
  rw [reflection_symmetrize hinv, real_inner_self_eq_norm_sq]
  have : (0 : ℝ) ≤ w * ‖u + R u‖ ^ 2 := by positivity
  linarith

/-- **`(267)`, odd half: the same multiple is nonnegative on the antisymmetrized direction.** -/
theorem neg_reflection_quadForm_antisymmetrize_nonneg {R : H →ₗ[ℝ] H} (hinv : ∀ x, R (R x) = x)
    {w : ℝ} (hw : 0 ≤ w) (u : H) :
    0 ≤ -w * (inner ℝ (R (u - R u)) (u - R u) : ℝ) := by
  rw [reflection_antisymmetrize hinv, inner_neg_left, real_inner_self_eq_norm_sq]
  have : (0 : ℝ) ≤ w * ‖u - R u‖ ^ 2 := by positivity
  linarith

end RHTower
