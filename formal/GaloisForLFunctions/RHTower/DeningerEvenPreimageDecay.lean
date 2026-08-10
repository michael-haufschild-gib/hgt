import GaloisForLFunctions.RHTower.DeningerPreimageRayDecay
import GaloisForLFunctions.RHTower.DeningerPreimageL1

/-!
# The even extension decays faster than every power, and carries every moment in norm form

The even extension takes the absolute value of the argument, so the far-ray estimate of the
canonical preimage becomes a two-sided estimate on `|x| ≥ 1` with no extra work.  Recording the
moments as integrability of `‖v‖^n ‖E f_h(v)‖` is the shape the Fourier differentiation lemmas
consume.

* `deningerEvenPreimage_norm_moment` : **every moment, in norm form.**
* `deningerEvenPreimage_decay` : **`‖E f_h(x)‖ ≤ C_B |x|^{-B}` for `|x| ≥ 1`, every `B`.**
-/

namespace RHTower

open MeasureTheory SchwartzMap

noncomputable section

/-- **Every moment of the even extension, in norm form.** -/
theorem deningerEvenPreimage_norm_moment {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (n : ℕ) :
    Integrable fun v : ℝ => ‖v‖ ^ n * ‖deningerEvenPreimage h v‖ := by
  have hbase := (deningerEvenPreimage_moment_integrable hh n).norm
  refine hbase.congr (Filter.Eventually.of_forall fun v => ?_)
  show ‖((v ^ n : ℝ) : ℂ) * deningerEvenPreimage h v‖
      = ‖v‖ ^ n * ‖deningerEvenPreimage h v‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]

/-- **The even extension decays faster than every power away from the origin.** -/
theorem deningerEvenPreimage_decay {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ |x| → ‖deningerEvenPreimage h x‖ ≤ C / |x| ^ B := by
  obtain ⟨C, hCnn, hC⟩ := deningerMobiusPreimage_ray_decay hh (k := max B 2) (le_max_right _ _)
  refine ⟨C, hCnn, fun x hx => ?_⟩
  have hxpos : (0 : ℝ) < |x| := lt_of_lt_of_le zero_lt_one hx
  have hbase : ‖deningerEvenPreimage h x‖ ≤ C / |x| ^ (max B 2) := hC |x| hx
  refine le_trans hbase ?_
  have hmono : |x| ^ B ≤ |x| ^ (max B 2) := pow_le_pow_right₀ hx (le_max_left _ _)
  exact div_le_div_of_nonneg_left hCnn (by positivity) hmono

/-- The right-ray form of the decay. -/
theorem deningerEvenPreimage_decayRight {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖deningerEvenPreimage h x‖ ≤ C / x ^ B := by
  obtain ⟨C, hCnn, hC⟩ := deningerEvenPreimage_decay hh B
  refine ⟨C, hCnn, fun x hx => ?_⟩
  have hxnn : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  have habs : |x| = x := abs_of_nonneg hxnn
  have := hC x (by rw [habs]; exact hx)
  rwa [habs] at this

/-- The left-ray form of the decay. -/
theorem deningerEvenPreimage_decayLeft {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖deningerEvenPreimage h (-x)‖ ≤ C / x ^ B := by
  obtain ⟨C, hCnn, hC⟩ := deningerEvenPreimage_decayRight hh B
  refine ⟨C, hCnn, fun x hx => ?_⟩
  rw [deningerEvenPreimage_even]
  exact hC x hx

end

end RHTower
