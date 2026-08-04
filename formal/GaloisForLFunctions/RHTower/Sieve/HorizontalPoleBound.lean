import GaloisForLFunctions.RHTower.Sieve.VerticalPoleIntegral

/-!
# The horizontal edges of the pole term

At height `T` the pole term satisfies `‖(s-1)⁻¹‖ ≤ 1/|T|`, because the norm of a complex number is at
least the modulus of its imaginary part and shifting by the real number `x - 1` leaves that part
alone.  So each horizontal edge of the pole term is at most `(d-c)/|T|` and vanishes as the
truncation height grows.

This is the last of the four edges of the pole term, and unlike the vertical ones it needs no
computation — only the trivial bound.
-/

namespace RHTower.Sieve

open Filter Topology

/-- The pole term is small at height `T`. -/
theorem norm_inv_sub_one_le {x T : ℝ} (hT : T ≠ 0) :
    ‖((x : ℂ) + (T : ℝ) * Complex.I - 1)⁻¹‖ ≤ |T|⁻¹ := by
  have him : ((x : ℂ) + (T : ℝ) * Complex.I - 1).im = T := by simp
  have hge : |T| ≤ ‖(x : ℂ) + (T : ℝ) * Complex.I - 1‖ := by
    have h := Complex.abs_im_le_norm ((x : ℂ) + (T : ℝ) * Complex.I - 1)
    rwa [him] at h
  have hTpos : (0 : ℝ) < |T| := abs_pos.2 hT
  have hpos : (0 : ℝ) < ‖(x : ℂ) + (T : ℝ) * Complex.I - 1‖ := lt_of_lt_of_le hTpos hge
  rw [norm_inv]
  exact inv_anti₀ hTpos hge

/-- **A horizontal edge of the pole term.** -/
theorem norm_integral_horizontal_pole_le {c d T : ℝ} (hcd : c ≤ d) (hT : T ≠ 0) :
    ‖∫ x : ℝ in c..d, ((x : ℂ) + (T : ℝ) * Complex.I - 1)⁻¹‖ ≤ (d - c) / |T| := by
  have hbd : ∀ x ∈ Set.uIoc c d, ‖((x : ℂ) + (T : ℝ) * Complex.I - 1)⁻¹‖ ≤ |T|⁻¹ :=
    fun x _ => norm_inv_sub_one_le hT
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ d - c), inv_mul_eq_div] at h

/-- **The horizontal edges of the pole term vanish.** -/
theorem tendsto_integral_horizontal_pole {c d : ℝ} (hcd : c ≤ d) :
    Tendsto (fun T : ℝ => ‖∫ x : ℝ in c..d, ((x : ℂ) + (T : ℝ) * Complex.I - 1)⁻¹‖)
      atTop (𝓝 0) := by
  have hmaj : Tendsto (fun T : ℝ => (d - c) / |T|) atTop (𝓝 0) := by
    have habs : Tendsto (fun T : ℝ => |T|) atTop atTop :=
      tendsto_abs_atTop_atTop
    have h := habs.inv_tendsto_atTop.const_mul (d - c)
    simp only [mul_zero] at h
    refine h.congr fun T => ?_
    simp only [Pi.inv_apply]
    rw [div_eq_mul_inv]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hmaj
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact norm_integral_horizontal_pole_le hcd (ne_of_gt hT)

end RHTower.Sieve
