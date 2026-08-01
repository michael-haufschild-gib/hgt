import GaloisForLFunctions.HTGeometry.GammaFieldProjectiveResidue

/-!
# The ratio of two normalized elements

Two functions presented by their normalization — a shape and the limit after dividing by it —
have a convergent ratio as soon as the shapes have one: the ratio is the quotient of the limits
times the limit of the shape ratio.  It vanishes exactly when the shape ratio does, that is when the
numerator is strictly dominated.

With the projective boundary of the Gamma field this is eq. (5): a finite tuple normalized by a
dominant member has a constant projective limit, nonzero exactly on the members sharing the dominant
datum.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- **The normalized ratio law.**  If two functions converge after division by their shapes and the
shape ratio converges, the ratio of the functions converges to the corresponding product. -/
theorem tendsto_ratio_of_normalized {F G shapeF shapeG : ℝ → ℂ} {cF cG r : ℂ} (hcG : cG ≠ 0)
    (hsF : ∀ᶠ t : ℝ in atTop, shapeF t ≠ 0) (hsG : ∀ᶠ t : ℝ in atTop, shapeG t ≠ 0)
    (hF : Tendsto (fun t : ℝ => F t / shapeF t) atTop (nhds cF))
    (hG : Tendsto (fun t : ℝ => G t / shapeG t) atTop (nhds cG))
    (hratio : Tendsto (fun t : ℝ => shapeF t / shapeG t) atTop (nhds r)) :
    Tendsto (fun t : ℝ => F t / G t) atTop (nhds (cF * r / cG)) := by
  have hinv : Tendsto (fun t : ℝ => (G t / shapeG t)⁻¹) atTop (nhds cG⁻¹) := hG.inv₀ hcG
  have hprod := (hF.mul hratio).mul hinv
  have hval : cF * r * cG⁻¹ = cF * r / cG := (div_eq_mul_inv _ _).symm
  rw [hval] at hprod
  refine hprod.congr' ?_
  filter_upwards [hsF, hsG, hG.eventually_ne hcG] with t h1 h2 h3
  have hGne : G t ≠ 0 := by
    intro h
    rw [h, zero_div] at h3
    exact h3 rfl
  field_simp

/-- A strictly larger Gamma power is negligible. -/
theorem tendsto_gammaLine_pow_ratio (hσ : 0 < σ) {u v : ℕ} (h : v < u) :
    Tendsto (fun t : ℝ => gammaLine σ t ^ u / gammaLine σ t ^ v) atTop (nhds 0) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, u = v + (k + 1) := ⟨u - v - 1, by omega⟩
  have hone : HasPolyGrowthLine (fun _ : ℝ => (1 : ℂ)) := ⟨0, 1, zero_le_one, by simp⟩
  have hlim := tendsto_gammaLine_pow_mul hσ hone k
  refine hlim.congr' (Filter.Eventually.of_forall fun t => ?_)
  have hne : gammaLine σ t ^ v ≠ 0 := pow_ne_zero v (gammaLine_ne_zero hσ t)
  rw [hk, pow_add]
  field_simp
  rw [pow_add, pow_succ]
  ring

end GaloisForLFunctions
