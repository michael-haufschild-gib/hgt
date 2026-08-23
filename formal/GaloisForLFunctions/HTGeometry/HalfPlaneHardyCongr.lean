import GaloisForLFunctions.HTGeometry.HalfPlaneHardyMul

/-!
# Hardy membership only sees the right half-plane

`IsHalfPlaneHardy F M` constrains `F` only through its values on `{Re w > 0}`: holomorphy there and
the mass of `F` on the vertical lines `Re w = σ > 0`.  Two functions agreeing there are therefore
Hardy together.  This is what lets one replace the anonymous quotient produced by a division lemma
by a concrete analytic representative, which the next division step can then differentiate.

## Main results

* `IsHalfPlaneHardy.congr_right`
-/

open Complex Set Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- Two functions agreeing on the open right half-plane are Hardy together. -/
theorem IsHalfPlaneHardy.congr_right {F G : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M)
    (h : ∀ w : ℂ, 0 < w.re → F w = G w) : IsHalfPlaneHardy G M where
  holo := hF.holo.congr fun w hw => (h w hw).symm
  memLp := by
    intro σ hσ
    have hfun : (fun ξ : ℝ => G (rayLine σ ξ)) = fun ξ : ℝ => F (rayLine σ ξ) := by
      funext ξ
      exact (h _ (by simpa using hσ)).symm
    rw [hfun]
    exact hF.memLp σ hσ
  bound := by
    intro σ hσ
    have hfun : ∀ ξ : ℝ, G (rayLine σ ξ) = F (rayLine σ ξ) := by
      intro ξ
      exact (h _ (by simpa using hσ)).symm
    simp only [hfun]
    exact hF.bound σ hσ

end GaloisForLFunctions.HTGeometry
