import GaloisForLFunctions.RHTower.Sieve.RouteTZetaZeroFree
import GaloisForLFunctions.RHTower.Sieve.ZetaLittlewoodRegionAbs

/-!
# Absolute-height Route-T zero-free region
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- **Route-T zero-free region at both signs of the ordinate.** -/
theorem exists_routeT_zero_free_region_abs :
    ∃ A : ℝ, ∀ β γ : ℝ, 100000 ≤ |γ| →
      routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight |γ| → β ≤ 1 →
      1 - routeTZeroFreeWidth A |γ| < β →
      riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨A, hA⟩ := exists_routeT_zero_free_region
  refine ⟨A, ?_⟩
  intro β γ hγ hlarge hβ1 hβgt
  rcases le_or_gt 0 γ with hγ0 | hγ0
  · have habs : |γ| = γ := abs_of_nonneg hγ0
    rw [habs] at hγ hlarge hβgt
    exact hA β γ hγ hlarge hβ1 hβgt
  · have habs : |γ| = -γ := abs_of_neg hγ0
    rw [habs] at hγ hlarge hβgt
    simpa only [neg_neg] using
      riemannZeta_ne_zero_neg_im (hA β (-γ) hγ hlarge hβ1 hβgt)

end

end RHTower.Sieve
