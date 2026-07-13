import GaloisForLFunctions.HTGeometry.JacobiThetaFamilyOrbitObstruction
import GaloisForLFunctions.HTGeometry.MeromorphicPoleOrbitBoundaryLocal

/-!
# Punctured-local finite-family theta obstruction

The finite separated-family theta pole-orbit obstruction is insensitive to assigned values at
poles: punctured-local equality on the distinguished orbit is already impossible for an elliptic
translation primitive.
-/

open Filter Topology Set Function

namespace GaloisForLFunctions

noncomputable section

/-- A separated finite theta-defect family with a nonzero operator cannot be punctured-locally
equal on its distinguished orbit to the translation coboundary of an elliptic meromorphic
function. -/
theorem thetaDifferentialFamily_ne_ellipticShiftCoboundary_of_eventuallyEq
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {L : ι → Polynomial ℂ} {h : ι → ℂ} {τ q : ℂ} (hτ : 0 < τ.im)
    (hq : ThetaTranslationNontorsion τ q)
    (hnonres : ∀ j ∈ s, ThetaTranslationNonresonant τ q (h j))
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hLi₀ : L i₀ ≠ 0)
    (hsep : ∀ j ∈ s, j ≠ i₀ → ThetaTranslationNonresonant τ q (h j - h i₀))
    (g : ℂ → ℂ) (hg : MeromorphicOn g Set.univ)
    (hperiodOne : Function.Periodic g 1)
    (hperiodTau : Function.Periodic g τ)
    (heq : ∀ n : ℤ, thetaDifferentialFamilySum s L h τ =ᶠ[
      𝓝[≠] additiveOrbitPoint (thetaHalfPeriod τ - h i₀) q n]
      (fun z => g (z + q) - g z)) : False := by
  obtain ⟨hpole, hunique⟩ := thetaDifferentialFamilySum_singleton_poleOrbit
    hτ hq hnonres hi₀ hLi₀ hsep
  apply shiftCoboundary_not_singleton_poleOrbit_of_eventuallyEq g
    (thetaDifferentialFamilySum s L h τ)
    (thetaHalfPeriod τ - h i₀) q
  · intro n
    exact hg _ (Set.mem_univ _)
  · exact heq
  · exact poleIndexSet_finite_of_elliptic hτ hg hperiodOne hperiodTau hq
  · simpa [additiveOrbitPoint] using hpole
  · exact hunique

end

end GaloisForLFunctions
