import GaloisForLFunctions.HTGeometry.AtomicHerglotzResidueCone
import GaloisForLFunctions.HTGeometry.PrimeLogGibbsDifferentialTranslateFreenessUniversalityLaw

/-!
# Prime-log Gibbs atomic-Herglotz-cone universality

The universal prime-log source has three exact faces: every susceptibility jet is a locally
uniform finite Hermitian Gibbs limit, distinct translates admit no nontrivial
constant-coefficient differential cancellation, and finite atomic perturbations remain
Herglotz exactly on the nonnegative residue cone.
-/

open Complex Set Filter Finset Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Prime-log Gibbs atomic-Herglotz-cone universality law.**  One universal prime-log
background is simultaneously Gibbs-realizable in every jet order, differentially rigid under
finite translation packets, and the base point of an exactly classified finite atomic Herglotz
cone. -/
theorem
    universalFacetOrbitGauge_gibbsRealizable_atomicHerglotzCone_differentialTranslateFree
    (S : Finset ℕ) (a : ℕ → ℝ) :
    ((∀ z : ℂ, 0 < z.im →
        0 ≤ (universalResidueConeHerglotz S a z).im) ↔
      ∀ n ∈ S, 0 ≤ a n) ∧
    (∀ (H : Finset ℂ) (L : ℂ → Polynomial ℂ) {h₀ : ℂ}, h₀ ∈ H → L h₀ ≠ 0 →
      (∑ h ∈ H, constantCoeffDifferentialOperator (L h)
        (primeLogTranslate (fun q => universalFacetOrbitGauge q) h)) ≠ 0) ∧
    ∀ m : ℕ,
      TendstoLocallyUniformlyOn
        (universalPrimeLogFiniteHermitianGibbsJet m)
        (iteratedDeriv m
          (primeLogHerglotz (fun q => universalFacetOrbitGauge q)))
        Filter.atTop upperHalfPlane := by
  obtain ⟨hfree, hgibbs⟩ :=
    universalFacetOrbitGauge_gibbsRealizable_differentialTranslateFree
  exact ⟨universalResidueConeHerglotz_nonneg_iff S a, hfree, hgibbs⟩

end

end GaloisForLFunctions.HTGeometry
