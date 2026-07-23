import GaloisForLFunctions.HTGeometry.CofiniteTailGramPolarization
import GaloisForLFunctions.HTGeometry.UpperEndLiteralLinearIndependence

/-!
# Literal tail independence from the upper-end carrier

Upper-end meromorphic independence is stronger than ordinary independence of literal functions.
A coefficient combination supported at only finitely many complex points has zero germ at the
upper end, so all its coefficients vanish.  Thus every finite deletion of the evaluation domain
preserves linear independence and strict square Gram realizability.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Filter

noncomputable section

local instance upperEndLiteralTailIndependenceDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance upperEndLiteralTailIndependenceComplexAlgebra :
    Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

/-- Meromorphic independence of upper-end analytic representatives forces independence of the
literal functions modulo every finite subset of the complex evaluation domain. -/
theorem tailCoefficientIndependent_literal_of_upperEndMero
    {ι : Type*} [Fintype ι]
    (u : ι → ℂ → ℂ) (analytic : ι → upperEndAnalyticSubring)
    (hcoe : ∀ i, upperEndAnalyticSubring.subtype (analytic i) =
      Germ.coeRingHom upperEndFilter (u i))
    (hmero : LinearIndependent ℂ
      (fun i => algebraMap upperEndAnalyticSubring upperEndMeroField (analytic i))) :
    TailCoefficientIndependent u := by
  classical
  intro c hsupp
  apply coefficients_eq_zero_of_upperEndGerm_eq_zero u analytic hcoe hmero c
  have hbdd : BddAbove
      (Complex.im '' {z : ℂ | ∑ i, c i * u i z ≠ 0}) :=
    (hsupp.image Complex.im).bddAbove
  obtain ⟨H, hH⟩ := bddAbove_def.mp hbdd
  apply Germ.coe_eq.mpr
  change ∀ᶠ z in upperEndFilter, (∑ i, c i • u i) z = 0
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨H, trivial, ?_⟩
  intro z hz
  have hzero : ∑ i, c i * u i z = 0 := by
    by_contra hne
    have him : z.im ≤ H := hH z.im ⟨z, hne, rfl⟩
    exact (not_le_of_gt hz) him
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hzero

end

end GaloisForLFunctions.HTGeometry
