import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeValuationMaster
import GaloisForLFunctions.HTGeometry.PrimeValuationProfileFieldClassification

/-!
# Tail-dense observable field classification

A tail-dense prime profile turns finite-dimensional spaces of continuous source observables into
embedded differential fields without losing the source linear geometry.  One common Dirichlet
shift already suffices: membership in the generated differential field is exactly membership in
the linear span of the source observables on the constraint set.  Consequently field inclusion
and field equality are classified by inclusion and equality of observable subspaces.

This is the source-space form of valuation--Hilbert completeness.  Polynomial restriction spaces
recover the homogeneous Hilbert layers, while arbitrary continuous observable spaces give the
intrinsic field-moduli statement.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped Differential

noncomputable section

universe u

/-- The differential carrier of a continuous observable sampled by a prime profile. -/
def tailDenseObservableShiftCarrier
    {V : Type*} (x : Nat.Primes → V) (f : V → ℂ) (a : ℂ) :
    arithmeticFunctionRationalCoordinateField :=
  primeCoefficientShiftCarrier (fun p => f (x p)) a

/-- Every finite linearly independent family of continuous observables on the constraint set
gives a differentially independent family of prime-supported carriers at any one common shift. -/
theorem cofiniteTailDenseOn_observableShiftCarrier_differentialIndependent
    {V J : Type u} [TopologicalSpace V] [Fintype J] [DecidableEq J] [Nonempty J]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j => fun v : K => f j v.1))
    (a : ℂ) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (fun j => tailDenseObservableShiftCarrier x (f j) a) := by
  let P : PrimeValuationRecurringPivotPresentation 1 (fun _ => J) (fun _ => J) where
    pivot _ j p := f j (x p)
    dependent _ _ _ := 0
    coefficient _ _ _ := 0
    pivotShiftJetTailIndependent := by
      intro r A _ alpha hdistinct m
      simpa using
        cofiniteTailDenseOn_primePowerShiftedRotatedJet_tailIndependent
          r.1 x K hx f hf hlinear alpha hdistinct m
    residualFinite := by
      intro _ _
      simp
  let alpha : ∀ _ : Fin 1, Unit → ℂ := fun _ _ => a
  have hP := P.pivotPalette_differentialIndependent alpha (fun _ => by
    intro b c _
    exact Subsingleton.elim b c)
  let e : J → Σ r : Fin 1, J × Unit := fun j => ⟨0, (j, ())⟩
  have he : Function.Injective e := by
    intro j k h
    exact congrArg (fun z => z.2.1) h
  have hsub := hP.comp e he
  simpa [e, P, alpha, PrimeValuationRecurringPivotPresentation.pivotPalette,
    tailDenseObservableShiftCarrier] using hsub

end

end GaloisForLFunctions.HTGeometry
