import GaloisForLFunctions.HTGeometry.PrimeRadialFusionRankSurfaceRealization
import GaloisForLFunctions.HTGeometry.PrimeRadialRelativeJetRank

/-!
# Intrinsic transcendence-degree classification of prime-radial fusion fields

The fusion rank surface classifies radial profile algebras by their additive order submonoids.
Independently, every numerical rank entry is the ordinary transcendence degree of an intrinsic
finite-jet field over the complete invisible tail.  Their closure promotes the combinatorial
classification to a field-theoretic one and realizes every admissible intrinsic trdeg surface.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

/-- **Intrinsic trdeg-surface completeness.**  Two prime-radial fusion profile algebras have the
same transcendence degree at every visible cutoff and jet depth exactly when their additive order
submonoids agree. -/
theorem primeRadialIntrinsicJetTrdeg_surface_eq_iff_orderSubmonoid_eq
    (A B : NonUnitalSubalgebra ℂ PrimeRadialProfile) :
    (∀ N r,
      Algebra.trdeg (primeRadialTailDifferentialField A.toSubmodule N)
          (primeRadialFiniteJetField A.toSubmodule N r) =
        Algebra.trdeg (primeRadialTailDifferentialField B.toSubmodule N)
          (primeRadialFiniteJetField B.toSubmodule N r)) ↔
      primeRadialOrderSubmonoid A = primeRadialOrderSubmonoid B := by
  constructor
  · intro hsurface
    apply (primeRadialFusionKolchinRank_surface_eq_iff_orderSubmonoid_eq A B).1
    intro N r
    have h := hsurface N r
    rw [primeRadialFiniteJetField_trdeg_eq_relativeJetRank,
      primeRadialFiniteJetField_trdeg_eq_relativeJetRank] at h
    exact_mod_cast h
  · intro hmonoid N r
    have hrank :=
      (primeRadialFusionKolchinRank_surface_eq_iff_orderSubmonoid_eq A B).2 hmonoid N r
    rw [primeRadialFiniteJetField_trdeg_eq_relativeJetRank,
      primeRadialFiniteJetField_trdeg_eq_relativeJetRank]
    exact_mod_cast hrank

/-- **Intrinsic trdeg-surface realization.**  Every additive submonoid of `ℕ` is realized by an
embedded fusion-closed radial differential field whose visible finite-jet extensions have exactly
the corresponding cumulative counting transcendence degrees. -/
theorem primeRadialIntrinsicJetTrdegSurface_realizes_addSubmonoid
    (S : AddSubmonoid Nat) :
    ∃ A : NonUnitalSubalgebra ℂ PrimeRadialProfile,
      PrimeRadialCarrierFusionClosed A.toSubmodule ∧
      primeRadialOrderSubmonoid A = S ∧
      (∀ N,
        (primeRadialRelativeDifferentialField A.toSubmodule N).restrictScalars
            finitePrimeCoefficientField =
          primeRadialDifferentialField A.toSubmodule) ∧
      ∀ N r,
        Algebra.trdeg (primeRadialTailDifferentialField A.toSubmodule N)
            (primeRadialFiniteJetField A.toSubmodule N r) =
          (((r + 1) * primeRadialAddSubmonoidCount S N : Nat) : Cardinal) := by
  let A := primeRadialMonoidProfileAlgebra S
  obtain ⟨hfusion, horder, hrank⟩ :=
    primeRadialFusionRankSurface_realizes_addSubmonoid S
  refine ⟨A, hfusion, horder, ?_, ?_⟩
  · intro N
    exact primeRadialRelativeDifferentialField_restrictScalars_eq A.toSubmodule N
  · intro N r
    rw [primeRadialFiniteJetField_trdeg_eq_relativeJetRank]
    exact_mod_cast hrank N r

/-- **Universal intrinsic classification law.**  Complete finite-jet trdeg surfaces are precisely
the cumulative surfaces of additive submonoids, and every such surface occurs with exact
tail-extension generation. -/
theorem primeRadialIntrinsicJetTrdegSurface_completeClassification :
    (∀ A B : NonUnitalSubalgebra ℂ PrimeRadialProfile,
      (∀ N r,
        Algebra.trdeg (primeRadialTailDifferentialField A.toSubmodule N)
            (primeRadialFiniteJetField A.toSubmodule N r) =
          Algebra.trdeg (primeRadialTailDifferentialField B.toSubmodule N)
            (primeRadialFiniteJetField B.toSubmodule N r)) ↔
        primeRadialOrderSubmonoid A = primeRadialOrderSubmonoid B) ∧
    ∀ S : AddSubmonoid Nat,
      ∃ A : NonUnitalSubalgebra ℂ PrimeRadialProfile,
        PrimeRadialCarrierFusionClosed A.toSubmodule ∧
        primeRadialOrderSubmonoid A = S ∧
        (∀ N,
          (primeRadialRelativeDifferentialField A.toSubmodule N).restrictScalars
              finitePrimeCoefficientField =
            primeRadialDifferentialField A.toSubmodule) ∧
        ∀ N r,
          Algebra.trdeg (primeRadialTailDifferentialField A.toSubmodule N)
              (primeRadialFiniteJetField A.toSubmodule N r) =
            (((r + 1) * primeRadialAddSubmonoidCount S N : Nat) : Cardinal) := by
  exact ⟨primeRadialIntrinsicJetTrdeg_surface_eq_iff_orderSubmonoid_eq,
    primeRadialIntrinsicJetTrdegSurface_realizes_addSubmonoid⟩

end

end GaloisForLFunctions.HTGeometry
