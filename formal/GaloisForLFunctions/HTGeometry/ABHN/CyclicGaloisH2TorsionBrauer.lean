/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerSubgroup
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerInverse
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsion

/-!
# Torsion-indexed cyclic Brauer representatives

An identification of finite continuous cyclic `H²` with `ℚ/ℤ[n]` indexes the existing cyclic
Brauer representatives by their actual finite local-invariant values.  Every such representative
splits over the defining cyclic extension.  No injectivity, surjectivity, or additivity claim is
made for this parameter map into the Brauer group.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-- A finite `ℚ/ℤ[n]` local-invariant value selects a cyclic Brauer representative. -/
noncomputable def finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n) :
    ratModIntNTorsion n → BrauerGroup K :=
  fun z ↦ finiteGaloisContinuousCyclicH2BrauerMap K L (e.symm z)

/-- A torsion-indexed cyclic Brauer representative becomes split over its defining cyclic
extension. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_scalarExtension_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (m : ℕ) (hdeg : Module.finrank K L = m + 1) (z : ratModIntNTorsion n) :
    scalarExtensionBrauerMap K L
      (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z) =
        brauerSplitClass L := by
  change scalarExtensionBrauerMap K L
    (finiteGaloisContinuousCyclicH2BrauerMap K L (e.symm z)) = brauerSplitClass L
  exact finiteGaloisContinuousCyclicH2BrauerMap_scalarExtension_eq_split K L m hdeg _

/-- A torsion-indexed cyclic Brauer representative lies in the defining relative Brauer kernel. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_mem_scalarExtensionBrauerKernel
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (m : ℕ) (hdeg : Module.finrank K L = m + 1) (z : ratModIntNTorsion n) :
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z ∈
      scalarExtensionBrauerKernel K L :=
  (mem_scalarExtensionBrauerKernel_iff K L _).mpr
    (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_scalarExtension_eq_split
      K L n e m hdeg z)

/-- The finite `ℚ/ℤ[n]` cyclic local-invariant parameter map, with its defining-field splitting
property retained in the relative Brauer kernel. -/
noncomputable def finiteGaloisContinuousCyclicH2TorsionInvariantRelativeBrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (m : ℕ) (hdeg : Module.finrank K L = m + 1) :
    ratModIntNTorsion n → scalarExtensionBrauerKernel K L :=
  fun z ↦ ⟨finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z,
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_mem_scalarExtensionBrauerKernel
      K L n e m hdeg z⟩

/-- Forgetting the relative-kernel witness recovers the selected torsion-indexed Brauer class. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantRelativeBrauerMap_coe
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (m : ℕ) (hdeg : Module.finrank K L = m + 1) (z : ratModIntNTorsion n) :
    (finiteGaloisContinuousCyclicH2TorsionInvariantRelativeBrauerMap K L n e m hdeg z :
      BrauerGroup K) = finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z := rfl

/-- The zero torsion value selects the split Brauer class. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_zero_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n) :
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e 0 = brauerSplitClass K := by
  change finiteGaloisContinuousCyclicH2BrauerMap K L (e.symm 0) = brauerSplitClass K
  rw [e.symm.map_zero]
  exact finiteGaloisContinuousCyclicH2BrauerMap_zero_eq_split K L

/-- Negation of a finite `ℚ/ℤ[n]` local-invariant value gives the Brauer inverse of its selected
cyclic representative.  This is the inverse half of a local invariant homomorphism, without
assuming the missing cyclic tensor-product addition law. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_brauerTensorNeg
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : ratModIntNTorsion n) :
    brauerTensorNeg K (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z) =
      finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e (-z) := by
  change brauerTensorNeg K (finiteGaloisContinuousCyclicH2BrauerMap K L (e.symm z)) =
    finiteGaloisContinuousCyclicH2BrauerMap K L (e.symm (-z))
  rw [map_neg]
  exact finiteGaloisContinuousCyclicH2BrauerMap_brauerTensorNeg K L (e.symm z)

/-- A torsion-indexed cyclic Brauer representative belongs to the additive cyclic Brauer
subgroup generated by the cyclic Galois algebra classes. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_mem_cyclicGaloisBrauerSubgroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : ratModIntNTorsion n) :
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z ∈
      cyclicGaloisBrauerSubgroup K L := by
  change finiteGaloisContinuousCyclicH2BrauerMap K L (e.symm z) ∈
    cyclicGaloisBrauerSubgroup K L
  exact finiteGaloisContinuousCyclicH2BrauerMap_mem_cyclicGaloisBrauerSubgroup K L _

/-- The finite `ℚ/ℤ[n]` cyclic local-invariant parameter map with codomain restricted to the
cyclic Brauer subgroup generated by its defining extension. -/
noncomputable def finiteGaloisContinuousCyclicH2TorsionInvariantBrauerSubgroupMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n) :
    ratModIntNTorsion n → cyclicGaloisBrauerSubgroup K L :=
  fun z ↦ ⟨finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z,
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_mem_cyclicGaloisBrauerSubgroup
      K L n e z⟩

/-- Forgetting the cyclic-subgroup witness recovers the selected torsion-indexed Brauer class. -/
theorem finiteGaloisContinuousCyclicH2TorsionInvariantBrauerSubgroupMap_coe
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : ratModIntNTorsion n) :
    (finiteGaloisContinuousCyclicH2TorsionInvariantBrauerSubgroupMap K L n e z : BrauerGroup K) =
      finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z := rfl

end GaloisForLFunctions.HTGeometry.ABHN
