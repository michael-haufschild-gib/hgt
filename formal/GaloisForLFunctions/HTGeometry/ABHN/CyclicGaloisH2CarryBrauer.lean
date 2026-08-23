/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2CarryNormQuotient
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerInverse

/-!
# Literal carry coordinates for cyclic Brauer representatives

On a finite cyclic norm quotient, literal carry classes parameterize all selected cyclic Brauer
representatives.  Every such representative is split by the defining extension, zero selects the
split class, and carry-coordinate negation selects the Brauer inverse.  The map remains a function,
not an additive homomorphism, until the cyclic-algebra tensor-product comparison is available.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-- Selected cyclic Brauer representative indexed by the literal carry model of the norm
quotient. -/
noncomputable def cyclicGaloisCarryNormQuotientBrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)] :
    Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L → BrauerGroup K :=
  fun q => cyclicGaloisH2BrauerMap K L (cyclicGaloisCarryNormQuotientEquiv K L q)

/-- A base-unit quotient representative selects the Brauer class indexed by its literal carry
two-cocycle. -/
@[simp] theorem cyclicGaloisCarryNormQuotientBrauerMap_mk
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    (a : Additive Kˣ) :
    cyclicGaloisCarryNormQuotientBrauerMap K L (QuotientAddGroup.mk a) =
      cyclicGaloisH2BrauerMap K L (cyclicGaloisCarryH2Class K L a) := by
  rw [cyclicGaloisCarryNormQuotientBrauerMap,
    cyclicGaloisCarryNormQuotientEquiv_mk]

/-- Carry and periodic norm-quotient Brauer parameterizations differ exactly by the finite
periodic-to-carry automorphism of cyclic `H²`. -/
theorem cyclicGaloisCarryNormQuotientBrauerMap_eq_periodicCarryAutomorphism
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    (q : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L) :
    cyclicGaloisCarryNormQuotientBrauerMap K L q =
      cyclicGaloisH2BrauerMap K L
        (cyclicGaloisH2PeriodicCarryAutomorphism K L
          (cyclicGaloisH2BaseNormQuotientEquiv K L q)) := by
  change cyclicGaloisH2BrauerMap K L (cyclicGaloisCarryNormQuotientEquiv K L q) =
    cyclicGaloisH2BrauerMap K L
      (cyclicGaloisCarryNormQuotientEquiv K L
        ((cyclicGaloisH2BaseNormQuotientEquiv K L).symm
          (cyclicGaloisH2BaseNormQuotientEquiv K L q)))
  rw [AddEquiv.symm_apply_apply]

/-- Literal carry coordinates exhaust exactly the selected cyclic `H²` Brauer representatives. -/
theorem cyclicGaloisCarryNormQuotientBrauerMap_range
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)] :
    Set.range (cyclicGaloisCarryNormQuotientBrauerMap K L) =
      Set.range (cyclicGaloisH2BrauerMap K L) := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨cyclicGaloisCarryNormQuotientEquiv K L q, rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨(cyclicGaloisCarryNormQuotientEquiv K L).symm z, ?_⟩
    change cyclicGaloisH2BrauerMap K L
      (cyclicGaloisCarryNormQuotientEquiv K L
        ((cyclicGaloisCarryNormQuotientEquiv K L).symm z)) = _
    rw [AddEquiv.apply_symm_apply]

/-- Every carry-indexed cyclic Brauer representative becomes split after scalar extension to its
defining cyclic field. -/
theorem cyclicGaloisCarryNormQuotientBrauerMap_scalarExtension_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    (n : ℕ) (hdegree : Module.finrank K L = n + 1)
    (q : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L) :
    scalarExtensionBrauerMap K L (cyclicGaloisCarryNormQuotientBrauerMap K L q) =
      brauerSplitClass L := by
  exact cyclicGaloisH2BrauerMap_scalarExtension_eq_split K L n hdegree
    (cyclicGaloisCarryNormQuotientEquiv K L q)

/-- Every carry-indexed representative belongs to the relative Brauer kernel cut out by the
defining cyclic extension. -/
theorem cyclicGaloisCarryNormQuotientBrauerMap_mem_scalarExtensionBrauerKernel
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    (n : ℕ) (hdegree : Module.finrank K L = n + 1)
    (q : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L) :
    cyclicGaloisCarryNormQuotientBrauerMap K L q ∈ scalarExtensionBrauerKernel K L :=
  (mem_scalarExtensionBrauerKernel_iff K L _).mpr
    (cyclicGaloisCarryNormQuotientBrauerMap_scalarExtension_eq_split
      K L n hdegree q)

/-- Zero carry coordinate selects the split Brauer class. -/
theorem cyclicGaloisCarryNormQuotientBrauerMap_zero_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)] :
    cyclicGaloisCarryNormQuotientBrauerMap K L 0 = brauerSplitClass K := by
  change cyclicGaloisH2BrauerMap K L
    (cyclicGaloisCarryNormQuotientEquiv K L 0) = brauerSplitClass K
  rw [map_zero]
  exact cyclicGaloisH2BrauerMap_zero_eq_split K L

/-- Negating a carry coordinate selects the Brauer inverse. -/
theorem cyclicGaloisCarryNormQuotientBrauerMap_brauerTensorNeg
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    (q : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L) :
    brauerTensorNeg K (cyclicGaloisCarryNormQuotientBrauerMap K L q) =
      cyclicGaloisCarryNormQuotientBrauerMap K L (-q) := by
  change brauerTensorNeg K
      (cyclicGaloisH2BrauerMap K L (cyclicGaloisCarryNormQuotientEquiv K L q)) =
    cyclicGaloisH2BrauerMap K L (cyclicGaloisCarryNormQuotientEquiv K L (-q))
  rw [map_neg]
  exact cyclicGaloisH2BrauerMap_brauerTensorNeg K L
    (cyclicGaloisCarryNormQuotientEquiv K L q)

end GaloisForLFunctions.HTGeometry.ABHN
