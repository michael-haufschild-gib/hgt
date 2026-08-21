/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.BrauerFoundations
import GaloisForLFunctions.HTGeometry.ABHN.BrauerGroupStructure
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionBrauer
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionTensorProduct
import GaloisForLFunctions.HTGeometry.ABHN.Specification
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Brauer groups of finite fields for ABHN

Every finite-dimensional central simple algebra over a finite field is split.  The proof uses
Artin--Wedderburn, Wedderburn's little theorem, and centrality to show that the division-algebra
factor is the base field.  This supplies the vanishing of finite residue-field Brauer groups used
in unramified local theory, independently of the Galois-cohomology description.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- Every central simple algebra over a finite field has split Brauer class. -/
theorem finiteField_brauerClass_eq_split (K : Type u) [Field K] [Finite K] (A : CSA.{u, u} K) :
    brauerClass A = brauerSplitClass K := by
  haveI : IsArtinianRing A.carrier := IsArtinianRing.of_finite K A.carrier
  obtain ⟨n, hn, D, hD, hKD, hfinite, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A.carrier
  letI : DivisionRing D := hD
  letI : Algebra K D := hKD
  letI : Module.Finite K D := hfinite
  letI : Finite D := Module.finite_of_finite K
  letI : Algebra K (Matrix (Fin n) (Fin n) D) := Matrix.instAlgebra
  letI : Algebra.IsCentral K (Matrix (Fin n) (Fin n) D) :=
    Algebra.IsCentral.of_algEquiv K A.carrier (Matrix (Fin n) (Fin n) D) e
  have hbij : Function.Bijective (algebraMap K D) :=
    Algebra.IsCentral.baseField_essentially_unique K D (Matrix (Fin n) (Fin n) D)
  let d : K ≃ₐ[K] D := AlgEquiv.ofBijective (Algebra.ofId K D) hbij
  calc
    brauerClass A = brauerClass (matrixFinCSA (scalarCSA K) n) :=
      brauerClass_eq_of_algEquiv A (matrixFinCSA (scalarCSA K) n) (e.trans d.symm.mapMatrix)
    _ = brauerSplitClass K := brauerClass_matrixFinCSA_scalar_eq n

/-- Every Brauer class over a finite field is split. -/
theorem finiteField_brauerGroup_eq_split (K : Type u) [Field K] [Finite K]
    (x : BrauerGroup.{u, u} K) : x = brauerSplitClass K := by
  refine Quotient.inductionOn x ?_
  exact finiteField_brauerClass_eq_split K

/-- The Brauer group of a finite field is trivial. -/
theorem finiteField_brauerGroup_subsingleton (K : Type u) [Field K] [Finite K] :
    Subsingleton (BrauerGroup.{u, u} K) where
  allEq x y := (finiteField_brauerGroup_eq_split K x).trans
    (finiteField_brauerGroup_eq_split K y).symm

/-- Scalar extension sends every finite-field Brauer class to the split class.  This is a
functorial form of finite-field Brauer triviality, suitable for future residue-field transports. -/
theorem finiteField_scalarExtensionBrauerMap_eq_split
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Finite K]
    (x : BrauerGroup.{u, u} K) :
    scalarExtensionBrauerMap K L x = brauerSplitClass L := by
  rw [finiteField_brauerGroup_eq_split K x]
  exact scalarExtensionBrauerMap_split K L

/-- Scalar extension out of a finite-field Brauer group is the zero additive homomorphism. -/
theorem finiteField_scalarExtensionBrauerAddHom_eq_zero
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Finite K] :
    scalarExtensionBrauerAddHom K L = 0 := by
  ext x
  change scalarExtensionBrauerMap K L x = brauerSplitClass L
  exact finiteField_scalarExtensionBrauerMap_eq_split K L x

/-- The finite-field Brauer invariant is the unique zero-valued map to `ℚ/ℤ`.  The meaningful
local invariant for a complete discretely valued field requires further ramification theory;
this is the residue-field contribution to that construction. -/
noncomputable def finiteFieldBrauerInvariant (K : Type u) [Field K] [Finite K] :
    BrauerGroup.{u, u} K →+ RatModInt where
  toFun := fun _ ↦ 0
  map_zero' := rfl
  map_add' := by intros; simp

theorem finiteFieldBrauerInvariant_eq_zero (K : Type u) [Field K] [Finite K]
    (x : BrauerGroup.{u, u} K) : finiteFieldBrauerInvariant K x = 0 := rfl

/-- The finite-field Brauer invariant is injective because every finite-field Brauer class is
split. -/
theorem finiteFieldBrauerInvariant_injective (K : Type u) [Field K] [Finite K] :
    Function.Injective (finiteFieldBrauerInvariant K) := by
  letI : Subsingleton (BrauerGroup.{u, u} K) := finiteField_brauerGroup_subsingleton K
  intro x y _
  exact Subsingleton.elim _ _

/-- The image of the finite-field Brauer invariant is precisely `{0}`. -/
theorem finiteFieldBrauerInvariant_range (K : Type u) [Field K] [Finite K] :
    Set.range (finiteFieldBrauerInvariant K) = {0} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    exact ⟨brauerSplitClass K, rfl⟩

/-- The finite-field Brauer invariant is an additive equivalence onto the zero subgroup of
`ℚ/ℤ`. -/
noncomputable def finiteFieldBrauerInvariantAddEquivBot (K : Type u) [Field K] [Finite K] :
    BrauerGroup.{u, u} K ≃+ (⊥ : AddSubgroup RatModInt) := by
  let invariantToBot : BrauerGroup.{u, u} K →+ (⊥ : AddSubgroup RatModInt) :=
    { toFun := fun x => ⟨finiteFieldBrauerInvariant K x, by
        simpa using finiteFieldBrauerInvariant_eq_zero K x⟩
      map_zero' := by
        apply Subtype.ext
        change finiteFieldBrauerInvariant K 0 = 0
        exact finiteFieldBrauerInvariant_eq_zero K 0
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (finiteFieldBrauerInvariant K).map_add x y }
  apply AddEquiv.ofBijective invariantToBot
  constructor
  · intro x y h
    exact finiteFieldBrauerInvariant_injective K (congrArg Subtype.val h)
  · intro y
    refine ⟨brauerSplitClass K, ?_⟩
    apply Subtype.ext
    change finiteFieldBrauerInvariant K (brauerSplitClass K) = y.val
    have hy : (y : RatModInt) = 0 := y.property
    rw [finiteFieldBrauerInvariant_eq_zero, hy]

/-- The additive finite-field invariant equivalence has the defined invariant as its underlying
`ℚ/ℤ`-valued map. -/
theorem finiteFieldBrauerInvariantAddEquivBot_apply (K : Type u) [Field K] [Finite K]
    (x : BrauerGroup.{u, u} K) :
    ((finiteFieldBrauerInvariantAddEquivBot K x : (⊥ : AddSubgroup RatModInt)) : RatModInt) =
      finiteFieldBrauerInvariant K x := rfl

end GaloisForLFunctions.HTGeometry.ABHN
