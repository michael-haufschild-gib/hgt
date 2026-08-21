/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldCohomology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Frobenius lifts at finite residue fields

For a finite invariant extension of rings, at maximal ideals with finite upper residue field,
Mathlib identifies the decomposition group modulo inertia with the Galois group of residue
fields.  This file chooses the arithmetic Frobenius in that quotient, lifts it to the
decomposition group, and proves that its class generates the quotient.

This is the unramified part of local reciprocity.  It does not construct norm reciprocity for
ramified extensions, the Brauer--cohomology comparison, or the local Brauer invariant.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

universe u v w

section

variable {A : Type u} {B : Type v} {G : Type w}
  [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
  [Finite (B ⧸ Q)]

/-- Arithmetic Frobenius of the finite residue-field extension. -/
noncomputable def residueFrobenius : Gal((B ⧸ Q)/(A ⧸ P)) :=
  letI : Finite (A ⧸ P) :=
    Finite.of_injective (algebraMap (A ⧸ P) (B ⧸ Q))
      (FaithfulSMul.algebraMap_injective _ _)
  letI : Fintype (A ⧸ P) := Fintype.ofFinite _
  letI : Fintype (B ⧸ Q) := Fintype.ofFinite _
  FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ P) (B ⧸ Q)

/-- The residue arithmetic Frobenius has a lift to the decomposition group. -/
theorem exists_decompositionFrobenius :
    ∃ sigma : MulAction.stabilizer G Q,
      Ideal.Quotient.stabilizerHom Q P G sigma = residueFrobenius P Q := by
  exact Ideal.Quotient.stabilizerHom_surjective G P Q (residueFrobenius P Q)

/-- Every residue-field Galois automorphism is a power of arithmetic Frobenius. -/
theorem residueFrobenius_spec (tau : Gal((B ⧸ Q)/(A ⧸ P))) :
    tau ∈ Subgroup.zpowers (residueFrobenius P Q) := by
  letI : Finite (A ⧸ P) :=
    Finite.of_injective (algebraMap (A ⧸ P) (B ⧸ Q))
      (FaithfulSMul.algebraMap_injective _ _)
  letI : Fintype (A ⧸ P) := Fintype.ofFinite _
  letI : Fintype (B ⧸ Q) := Fintype.ofFinite _
  obtain ⟨n, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (A ⧸ P) (B ⧸ Q)).surjective tau
  rw [← hn]
  exact Subgroup.npow_mem_zpowers _ n

/-- A chosen Frobenius lift in the decomposition group. -/
noncomputable def decompositionFrobeniusLift : MulAction.stabilizer G Q :=
  (exists_decompositionFrobenius (G := G) P Q).choose

/-- The chosen decomposition-group lift induces residue arithmetic Frobenius. -/
theorem decompositionFrobeniusLift_spec :
    Ideal.Quotient.stabilizerHom Q P G (decompositionFrobeniusLift (G := G) P Q) =
      residueFrobenius P Q :=
  (exists_decompositionFrobenius (G := G) P Q).choose_spec

/-- The residual action of the chosen Frobenius lift generates the residue Galois group. -/
theorem decompositionFrobeniusLift_generator
    (tau : Gal((B ⧸ Q)/(A ⧸ P))) :
    tau ∈ Subgroup.zpowers
      (Ideal.Quotient.stabilizerHom Q P G (decompositionFrobeniusLift (G := G) P Q)) := by
  rw [decompositionFrobeniusLift_spec]
  exact residueFrobenius_spec P Q tau

/-- The class of the chosen Frobenius lift in decomposition modulo inertia. -/
noncomputable def decompositionFrobeniusClass :
    MulAction.stabilizer G Q ⧸ Q.inertia (MulAction.stabilizer G Q) :=
  QuotientGroup.mk (decompositionFrobeniusLift (G := G) P Q)

/-- Frobenius generates decomposition modulo inertia. -/
theorem decompositionFrobeniusClass_generator
    (x : MulAction.stabilizer G Q ⧸ Q.inertia (MulAction.stabilizer G Q)) :
    x ∈ Subgroup.zpowers (decompositionFrobeniusClass (G := G) P Q) := by
  let e := Ideal.Quotient.stabilizerQuotientInertiaEquiv G P Q
  have he : e (decompositionFrobeniusClass (G := G) P Q) = residueFrobenius P Q := by
    change Ideal.Quotient.stabilizerHom Q P G
      (decompositionFrobeniusLift (G := G) P Q) = residueFrobenius P Q
    exact decompositionFrobeniusLift_spec (G := G) P Q
  have hx : e x ∈ Subgroup.zpowers (e (decompositionFrobeniusClass (G := G) P Q)) := by
    rw [he]
    exact residueFrobenius_spec P Q (e x)
  have hx' : e x ∈ (Subgroup.zpowers (decompositionFrobeniusClass (G := G) P Q)).map
      e.toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    exact hx
  obtain ⟨y, hy, hey⟩ := hx'
  have hxy : x = y := e.injective (by simpa using hey.symm)
  rw [hxy]
  exact hy

/-- The chosen Frobenius class generates the entire decomposition quotient. -/
theorem decompositionFrobeniusClass_zpowers_eq_top :
    Subgroup.zpowers (decompositionFrobeniusClass (G := G) P Q) = ⊤ := by
  apply le_antisymm le_top
  intro x _
  exact decompositionFrobeniusClass_generator (G := G) P Q x

include P in
/-- The decomposition group modulo inertia is cyclic at a finite residue field. -/
theorem decompositionQuotient_isCyclic :
    IsCyclic (MulAction.stabilizer G Q ⧸ Q.inertia (MulAction.stabilizer G Q)) := by
  constructor
  refine ⟨decompositionFrobeniusClass (G := G) P Q, ?_⟩
  intro x
  exact Subgroup.mem_zpowers_iff.mp
    (decompositionFrobeniusClass_generator (G := G) P Q x)

end

section FiniteResidueNorm

variable {A B G : Type}
  [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
  [Finite (B ⧸ Q)]

/-- The finite-residue norm sequence is exact for the arithmetic Frobenius lifted by the
decomposition group.  This is the residue-field part of local norm reciprocity; lifting norm
statements through a valuation ring remains a separate local-field theorem. -/
theorem residueFrobenius_fullNormSequence :
    Function.Injective (cyclicGaloisBaseUnitsMap (K := A ⧸ P) (L := B ⧸ Q)) ∧
      Function.Exact (cyclicGaloisBaseUnitsMap (K := A ⧸ P) (L := B ⧸ Q))
        (cyclicGaloisAdditiveCoboundary (residueFrobenius P Q)) ∧
      Function.Exact (cyclicGaloisAdditiveCoboundary (residueFrobenius P Q))
        (cyclicGaloisAdditiveNormUnits (A ⧸ P) (B ⧸ Q)) ∧
      Function.Surjective (cyclicGaloisAdditiveNormUnits (A ⧸ P) (B ⧸ Q)) := by
  exact finiteField_cyclicGaloisFullNormSequence (residueFrobenius_spec P Q)

end FiniteResidueNorm

section FiniteResidueCohomology

open CategoryTheory groupCohomology Rep

attribute [local instance] IsCyclic.commGroup

variable {A B G : Type}
  [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
  [Finite (B ⧸ Q)]

/-- Degree-two unit Galois cohomology of every finite residue-field extension vanishes.  This is
the cohomological counterpart of the residue norm sequence and the zero residue Brauer group. -/
theorem residueH2_eq_zero
    (z : groupCohomology (Rep.ofAlgebraAutOnUnits (A ⧸ P) (B ⧸ Q)) 2) : z = 0 :=
  finiteField_H2_eq_zero z

/-- Degree-two unit Galois cohomology at a finite residue extension is trivial. -/
theorem residueH2_subsingleton :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits (A ⧸ P) (B ⧸ Q)) 2) :=
  finiteField_H2_subsingleton

end FiniteResidueCohomology

end GaloisForLFunctions.HTGeometry.ABHN
