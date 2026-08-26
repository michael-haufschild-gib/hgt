import GaloisForLFunctions.HTGeometry.MixedProjectionTensorBialgebra
import GaloisForLFunctions.HTGeometry.HopfIdealKernel
import GaloisForLFunctions.HTGeometry.AddMonoidAlgebraTensorCoefficients
import GaloisForLFunctions.HTGeometry.TensorGroupHopfEquiv
import GaloisForLFunctions.HTGeometry.CommonHopfSubalgebraTrivial
import GaloisForLFunctions.HTGeometry.GroupGradedHopfSkewPrimitive

/-!
# The residual mixed Hopf kernel

The joint tensor presentation of the torus and additive projection images is a surjective
bialgebra morphism.  This file names its exact kernel, proves that it is a Hopf ideal, and proves
that it has zero intersection with either pure factor.  Thus all remaining subgroup-classification
content is concentrated in one genuinely mixed Hopf ideal.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace MixedProjectionTensorKernel

noncomputable section

open AffineExponentialGroup AffineExponentialProjectionImages
open AffineExponentialProjectionClassification
open MixedTorusProjectionSaturation MixedAdditiveProjectionClassification
open MixedProjectionTensorBialgebra

variable (k : Type*) [Field k]
variable {n : ℕ} (I : Ideal (CoordinateAlgebra k n)) [I.IsHopfIdeal k]

local instance torusProjectionHopfIdeal :
    (torusProjectionIdeal k I).IsHopfIdeal k :=
  torusProjectionIdeal_isHopfIdeal k I

local instance additiveProjectionHopfIdeal :
    (additiveProjectionIdeal k I).IsHopfIdeal k :=
  additiveProjectionIdeal_isHopfIdeal k I

local instance mixedQuotientCoideal :
    (I.restrictScalars k).IsCoideal := Ideal.IsHopfIdeal.toIsCoideal

local instance mixedQuotientHopfAlgebra :
    HopfAlgebra k (CoordinateAlgebra k n ⧸ I) := by
  infer_instance

/-- Domain of the classified joint torus-additive tensor presentation. -/
abbrev MixedProjectionTensor :=
  AddMonoidAlgebra k
      ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I) ⊗[k]
    SymmetricAlgebra k
      ((Fin n → k) ⧸ additiveRelationSubspace k I)

/-- Group-graded form of the classified mixed projection tensor product. -/
abbrev GroupGradedMixedProjection :=
  AddMonoidAlgebra
    (SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I))
    ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I)

/-- Classified torus factor embedded in the actual mixed quotient as a bialgebra morphism. -/
noncomputable def torusFactorBialgHom :
    AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I) →ₐc[k]
      CoordinateAlgebra k n ⧸ I :=
  (mixedProjectionTensorBialgHom k I).comp
    (leftCoordinateInclusion k
      (AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I))
      (SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I)))

/-- Classified additive factor embedded in the actual mixed quotient as a bialgebra morphism. -/
noncomputable def additiveFactorBialgHom :
    SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I) →ₐc[k]
      CoordinateAlgebra k n ⧸ I :=
  (mixedProjectionTensorBialgHom k I).comp
    (rightCoordinateInclusion k
      (AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I))
      (SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I)))

/-- The torus factor bialgebra map is the previously classified torus factor algebra map. -/
theorem torusFactorBialgHom_toAlgHom :
    (torusFactorBialgHom k I).toAlgHom =
      torusRelationGroupAlgHomIntoSubgroupQuotient k I := by
  apply DFunLike.ext _ _
  intro x
  change MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom k I
      (x ⊗ₜ[k] 1) = torusRelationGroupAlgHomIntoSubgroupQuotient k I x
  rw [MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom_tmul, map_one]
  exact mul_one (torusRelationGroupAlgHomIntoSubgroupQuotient k I x)

/-- The additive factor bialgebra map is the previously classified additive factor algebra map. -/
theorem additiveFactorBialgHom_toAlgHom :
    (additiveFactorBialgHom k I).toAlgHom =
      additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I := by
  apply DFunLike.ext _ _
  intro x
  change MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom k I
      (1 ⊗ₜ[k] x) = additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I x
  rw [MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom_tmul, map_one]
  exact one_mul (additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I x)

/-- The classified torus factor bialgebra embedding is injective. -/
theorem torusFactorBialgHom_injective : Function.Injective (torusFactorBialgHom k I) := by
  intro x y hxy
  apply torusRelationGroupAlgHomIntoSubgroupQuotient_injective k I
  rw [← torusFactorBialgHom_toAlgHom]
  exact hxy

/-- The classified additive factor bialgebra embedding is injective in characteristic zero. -/
theorem additiveFactorBialgHom_injective [CharZero k] :
    Function.Injective (additiveFactorBialgHom k I) := by
  intro x y hxy
  apply additiveRelationSymmetricAlgHomIntoSubgroupQuotient_injective k I
  rw [← additiveFactorBialgHom_toAlgHom]
  exact hxy

/-- The two classified factor images inside the mixed quotient intersect exactly in the same
scalar.  This is the concrete common-factor conclusion required by Hopf-Goursat. -/
theorem factor_images_intersection_eq_scalars [CharZero k]
    (a : AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I))
    (b : SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I))
    (hab : torusFactorBialgHom k I a = additiveFactorBialgHom k I b) :
    ∃ c : k,
      a = algebraMap k
          (AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I)) c ∧
      b = algebraMap k
          (SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I)) c := by
  let basis := Module.Free.chooseBasis k
    ((Fin n → k) ⧸ additiveRelationSubspace k I)
  exact group_symmetric_image_intersection_eq_scalars
    (k := k)
    (M := (Fin n →₀ ℤ) ⧸ torusRelationLattice k I)
    (H := CoordinateAlgebra k n ⧸ I)
    (V := (Fin n → k) ⧸ additiveRelationSubspace k I) basis
    (torusFactorBialgHom k I) (torusFactorBialgHom_injective k I)
    (additiveFactorBialgHom k I) (additiveFactorBialgHom_injective k I)
    a b hab

/-- The joint presentation transported to the group-graded coefficient algebra. -/
noncomputable def groupGradedJointBialgHom :
    GroupGradedMixedProjection k I →ₐc[k] CoordinateAlgebra k n ⧸ I :=
  (mixedProjectionTensorBialgHom k I).comp
    (TensorGroupEquiv.tensorGroupBialgEquiv
      (k := k)
      (B := SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I))
      (M := (Fin n →₀ ℤ) ⧸ torusRelationLattice k I)).symm.toBialgHom

/-- A homogeneous group-graded coefficient maps to the product of its torus monomial and
additive coefficient images. -/
@[simp] theorem groupGradedJointBialgHom_single
    (m : (Fin n →₀ ℤ) ⧸ torusRelationLattice k I)
    (b : SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I)) :
    groupGradedJointBialgHom k I (AddMonoidAlgebra.single m b) =
      torusRelationGroupAlgHomIntoSubgroupQuotient k I
          (AddMonoidAlgebra.single m (1 : k)) *
        additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I b := by
  change mixedProjectionTensorBialgHom k I
      ((TensorGroupEquiv.tensorGroupBialgEquiv
        (k := k)
        (B := SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I))
        (M := (Fin n →₀ ℤ) ⧸ torusRelationLattice k I)).symm
          (AddMonoidAlgebra.single m b)) = _
  rw [TensorGroupEquiv.tensorGroupBialgEquiv_symm_single]
  change MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom k I
      (AddMonoidAlgebra.single m (1 : k) ⊗ₜ[k] b) = _
  rw [MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom_tmul]

/-- The group-graded presentation remains surjective. -/
theorem groupGradedJointBialgHom_surjective :
    Function.Surjective (groupGradedJointBialgHom k I) :=
  (mixedProjectionTensorBialgHom_surjective k I).comp
    (TensorGroupEquiv.tensorGroupBialgEquiv
      (k := k)
      (B := SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I))
      (M := (Fin n →₀ ℤ) ⧸ torusRelationLattice k I)).symm.surjective

/-- Decompose a mixed tensor into its finitely supported family of additive coefficients, indexed
by torus weights. -/
noncomputable def torusCoefficientEquiv :
    MixedProjectionTensor k I ≃ₗ[k]
      ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I →₀
        SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I)) :=
  AddMonoidAlgebraTensorCoefficients.tensorCoeffEquiv
    (M := (Fin n →₀ ℤ) ⧸ torusRelationLattice k I) k
    (SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I))

@[simp]
theorem torusCoefficientEquiv_tmul_apply
    (x : AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I))
    (y : SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I))
    (m : (Fin n →₀ ℤ) ⧸ torusRelationLattice k I) :
    torusCoefficientEquiv k I (x ⊗ₜ[k] y) m = x.coeff m • y :=
  AddMonoidAlgebraTensorCoefficients.tensorCoeffEquiv_tmul_apply k _ x y m

/-- A mixed tensor vanishes exactly when every torus-weight coefficient vanishes. -/
theorem eq_zero_iff_torusCoefficientEquiv_apply
    (z : MixedProjectionTensor k I) :
    z = 0 ↔ ∀ m, torusCoefficientEquiv k I z m = 0 :=
  AddMonoidAlgebraTensorCoefficients.eq_zero_iff_tensorCoeffEquiv_apply k _ z

/-- Finite set of torus weights occurring in a mixed tensor. -/
noncomputable def torusSupport (z : MixedProjectionTensor k I) :
    Finset ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I) := by
  classical
  exact (torusCoefficientEquiv k I z).support

/-- A mixed tensor supported at one torus weight is the corresponding pure tensor. -/
theorem eq_single_tmul_of_torusSupport_eq_singleton
    (z : MixedProjectionTensor k I)
    (m : (Fin n →₀ ℤ) ⧸ torusRelationLattice k I)
    (h : torusSupport k I z = {m}) :
    z = AddMonoidAlgebra.single m (1 : k) ⊗ₜ[k] torusCoefficientEquiv k I z m := by
  classical
  apply (torusCoefficientEquiv k I).injective
  apply Finsupp.ext
  intro a
  rw [torusCoefficientEquiv_tmul_apply]
  by_cases ham : a = m
  · subst a
    simp
  · have ha : a ∉ torusSupport k I z := by simp [h, ham]
    have hcoeff : torusCoefficientEquiv k I z a = 0 := by
      simpa [torusSupport, Finsupp.mem_support_iff] using ha
    simp [ham, hcoeff]

-- `Ideal.IsHopfIdeal` is indexed by a `Ring`, while the tensor-product bialgebra uses its direct
-- `Semiring` instance.  These aligned structures contain the same operations but make that
-- definitional choice explicit, avoiding an instance diamond in the generic kernel theorem.
@[reducible] def mixedProjectionTensorDefaultCommRing :
    CommRing (MixedProjectionTensor k I) := inferInstance

@[reducible] def mixedProjectionTargetDefaultCommRing :
    CommRing (CoordinateAlgebra k n ⧸ I) := inferInstance

local instance mixedProjectionTensorRing : Ring (MixedProjectionTensor k I) :=
  { (mixedProjectionTensorDefaultCommRing k I).toRing with
    toSemiring := inferInstance }

local instance mixedProjectionTensorCommRing : CommRing (MixedProjectionTensor k I) :=
  CommRing.mk (mixedProjectionTensorDefaultCommRing k I).mul_comm

local instance mixedProjectionTargetRing : Ring (CoordinateAlgebra k n ⧸ I) :=
  { (mixedProjectionTargetDefaultCommRing k I).toRing with
    toSemiring := inferInstance }

local instance mixedProjectionTargetCommRing : CommRing (CoordinateAlgebra k n ⧸ I) :=
  CommRing.mk (mixedProjectionTargetDefaultCommRing k I).mul_comm

/-- The one residual relation ideal after classifying both factor projections. -/
noncomputable def jointKernel : Ideal (MixedProjectionTensor k I) :=
  RingHom.ker (mixedProjectionTensorBialgHom k I).toAlgHom.toRingHom

/-- Residual kernel in the equivalent group-graded coefficient presentation. -/
noncomputable def groupGradedJointKernel : Ideal (GroupGradedMixedProjection k I) :=
  RingHom.ker (groupGradedJointBialgHom k I).toAlgHom.toRingHom

/-- Kernel membership transports exactly across the tensor/group-graded bialgebra equivalence. -/
theorem mem_groupGradedJointKernel_iff (z : GroupGradedMixedProjection k I) :
    z ∈ groupGradedJointKernel k I ↔
      (TensorGroupEquiv.tensorGroupBialgEquiv
        (k := k)
        (B := SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I))
        (M := (Fin n →₀ ℤ) ⧸ torusRelationLattice k I)).symm z ∈ jointKernel k I :=
  Iff.rfl

/-- The residual joint kernel is an actual Hopf ideal, not merely the kernel of an algebra map. -/
theorem jointKernel_isHopfIdeal : (jointKernel k I).IsHopfIdeal k := by
  exact @HopfIdealKernel.ker_isHopfIdeal
    k (MixedProjectionTensor k I) (CoordinateAlgebra k n ⧸ I)
    inferInstance (mixedProjectionTensorCommRing k I)
    (mixedProjectionTargetCommRing k I) inferInstance inferInstance
    (mixedProjectionTensorBialgHom k I)

/-- The equivalent group-graded residual kernel is an actual Hopf ideal. -/
theorem groupGradedJointKernel_isHopfIdeal :
    (groupGradedJointKernel k I).IsHopfIdeal k := by
  exact HopfIdealKernel.ker_isHopfIdeal (groupGradedJointBialgHom k I)

/-- The residual mixed kernel contains no nonzero element supported purely on the torus factor. -/
theorem tmul_one_mem_jointKernel_iff
    (x : AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I)) :
    x ⊗ₜ[k] (1 : SymmetricAlgebra k
        ((Fin n → k) ⧸ additiveRelationSubspace k I)) ∈ jointKernel k I ↔ x = 0 := by
  change mixedProjectionTensorBialgHom k I (x ⊗ₜ[k] 1) = 0 ↔ x = 0
  change MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom k I
    (x ⊗ₜ[k] 1) = 0 ↔ x = 0
  simp only [MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom_tmul, map_one, mul_one]
  simpa using
    ((torusRelationGroupAlgHomIntoSubgroupQuotient_injective k I).eq_iff :
      torusRelationGroupAlgHomIntoSubgroupQuotient k I x =
        torusRelationGroupAlgHomIntoSubgroupQuotient k I 0 ↔ x = 0)

variable [CharZero k]

/-- The residual mixed kernel contains no nonzero element supported purely on the additive factor. -/
theorem one_tmul_mem_jointKernel_iff
    (x : SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I)) :
    (1 : AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I)) ⊗ₜ[k] x ∈
      jointKernel k I ↔ x = 0 := by
  change mixedProjectionTensorBialgHom k I (1 ⊗ₜ[k] x) = 0 ↔ x = 0
  change MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom k I
    (1 ⊗ₜ[k] x) = 0 ↔ x = 0
  simp only [MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom_tmul, map_one, one_mul]
  simpa using
    ((additiveRelationSymmetricAlgHomIntoSubgroupQuotient_injective k I).eq_iff :
      additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I x =
        additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I 0 ↔ x = 0)

/-- A residual mixed relation with an invertible torus factor is zero. -/
theorem unit_tmul_mem_jointKernel_iff
    (a : AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I))
    (ha : IsUnit a)
    (x : SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I)) :
    a ⊗ₜ[k] x ∈ jointKernel k I ↔ x = 0 := by
  constructor
  · intro h
    change mixedProjectionTensorBialgHom k I
        (a ⊗ₜ[k] x) = 0 at h
    change MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom k I
        (a ⊗ₜ[k] x) = 0 at h
    rw [MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom_tmul] at h
    have hu : IsUnit (torusRelationGroupAlgHomIntoSubgroupQuotient k I a) :=
      ha.map
        (torusRelationGroupAlgHomIntoSubgroupQuotient k I).toMonoidHom
    have hadd : additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I x = 0 := by
      apply hu.mul_left_cancel
      exact h.trans (mul_zero _).symm
    apply additiveRelationSymmetricAlgHomIntoSubgroupQuotient_injective k I
    exact hadd.trans (map_zero _).symm
  · rintro rfl
    simp

omit [CharZero k] in
/-- A residual mixed relation with an invertible additive factor is zero. -/
theorem tmul_unit_mem_jointKernel_iff
    (x : AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I))
    (a : SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I))
    (ha : IsUnit a) :
    x ⊗ₜ[k] a ∈ jointKernel k I ↔ x = 0 := by
  constructor
  · intro h
    change mixedProjectionTensorBialgHom k I (x ⊗ₜ[k] a) = 0 at h
    change MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom k I
        (x ⊗ₜ[k] a) = 0 at h
    rw [MixedProjectionTensorPresentation.mixedProjectionTensorAlgHom_tmul] at h
    have hu : IsUnit (additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I a) :=
      ha.map (additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I).toMonoidHom
    have htorus : torusRelationGroupAlgHomIntoSubgroupQuotient k I x = 0 := by
      apply hu.mul_right_cancel
      exact h.trans (zero_mul _).symm
    apply torusRelationGroupAlgHomIntoSubgroupQuotient_injective k I
    exact htorus.trans (map_zero _).symm
  · rintro rfl
    simp

/-- A residual mixed relation cannot be supported on one torus weight.  Multiplication by that
weight is invertible, so such a relation would give a forbidden pure-additive relation. -/
theorem single_tmul_mem_jointKernel_iff
    (m : (Fin n →₀ ℤ) ⧸ torusRelationLattice k I)
    (x : SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I)) :
    AddMonoidAlgebra.single m (1 : k) ⊗ₜ[k] x ∈ jointKernel k I ↔ x = 0 :=
  unit_tmul_mem_jointKernel_iff k I _
    (AlgebraicGroupCrossHomFinite.groupMonomial_isUnit k m) x

/-- The group-graded residual kernel contains no nonzero homogeneous element. -/
theorem single_mem_groupGradedJointKernel_iff
    (m : (Fin n →₀ ℤ) ⧸ torusRelationLattice k I)
    (b : SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I)) :
    AddMonoidAlgebra.single m b ∈ groupGradedJointKernel k I ↔ b = 0 := by
  change groupGradedJointBialgHom k I (AddMonoidAlgebra.single m b) = 0 ↔ b = 0
  rw [groupGradedJointBialgHom_single]
  exact unit_tmul_mem_jointKernel_iff k I _
    (AlgebraicGroupCrossHomFinite.groupMonomial_isUnit k m) b

/-- Every nonzero group-graded residual relation has at least two homogeneous weights. -/
theorem two_le_card_support_of_mem_groupGradedJointKernel
    (z : GroupGradedMixedProjection k I)
    (hz : z ∈ groupGradedJointKernel k I)
    (hz0 : z ≠ 0) :
    2 ≤ z.coeff.support.card := by
  classical
  have hcard0 : z.coeff.support.card ≠ 0 := by
    intro hc
    have hs : z.coeff.support = ∅ := Finset.card_eq_zero.mp hc
    apply hz0
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro m
    have hm : m ∉ z.coeff.support := by simp [hs]
    simpa [Finsupp.mem_support_iff] using hm
  have hcard1 : z.coeff.support.card ≠ 1 := by
    intro hc
    obtain ⟨m, hs⟩ := Finset.card_eq_one.mp hc
    have hform : z = AddMonoidAlgebra.single m (z.coeff m) := by
      apply AddMonoidAlgebra.ext
      apply Finsupp.ext
      intro a
      by_cases ham : a = m
      · subst a
        simp
      · have ha : a ∉ z.coeff.support := by simp [hs, ham]
        have hcoeff : z.coeff a = 0 := by
          simpa [Finsupp.mem_support_iff] using ha
        simp [ham, hcoeff]
    have hz' := hz
    rw [hform] at hz'
    have hcoeff : z.coeff m = 0 :=
      (single_mem_groupGradedJointKernel_iff k I m _).1 hz'
    apply hz0
    rw [hform, hcoeff]
    simp
  omega

/-- The residual group-graded Hopf kernel contains no nonzero skew-primitive between any two
torus weights. -/
theorem eq_zero_of_mem_groupGradedJointKernel_of_skewPrimitive
    (p : GroupGradedMixedProjection k I)
    (a b : (Fin n →₀ ℤ) ⧸ torusRelationLattice k I)
    (hmem : p ∈ groupGradedJointKernel k I)
    (hskew : Coalgebra.comul (R := k) p =
      p ⊗ₜ[k] AddMonoidAlgebra.single a 1 +
        AddMonoidAlgebra.single b 1 ⊗ₜ[k] p) :
    p = 0 := by
  classical
  by_cases hab : a = b
  · subst b
    let basis := Module.Free.chooseBasis k
      ((Fin n → k) ⧸ additiveRelationSubspace k I)
    obtain ⟨v, rfl⟩ :=
      GroupGradedSkewPrimitive.sameWeight_skewPrimitive_group_symmetric_eq_single_generator
        basis p a hskew
    have hv : SymmetricAlgebra.ι k
        ((Fin n → k) ⧸ additiveRelationSubspace k I) v = 0 :=
      (single_mem_groupGradedJointKernel_iff k I a _).1 hmem
    rw [hv]
    simp
  · obtain ⟨c, hp⟩ :=
      GroupGradedSkewPrimitive.distinctWeight_skewPrimitive_eq_smul_sub
        p a b hab hskew
    have hker := hmem
    change groupGradedJointBialgHom k I p = 0 at hker
    rw [hp, map_smul, map_sub, groupGradedJointBialgHom_single,
      groupGradedJointBialgHom_single] at hker
    simp only [map_one, mul_one] at hker
    have htorus : torusFactorBialgHom k I
        (c • (AddMonoidAlgebra.single a (1 : k) -
          AddMonoidAlgebra.single b 1)) = 0 := by
      rw [map_smul, map_sub]
      change c •
          ((torusFactorBialgHom k I).toAlgHom
              (AddMonoidAlgebra.single a (1 : k)) -
            (torusFactorBialgHom k I).toAlgHom
              (AddMonoidAlgebra.single b (1 : k))) = 0
      rw [torusFactorBialgHom_toAlgHom]
      exact hker
    have htorus0 : c • (AddMonoidAlgebra.single a (1 : k) -
        AddMonoidAlgebra.single b 1) = 0 := by
      apply torusFactorBialgHom_injective k I
      exact htorus.trans (map_zero _).symm
    have hcoeff := congrArg
      (fun z : AddMonoidAlgebra k
          ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I) => z.coeff a) htorus0
    have hc : c = 0 := by simpa [hab] using hcoeff
    rw [hp, hc]
    simp

/-- Every nonzero residual mixed relation involves at least two distinct torus weights. -/
theorem two_le_card_torusSupport_of_mem_jointKernel
    (z : MixedProjectionTensor k I)
    (hz : z ∈ jointKernel k I)
    (hz0 : z ≠ 0) :
    2 ≤ (torusSupport k I z).card := by
  classical
  have hcard0 : (torusSupport k I z).card ≠ 0 := by
    intro hc
    have hs : torusSupport k I z = ∅ := Finset.card_eq_zero.mp hc
    apply hz0
    apply (eq_zero_iff_torusCoefficientEquiv_apply k I z).2
    intro m
    have hm : m ∉ torusSupport k I z := by simp [hs]
    simpa [torusSupport, Finsupp.mem_support_iff] using hm
  have hcard1 : (torusSupport k I z).card ≠ 1 := by
    intro hc
    obtain ⟨m, hs⟩ := Finset.card_eq_one.mp hc
    have hform := eq_single_tmul_of_torusSupport_eq_singleton k I z m hs
    have hz' := hz
    rw [hform] at hz'
    have hcoeff : torusCoefficientEquiv k I z m = 0 :=
      (single_tmul_mem_jointKernel_iff k I m _).1 hz'
    apply hz0
    rw [hform, hcoeff]
    simp
  omega

end
end MixedProjectionTensorKernel
end GaloisForLFunctions.HTGeometry
