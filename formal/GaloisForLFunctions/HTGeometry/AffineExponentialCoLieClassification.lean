import GaloisForLFunctions.HTGeometry.MixedProjectionTensorKernelVanishing
import GaloisForLFunctions.HTGeometry.CoLieProduct
import GaloisForLFunctions.HTGeometry.TorusCharacterCoLie
import GaloisForLFunctions.HTGeometry.SymmetricAlgebraCoLie

/-!
# Co-Lie classification for mixed affine-exponential subgroup quotients

For a Hopf ideal in the coordinate algebra of `Gₘⁿ × Gₐⁿ`, the kernel of the induced map on
co-Lie modules is classified exactly.  A mixed logarithmic/additive tangent vector vanishes in the
subgroup quotient precisely when its torus component lies in the field-linear span of the integral
character relations and its additive component lies in the additive relation subspace.

The proof reuses the exact tensor presentation of the subgroup quotient, the independent torus and
additive co-Lie classifications, and the already-proved vanishing of the mixed tensor kernel.  No
connectedness or saturation hypothesis is required.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialCoLieClassification

noncomputable section

open AffineExponentialGroup AffineGroupScheme
open AffineExponentialProjectionClassification
open MixedAdditiveProjectionClassification
open MixedProjectionTensorBialgebra MixedProjectionTensorKernelVanishing
open MixedProjectionTensorKernel
open TorusCharacterCoLie SymmetricAlgebraCoLie

variable (k : Type*) [Field k] [CharZero k]
variable {n : ℕ} (I : Ideal (CoordinateAlgebra k n)) [I.IsHopfIdeal k]

@[reducible] def coordinateDefaultCommRing :
    CommRing (CoordinateAlgebra k n) := inferInstance

local instance coordinateRing : Ring (CoordinateAlgebra k n) :=
  { (coordinateDefaultCommRing k (n := n)).toRing with
    toSemiring := inferInstance }

local instance coordinateCommRing : CommRing (CoordinateAlgebra k n) :=
  CommRing.mk (coordinateDefaultCommRing k (n := n)).mul_comm

local instance mixedQuotientCoideal :
    (I.restrictScalars k).IsCoideal := Ideal.IsHopfIdeal.toIsCoideal

local instance mixedQuotientHopfAlgebra :
    HopfAlgebra k (CoordinateAlgebra k n ⧸ I) := by infer_instance

abbrev TorusQuotient := AddMonoidAlgebra k
  ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I)

abbrev AdditiveQuotient := SymmetricAlgebra k
  ((Fin n → k) ⧸ additiveRelationSubspace k I)

local instance mixedProjectionTensorRing :
    Ring (TorusQuotient k I ⊗[k] AdditiveQuotient k I) :=
  { (mixedProjectionTensorDefaultCommRing k I).toRing with
    toSemiring := inferInstance }

local instance mixedProjectionTensorCommRing :
    CommRing (TorusQuotient k I ⊗[k] AdditiveQuotient k I) :=
  CommRing.mk (mixedProjectionTensorDefaultCommRing k I).mul_comm

local instance mixedProjectionTargetRing : Ring (CoordinateAlgebra k n ⧸ I) :=
  { (mixedProjectionTargetDefaultCommRing k I).toRing with
    toSemiring := inferInstance }

local instance mixedProjectionTargetCommRing : CommRing (CoordinateAlgebra k n ⧸ I) :=
  CommRing.mk (mixedProjectionTargetDefaultCommRing k I).mul_comm

noncomputable def alignedMixedProjectionBialgHom :
    CoordinateAlgebra k n →ₐc[k]
      TorusQuotient k I ⊗[k] AdditiveQuotient k I :=
  mixedProjectionTensorQuotientBialgHom k I

noncomputable def alignedMixedPresentationBialgHom :
    TorusQuotient k I ⊗[k] AdditiveQuotient k I →ₐc[k]
      CoordinateAlgebra k n ⧸ I :=
  mixedProjectionTensorBialgHom k I

noncomputable def alignedSubgroupQuotientBialgHom :
    CoordinateAlgebra k n →ₐc[k] CoordinateAlgebra k n ⧸ I :=
  Bialgebra.Quotient.mkBialgHom (R := k) I

theorem alignedMixedPresentationBialgHom_bijective :
    Function.Bijective (alignedMixedPresentationBialgHom k I) :=
  mixedProjectionTensorBialgHom_bijective k I

noncomputable def alignedMixedPresentationBialgEquiv :
    TorusQuotient k I ⊗[k] AdditiveQuotient k I ≃ₐc[k]
      CoordinateAlgebra k n ⧸ I :=
  BialgEquiv.ofBijective
    (R := k) (A := TorusQuotient k I ⊗[k] AdditiveQuotient k I)
    (B := CoordinateAlgebra k n ⧸ I)
    (alignedMixedPresentationBialgHom k I)
    (alignedMixedPresentationBialgHom_bijective k I)

noncomputable def alignedMixedPresentationInverseBialgHom :
    CoordinateAlgebra k n ⧸ I →ₐc[k]
      TorusQuotient k I ⊗[k] AdditiveQuotient k I :=
  (alignedMixedPresentationBialgEquiv k I).symm.toBialgHom

noncomputable def mixedProjectionCoLieMap :
    coLie k (CoordinateAlgebra k n) →ₗ[k]
      coLie k (TorusQuotient k I ⊗[k] AdditiveQuotient k I) :=
  coLieMap (alignedMixedProjectionBialgHom k I)

noncomputable def mixedPresentationCoLieMap :
    coLie k (TorusQuotient k I ⊗[k] AdditiveQuotient k I) →ₗ[k]
      coLie k (CoordinateAlgebra k n ⧸ I) :=
  coLieMap (alignedMixedPresentationBialgHom k I)

noncomputable def subgroupQuotientCoLieMap :
    coLie k (CoordinateAlgebra k n) →ₗ[k]
      coLie k (CoordinateAlgebra k n ⧸ I) :=
  coLieMap (alignedSubgroupQuotientBialgHom k I)

noncomputable def mixedPresentationInverseCoLieMap :
    coLie k (CoordinateAlgebra k n ⧸ I) →ₗ[k]
      coLie k (TorusQuotient k I ⊗[k] AdditiveQuotient k I) :=
  coLieMap (alignedMixedPresentationInverseBialgHom k I)

theorem alignedMixedPresentationCoLie_leftInverse
    (z : coLie k (TorusQuotient k I ⊗[k] AdditiveQuotient k I)) :
    mixedPresentationInverseCoLieMap k I
        (mixedPresentationCoLieMap k I z) = z := by
  have hcomp :
      (alignedMixedPresentationInverseBialgHom k I).comp
          (alignedMixedPresentationBialgHom k I) =
        BialgHom.id k (TorusQuotient k I ⊗[k] AdditiveQuotient k I) := by
    apply BialgHom.ext
    intro x
    change (alignedMixedPresentationBialgEquiv k I).symm
      ((alignedMixedPresentationBialgEquiv k I) x) = x
    exact (alignedMixedPresentationBialgEquiv k I).symm_apply_apply x
  change coLieMap (alignedMixedPresentationInverseBialgHom k I)
      (coLieMap (alignedMixedPresentationBialgHom k I) z) = z
  change ((coLieMap (alignedMixedPresentationInverseBialgHom k I)).comp
      (coLieMap (alignedMixedPresentationBialgHom k I))) z = z
  rw [← coLieMap_comp, hcomp, coLieMap_id, LinearMap.id_apply]

/-- Mixed logarithmic/additive co-Lie vector in the ambient coordinate algebra. -/
noncomputable def mixedCoLieVector (tor add : Fin n → k) :
    coLie k (CoordinateAlgebra k n) :=
  (∑ i, tor i • d k (CoordinateAlgebra k n)
      (torusCharacter k (Finsupp.single i 1))) +
    ∑ i, add i • d k (CoordinateAlgebra k n) (additiveCoordinate k i)

omit [CharZero k] in
theorem coLieMap_mixedProjection_torus (i : Fin n) :
    coLieMap (mixedProjectionTensorQuotientBialgHom k I)
        (d k (CoordinateAlgebra k n)
          (torusCharacter k (Finsupp.single i 1))) =
      coLieInl k (TorusQuotient k I) (AdditiveQuotient k I)
        (d k (TorusQuotient k I)
          (AddMonoidAlgebra.single
            (QuotientAddGroup.mk' (torusRelationLattice k I)
              (Finsupp.single i 1)) 1)) := by
  rw [coLieMap_d, coLieInl_d]
  congr 1
  rw [show torusCharacter k (Finsupp.single i 1) =
      AddMonoidAlgebra.single (Finsupp.single i 1) 1 ⊗ₜ[k] 1 by
    rfl]
  rw [mixedProjectionTensorQuotientBialgHom_tmul]
  congr 1
  change AddMonoidAlgebra.mapDomain
      (QuotientAddGroup.mk' (torusRelationLattice k I))
        (AddMonoidAlgebra.single (Finsupp.single i 1) 1) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  exact map_one _

omit [CharZero k] in
theorem coLieMap_mixedProjection_additive (i : Fin n) :
    coLieMap (mixedProjectionTensorQuotientBialgHom k I)
        (d k (CoordinateAlgebra k n) (additiveCoordinate k i)) =
      coLieInr k (TorusQuotient k I) (AdditiveQuotient k I)
        (d k (AdditiveQuotient k I)
          (SymmetricAlgebra.ι k
            ((Fin n → k) ⧸ additiveRelationSubspace k I)
            (Submodule.Quotient.mk (additiveBasisVector k i)))) := by
  rw [coLieMap_d, coLieInr_d]
  congr 1
  simp [additiveCoordinate, mixedProjectionTensorQuotientBialgHom,
    torusRelationQuotientBialgHom,
    SymmetricAlgebraSubmoduleQuotient.quotientBialgHom,
    SymmetricAlgebraSubmoduleQuotient.quotientMap]

omit [CharZero k] in
@[simp] theorem coLieFst_coLieInl (x : coLie k (TorusQuotient k I)) :
    coLieFst k (TorusQuotient k I) (AdditiveQuotient k I)
        (coLieInl k (TorusQuotient k I) (AdditiveQuotient k I) x) = x := by
  have h := LinearMap.congr_fun
    (coLieFst_comp_coLieInl (R := k) (A := TorusQuotient k I)
      (B := AdditiveQuotient k I)) x
  simpa using h

omit [CharZero k] in
@[simp] theorem coLieSnd_coLieInl (x : coLie k (TorusQuotient k I)) :
    coLieSnd k (TorusQuotient k I) (AdditiveQuotient k I)
        (coLieInl k (TorusQuotient k I) (AdditiveQuotient k I) x) = 0 := by
  have h := LinearMap.congr_fun
    (coLieSnd_comp_coLieInl (R := k) (A := TorusQuotient k I)
      (B := AdditiveQuotient k I)) x
  simpa using h

omit [CharZero k] in
@[simp] theorem coLieFst_coLieInr (x : coLie k (AdditiveQuotient k I)) :
    coLieFst k (TorusQuotient k I) (AdditiveQuotient k I)
        (coLieInr k (TorusQuotient k I) (AdditiveQuotient k I) x) = 0 := by
  have h := LinearMap.congr_fun
    (coLieFst_comp_coLieInr (R := k) (A := TorusQuotient k I)
      (B := AdditiveQuotient k I)) x
  simpa using h

omit [CharZero k] in
@[simp] theorem coLieSnd_coLieInr (x : coLie k (AdditiveQuotient k I)) :
    coLieSnd k (TorusQuotient k I) (AdditiveQuotient k I)
        (coLieInr k (TorusQuotient k I) (AdditiveQuotient k I) x) = x := by
  have h := LinearMap.congr_fun
    (coLieSnd_comp_coLieInr (R := k) (A := TorusQuotient k I)
      (B := AdditiveQuotient k I)) x
  simpa using h

omit [CharZero k] in
theorem coLieProdEquiv_mixedProjection (tor add : Fin n → k) :
    coLieProdEquiv
        (mixedProjectionCoLieMap k I (mixedCoLieVector k tor add)) =
      (quotientGroupCoLieMap k (torusRelationLattice k I) tor,
        generatorCoLieMap
          (Submodule.Quotient.mk (p := additiveRelationSubspace k I) add)) := by
  rw [mixedProjectionCoLieMap, alignedMixedProjectionBialgHom,
    mixedCoLieVector, map_add, map_sum, map_sum]
  simp_rw [map_smul, coLieMap_mixedProjection_torus,
    coLieMap_mixedProjection_additive]
  apply Prod.ext
  · simp [coLieFst_coLieInl, coLieFst_coLieInr, quotientGroupCoLieMap_apply]
  · simp [coLieSnd_coLieInl, coLieSnd_coLieInr]
    change (∑ i, add i • generatorCoLieMap
        (k := k) (V := (Fin n → k) ⧸ additiveRelationSubspace k I)
        (Submodule.Quotient.mk (p := additiveRelationSubspace k I)
          (additiveBasisVector k i))) =
      generatorCoLieMap (k := k)
        (V := (Fin n → k) ⧸ additiveRelationSubspace k I)
        (Submodule.Quotient.mk (p := additiveRelationSubspace k I) add)
    have hcoords : add = ∑ i, add i • additiveBasisVector k i := by
      classical
      funext j
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single j (fun i _ hij => by
        change add i * additiveBasisVector k i j = 0
        rw [show additiveBasisVector k i j = 0 by
          simp [additiveBasisVector, Pi.single_eq_of_ne (Ne.symm hij)], mul_zero])
        (fun hmem => absurd (Finset.mem_univ j) hmem)]
      change add j = add j * additiveBasisVector k j j
      rw [show additiveBasisVector k j j = 1 by simp [additiveBasisVector], mul_one]
    have hmap := congrArg
      ((generatorCoLieMap (k := k)
          (V := (Fin n → k) ⧸ additiveRelationSubspace k I)).comp
        (Submodule.mkQ (additiveRelationSubspace k I))) hcoords
    convert hmap.symm using 1 <;>
      simp only [LinearMap.comp_apply, map_sum, map_smul] <;> rfl

/- Exact kernel of the factorwise mixed projection on logarithmic/additive directions. -/
omit [CharZero k] in
theorem coLieMap_mixedProjection_eq_zero_iff (tor add : Fin n → k) :
    mixedProjectionCoLieMap k I (mixedCoLieVector k tor add) = 0 ↔
      tor ∈ latticeSpan k (torusRelationLattice k I) ∧
        add ∈ additiveRelationSubspace k I := by
  constructor
  · intro h
    have hp := congrArg coLieProdEquiv h
    rw [coLieProdEquiv_mixedProjection] at hp
    simp only [map_zero] at hp
    have ht : quotientGroupCoLieMap k (torusRelationLattice k I) tor = 0 :=
      congrArg Prod.fst hp
    have ha : generatorCoLieMap
        (k := k) (V := (Fin n → k) ⧸ additiveRelationSubspace k I)
        (Submodule.Quotient.mk (p := additiveRelationSubspace k I) add) = 0 :=
      congrArg Prod.snd hp
    constructor
    · exact (quotientGroupCoLieMap_eq_zero_iff k _ tor).mp ht
    · rw [← Submodule.Quotient.mk_eq_zero]
      apply generatorCoLieMap_injective (k := k)
        (V := (Fin n → k) ⧸ additiveRelationSubspace k I)
      simpa using ha
  · rintro ⟨ht, ha⟩
    apply coLieProdEquiv.injective
    rw [coLieProdEquiv_mixedProjection]
    rw [(quotientGroupCoLieMap_eq_zero_iff k _ tor).mpr ht]
    have haq : Submodule.Quotient.mk (p := additiveRelationSubspace k I) add = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ha
    rw [haq, map_zero]
    rfl

/- Exact invariant-differential kernel for an arbitrary mixed affine-exponential Hopf quotient. -/
set_option maxHeartbeats 800000 in
theorem coLieMap_subgroupQuotient_eq_zero_iff (tor add : Fin n → k) :
    subgroupQuotientCoLieMap k I (mixedCoLieVector k tor add) = 0 ↔
      tor ∈ latticeSpan k (torusRelationLattice k I) ∧
        add ∈ additiveRelationSubspace k I := by
  have hbialg :
      (alignedMixedPresentationBialgHom k I).comp
          (alignedMixedProjectionBialgHom k I) =
        alignedSubgroupQuotientBialgHom k I := by
    apply BialgHom.ext
    intro x
    exact DFunLike.congr_fun
      (mixedProjectionTensorAlgHom_comp_quotientBialgHom k I) x
  have hcomp :
      (mixedPresentationCoLieMap k I).comp (mixedProjectionCoLieMap k I) =
        subgroupQuotientCoLieMap k I := by
    refine coLie_hom_ext fun a => ?_
    rw [LinearMap.comp_apply, mixedProjectionCoLieMap, mixedPresentationCoLieMap,
      subgroupQuotientCoLieMap, coLieMap_d, coLieMap_d, coLieMap_d]
    congr 1
    exact DFunLike.congr_fun hbialg a
  rw [← hcomp]
  constructor
  · intro h
    have hzero : mixedProjectionCoLieMap k I
        (mixedCoLieVector k tor add) = 0 := by
      have h' := congrArg (mixedPresentationInverseCoLieMap k I) h
      rw [LinearMap.comp_apply, alignedMixedPresentationCoLie_leftInverse, map_zero] at h'
      exact h'
    exact (coLieMap_mixedProjection_eq_zero_iff k I tor add).mp hzero
  · intro h
    rw [LinearMap.comp_apply,
      (coLieMap_mixedProjection_eq_zero_iff k I tor add).mpr h]
    simp

end
end AffineExponentialCoLieClassification
end GaloisForLFunctions.HTGeometry
