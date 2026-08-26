import GaloisForLFunctions.HTGeometry.MixedProjectionTensorKernel
import GaloisForLFunctions.HTGeometry.GroupGradedBialgKernelDegreeOne
import GaloisForLFunctions.HTGeometry.GroupGradedSymmetricAffine

/-!
# Vanishing of the residual mixed projection kernel

The classified torus and additive projection factors are linearly disjoint in the mixed Hopf
quotient.  Higher additive degrees descend to degree one by coalgebra slicing.  Degree zero is
pure torus.  At degree one, a torus-weight slice isolates one affine coefficient; its nonconstant
part lies simultaneously in the torus and additive factor images, whose intersection is scalar.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace MixedProjectionTensorKernelVanishing

noncomputable section

open AffineExponentialGroup AffineExponentialProjectionImages
open AffineExponentialProjectionClassification
open MixedTorusProjectionSaturation MixedAdditiveProjectionClassification
open MixedProjectionTensorBialgebra MixedProjectionTensorKernel
open GroupGradedSymmetricDegree GroupGradedSymmetricCoalgebraFiltration
open GroupGradedSymmetricAffine GroupGradedBialgKernelDegreeOne

variable (k : Type*) [Field k] [CharZero k]
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

local instance mixedProjectionTargetRing : Ring (CoordinateAlgebra k n ⧸ I) :=
  { (mixedProjectionTargetDefaultCommRing k I).toRing with
    toSemiring := inferInstance }

local instance mixedProjectionTargetCommRing : CommRing (CoordinateAlgebra k n ⧸ I) :=
  CommRing.mk (mixedProjectionTargetDefaultCommRing k I).mul_comm

abbrev TorusRelationGroup :=
  (Fin n →₀ ℤ) ⧸ torusRelationLattice k I

abbrev AdditiveRelationSpace :=
  (Fin n → k) ⧸ additiveRelationSubspace k I

omit [CharZero k] in
/-- The group-graded joint map sends an embedded scalar group algebra through the torus factor. -/
theorem groupGradedJointBialgHom_scalarEmbedding
    (a : AddMonoidAlgebra k (TorusRelationGroup k I)) :
    groupGradedJointBialgHom k I
        (scalarEmbedding (V := AdditiveRelationSpace k I) a) =
      torusFactorBialgHom k I a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb
  | single m c =>
      rw [scalarEmbedding_single, groupGradedJointBialgHom_single]
      change torusRelationGroupAlgHomIntoSubgroupQuotient k I
            (AddMonoidAlgebra.single m (1 : k)) *
          additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I
            (algebraMap k (SymmetricAlgebra k (AdditiveRelationSpace k I)) c) =
        torusFactorBialgHom k I (AddMonoidAlgebra.single m c)
      rw [(additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I).commutes]
      rw [← torusFactorBialgHom_toAlgHom]
      rw [show AddMonoidAlgebra.single m c =
          c • AddMonoidAlgebra.single m (1 : k) by simp, map_smul]
      rw [mul_comm]
      exact (Algebra.smul_def c _).symm

omit [CharZero k] in
/-- Homogeneous evaluation is multiplication of the classified torus and additive factors. -/
theorem groupGradedJointBialgHom_single_eq_factor_mul
    (m : TorusRelationGroup k I)
    (b : SymmetricAlgebra k (AdditiveRelationSpace k I)) :
    groupGradedJointBialgHom k I (AddMonoidAlgebra.single m b) =
      torusFactorBialgHom k I (AddMonoidAlgebra.single m (1 : k)) *
        additiveFactorBialgHom k I b := by
  rw [groupGradedJointBialgHom_single]
  rw [← torusFactorBialgHom_toAlgHom, ← additiveFactorBialgHom_toAlgHom]
  rfl

omit [CharZero k] in
/-- The joint map has no nonzero additive-degree-zero kernel element. -/
theorem eq_zero_of_groupGradedJointBialgHom_eq_zero_of_additiveDegree_eq_zero
    (basis : Module.Basis ι k (AdditiveRelationSpace k I))
    {p : GroupGradedMixedProjection k I}
    (hp : groupGradedJointBialgHom k I p = 0)
    (hpdeg : additiveDegree basis p = 0) : p = 0 := by
  rw [eq_scalarEmbedding_scalarPart_of_additiveDegree_eq_zero basis hpdeg] at hp
  rw [groupGradedJointBialgHom_scalarEmbedding] at hp
  have hscalar : scalarPart basis p = 0 := by
    apply torusFactorBialgHom_injective k I
    exact hp.trans (map_zero _).symm
  rw [eq_scalarEmbedding_scalarPart_of_additiveDegree_eq_zero basis hpdeg,
    hscalar, map_zero]

set_option maxHeartbeats 1000000 in
/-- The classified group-graded joint presentation is injective. -/
theorem groupGradedJointBialgHom_injective :
    Function.Injective (groupGradedJointBialgHom k I) := by
  classical
  let basis := Module.Free.chooseBasis k (AdditiveRelationSpace k I)
  by_contra hInjective
  let f : GroupGradedMixedProjection k I →ₐc[k]
      (CoordinateAlgebra k n ⧸ I) := groupGradedJointBialgHom k I
  have hf : ¬ Function.Injective f := by
    simpa [f] using hInjective
  obtain ⟨p, hpker, hp0, hpdeg⟩ :=
    exists_nonzero_ker_additiveDegree_le_one
      (k := k) (V := AdditiveRelationSpace k I)
      (M := TorusRelationGroup k I) (H := CoordinateAlgebra k n ⧸ I)
      basis f hf
  change groupGradedJointBialgHom k I p = 0 at hpker
  by_cases hdegreeZero : additiveDegree basis p = 0
  · exact hp0
      (eq_zero_of_groupGradedJointBialgHom_eq_zero_of_additiveDegree_eq_zero
        k I basis hpker hdegreeZero)
  · have hpdegOne : additiveDegree basis p = 1 := by omega
    have hinjZero : Function.Injective
        ((groupGradedJointBialgHom k I).toLinearMap.domRestrict
          (degreeLE basis 0)) := by
      intro x y hxy
      apply Subtype.ext
      by_contra hval
      have hdiff0 : (x.1 - y.1 : GroupGradedMixedProjection k I) ≠ 0 :=
        sub_ne_zero.mpr hval
      have hdiffker : groupGradedJointBialgHom k I (x.1 - y.1) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact hxy
      have hdiffdegLe : additiveDegree basis (x.1 - y.1) ≤ 0 :=
        (degreeLE basis 0).sub_mem x.2 y.2
      have hdiffdeg : additiveDegree basis (x.1 - y.1) = 0 :=
        Nat.eq_zero_of_le_zero hdiffdegLe
      exact hdiff0
        (eq_zero_of_groupGradedJointBialgHom_eq_zero_of_additiveDegree_eq_zero
          k I basis hdiffker hdiffdeg)
    let fZero : (degreeLE basis 0) →ₗ[k] (CoordinateAlgebra k n ⧸ I) :=
      (groupGradedJointBialgHom k I).toLinearMap.domRestrict (degreeLE basis 0)
    have hinjZero' : Function.Injective fZero := by
      simpa [fZero] using hinjZero
    have hfZeroKer : fZero.ker = ⊥ := by
      ext x
      constructor
      · intro hx
        change fZero x = 0 at hx
        have hx0 : x = 0 := hinjZero' (hx.trans (map_zero fZero).symm)
        simp [hx0]
      · intro hx
        change x = 0 at hx
        subst x
        simp
    obtain ⟨l, hl⟩ := @LinearMap.exists_leftInverse_of_injective
      k (degreeLE basis 0) (CoordinateAlgebra k n ⧸ I)
        inferInstance inferInstance inferInstance inferInstance inferInstance
        fZero hfZeroKer
    obtain ⟨m, hm, hmdeg⟩ := exists_weight_additiveDegree_eq basis hp0
    let χ := weightCounit
      (k := k) (V := AdditiveRelationSpace k I) m
    let χZero : (degreeLE basis 0) →ₗ[k] k :=
      χ.comp (degreeLE basis 0).subtype
    let φ : (CoordinateAlgebra k n ⧸ I) →ₗ[k] k := χZero.comp l
    let ψ : GroupGradedMixedProjection k I →ₗ[k] k :=
      φ.comp (groupGradedJointBialgHom k I).toLinearMap
    have hagree (x : GroupGradedMixedProjection k I)
        (hx : x ∈ degreeLE basis 0) : ψ x = χ x := by
      have hlx := DFunLike.congr_fun hl (⟨x, hx⟩ : degreeLE basis 0)
      have hlx' : l ((groupGradedJointBialgHom k I).toLinearMap x) =
          (⟨x, hx⟩ : degreeLE basis 0) := by
        simpa [fZero] using hlx
      change χ ((l ((groupGradedJointBialgHom k I).toLinearMap x) :
        degreeLE basis 0).1) = χ x
      rw [hlx']
    have hgroup : ∀ a : TorusRelationGroup k I,
        ψ (AddMonoidAlgebra.single a
            (1 : SymmetricAlgebra k (AdditiveRelationSpace k I))) =
          χ (AddMonoidAlgebra.single a 1) := by
      intro a
      exact hagree _ (single_one_mem_degreeLE basis a)
    let q := rightSlice ψ (Coalgebra.comul (R := k) p)
    let r := rightSlice χ (Coalgebra.comul (R := k) p)
    let e := q - r
    have hqker : groupGradedJointBialgHom k I q = 0 := by
      change groupGradedJointBialgHom k I
        (rightSlice (φ.comp (groupGradedJointBialgHom k I).toLinearMap)
          (Coalgebra.comul (R := k) p)) = 0
      change (groupGradedJointBialgHom k I).toLinearMap
        (rightSlice (φ.comp (groupGradedJointBialgHom k I).toLinearMap)
          (Coalgebra.comul (R := k) p)) = 0
      rw [← rightSlice_map (groupGradedJointBialgHom k I).toLinearMap φ]
      have hmap := DFunLike.congr_fun
        (BialgHom.map_comp_comulAlgHom (groupGradedJointBialgHom k I)) p
      change TensorProduct.map (groupGradedJointBialgHom k I).toLinearMap
          (groupGradedJointBialgHom k I).toLinearMap
          (Coalgebra.comul (R := k) p) =
        Coalgebra.comul (R := k) (groupGradedJointBialgHom k I p) at hmap
      rw [hmap, hpker, map_zero]
      simp [rightSlice]
    have hr : r = AddMonoidAlgebra.single m (p.coeff m) := by
      exact rightSlice_weightCounit_comul p m
    have hedeg : additiveDegree basis e = 0 := by
      by_cases he0 : e = 0
      · rw [he0, additiveDegree_zero]
      · have hedrop := additiveDegree_sub_rightSlice_comul_lt_of_groupLike_eq
          basis ψ χ hgroup p (by simpa [e, q, r] using he0)
        change additiveDegree basis e < additiveDegree basis p at hedrop
        omega
    have heform : e = scalarEmbedding
        (V := AdditiveRelationSpace k I) (scalarPart basis e) :=
      eq_scalarEmbedding_scalarPart_of_additiveDegree_eq_zero basis hedeg
    have hpcoeffDeg : (SymmetricAlgebra.equivMvPolynomial basis
        (p.coeff m)).totalDegree ≤ 1 := by
      exact (coefficientPolynomial_totalDegree_le basis p m).trans hpdeg
    obtain ⟨v, hv⟩ := exists_eq_algebraMap_constant_add_ι_of_totalDegree_le_one
      basis (p.coeff m) hpcoeffDeg
    let c := symmetricConstantCoefficient basis (p.coeff m)
    let a : AddMonoidAlgebra k (TorusRelationGroup k I) :=
      AddMonoidAlgebra.single m c + scalarPart basis e
    have hqform : q = scalarEmbedding (V := AdditiveRelationSpace k I) a +
        AddMonoidAlgebra.single m (SymmetricAlgebra.ι k (AdditiveRelationSpace k I) v) := by
      have hqeq : q = r + e := by simp [e]
      rw [hqeq, hr, hv, AddMonoidAlgebra.single_add, heform]
      have ha : scalarEmbedding (V := AdditiveRelationSpace k I) a =
          AddMonoidAlgebra.single m
              (algebraMap k (SymmetricAlgebra k (AdditiveRelationSpace k I)) c) +
            scalarEmbedding (V := AdditiveRelationSpace k I) (scalarPart basis e) := by
        change scalarEmbedding (V := AdditiveRelationSpace k I)
            (AddMonoidAlgebra.single m c + scalarPart basis e) = _
        rw [map_add, scalarEmbedding_single]
      rw [ha]
      abel
    have hrelation :
        torusFactorBialgHom k I a +
          torusFactorBialgHom k I (AddMonoidAlgebra.single m (1 : k)) *
            additiveFactorBialgHom k I
              (SymmetricAlgebra.ι k (AdditiveRelationSpace k I) v) = 0 := by
      rw [← groupGradedJointBialgHom_scalarEmbedding k I a,
        ← groupGradedJointBialgHom_single_eq_factor_mul k I]
      rw [← map_add, ← hqform]
      exact hqker
    let tm : CoordinateAlgebra k n ⧸ I :=
      torusFactorBialgHom k I (AddMonoidAlgebra.single m (1 : k))
    let av : CoordinateAlgebra k n ⧸ I := additiveFactorBialgHom k I
      (SymmetricAlgebra.ι k (AdditiveRelationSpace k I) v)
    have hrelation' : torusFactorBialgHom k I a + tm * av = 0 := by
      change torusFactorBialgHom k I a +
          torusFactorBialgHom k I (AddMonoidAlgebra.single m (1 : k)) *
            additiveFactorBialgHom k I
              (SymmetricAlgebra.ι k (AdditiveRelationSpace k I) v) = 0
      exact hrelation
    let b : AddMonoidAlgebra k (TorusRelationGroup k I) :=
      AddMonoidAlgebra.single (-m) (1 : k) * a
    let tmInv : CoordinateAlgebra k n ⧸ I :=
      torusFactorBialgHom k I (AddMonoidAlgebra.single (-m) (1 : k))
    have hmonomial : AddMonoidAlgebra.single (-m) (1 : k) *
        AddMonoidAlgebra.single m (1 : k) =
          (1 : AddMonoidAlgebra k (TorusRelationGroup k I)) := by
      simp [AddMonoidAlgebra.one_def]
    have hunit : tmInv * tm = 1 := by
      calc
        tmInv * tm =
            torusFactorBialgHom k I (AddMonoidAlgebra.single (-m) (1 : k)) *
              torusFactorBialgHom k I (AddMonoidAlgebra.single m (1 : k)) := rfl
        _ = torusFactorBialgHom k I
              (AddMonoidAlgebra.single (-m) (1 : k) *
                AddMonoidAlgebra.single m (1 : k)) :=
          ((torusFactorBialgHom k I).map_mul _ _).symm
        _ = torusFactorBialgHom k I 1 := congrArg
          (fun x : AddMonoidAlgebra k (TorusRelationGroup k I) =>
            torusFactorBialgHom k I x) hmonomial
        _ = 1 := (torusFactorBialgHom k I).map_one
    have hmapb : torusFactorBialgHom k I b =
        tmInv * torusFactorBialgHom k I a := by
      calc
        torusFactorBialgHom k I b = torusFactorBialgHom k I
            (AddMonoidAlgebra.single (-m) (1 : k) * a) := rfl
        _ = torusFactorBialgHom k I (AddMonoidAlgebra.single (-m) (1 : k)) *
              torusFactorBialgHom k I a := (torusFactorBialgHom k I).map_mul _ _
        _ = tmInv * torusFactorBialgHom k I a := rfl
    have hleftZero : torusFactorBialgHom k I b + av = 0 := by
      calc
        torusFactorBialgHom k I b + av =
            tmInv * torusFactorBialgHom k I a + av := by rw [hmapb]
        _ = tmInv * torusFactorBialgHom k I a + (tmInv * tm) * av := by
          rw [hunit, one_mul]
        _ = tmInv * (torusFactorBialgHom k I a + tm * av) := by
          rw [mul_add, mul_assoc]
        _ = tmInv * 0 := by rw [hrelation']
        _ = 0 := mul_zero _
    have hrightZero : additiveFactorBialgHom k I
          (-SymmetricAlgebra.ι k (AdditiveRelationSpace k I) v) + av = 0 := by
      change additiveFactorBialgHom k I
            (-SymmetricAlgebra.ι k (AdditiveRelationSpace k I) v) +
          additiveFactorBialgHom k I
            (SymmetricAlgebra.ι k (AdditiveRelationSpace k I) v) = 0
      rw [← map_add]
      simp
    have hintersection : torusFactorBialgHom k I b =
        additiveFactorBialgHom k I
          (-SymmetricAlgebra.ι k (AdditiveRelationSpace k I) v) := by
      apply add_right_cancel (b := av)
      exact hleftZero.trans hrightZero.symm
    obtain ⟨d, _, hvscalar⟩ := factor_images_intersection_eq_scalars
      k I b (-SymmetricAlgebra.ι k (AdditiveRelationSpace k I) v) hintersection
    have hvscalar' : SymmetricAlgebra.ι k (AdditiveRelationSpace k I) v =
        algebraMap k (SymmetricAlgebra k (AdditiveRelationSpace k I)) (-d) := by
      calc
        SymmetricAlgebra.ι k (AdditiveRelationSpace k I) v =
            -(-SymmetricAlgebra.ι k (AdditiveRelationSpace k I) v) := by simp
        _ = -algebraMap k (SymmetricAlgebra k (AdditiveRelationSpace k I)) d := by
          rw [hvscalar]
        _ = algebraMap k (SymmetricAlgebra k (AdditiveRelationSpace k I)) (-d) := by
          rw [map_neg]
    have hpcoeffScalar : p.coeff m =
        algebraMap k (SymmetricAlgebra k (AdditiveRelationSpace k I)) (c + (-d)) := by
      rw [hv, hvscalar', ← map_add]
    have hdegreeZero : (coefficientPolynomial basis p m).totalDegree = 0 := by
      rw [coefficientPolynomial, hpcoeffScalar]
      have hequiv : SymmetricAlgebra.equivMvPolynomial basis
          (algebraMap k (SymmetricAlgebra k (AdditiveRelationSpace k I)) (c + -d)) =
            MvPolynomial.C (c + -d) := by simp
      rw [hequiv]
      exact MvPolynomial.totalDegree_C (c + -d)
    rw [hdegreeZero, hpdegOne] at hmdeg
    omega

/-- The classified tensor presentation is injective. -/
theorem mixedProjectionTensorBialgHom_injective :
    Function.Injective (mixedProjectionTensorBialgHom k I) := by
  intro x y hxy
  let e := TensorGroupEquiv.tensorGroupBialgEquiv
    (k := k)
    (B := SymmetricAlgebra k (AdditiveRelationSpace k I))
    (M := TorusRelationGroup k I)
  apply e.injective
  apply groupGradedJointBialgHom_injective k I
  change mixedProjectionTensorBialgHom k I (e.symm (e x)) =
    mixedProjectionTensorBialgHom k I (e.symm (e y))
  rw [e.symm_apply_apply, e.symm_apply_apply]
  exact hxy

/-- The classified tensor presentation is a bijective bialgebra morphism. -/
theorem mixedProjectionTensorBialgHom_bijective :
    Function.Bijective (mixedProjectionTensorBialgHom k I) :=
  ⟨mixedProjectionTensorBialgHom_injective k I,
    mixedProjectionTensorBialgHom_surjective k I⟩

/-- The factorwise classified quotient kills exactly the original mixed Hopf ideal. -/
theorem mem_iff_mixedProjectionTensorQuotientBialgHom_eq_zero
    (x : CoordinateAlgebra k n) :
    x ∈ I ↔ mixedProjectionTensorQuotientBialgHom k I x = 0 := by
  have hcomp := DFunLike.congr_fun
    (mixedProjectionTensorAlgHom_comp_quotientBialgHom k I) x
  change mixedProjectionTensorBialgHom k I
      (mixedProjectionTensorQuotientBialgHom k I x) =
    Ideal.Quotient.mk I x at hcomp
  constructor
  · intro hx
    apply mixedProjectionTensorBialgHom_injective k I
    rw [hcomp, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · intro hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← hcomp, hx, map_zero]

/-- The residual tensor kernel is zero. -/
theorem jointKernel_eq_bot : jointKernel k I = ⊥ := by
  ext x
  change mixedProjectionTensorBialgHom k I x = 0 ↔ x = 0
  constructor
  · intro hx
    apply mixedProjectionTensorBialgHom_injective k I
    exact hx.trans (map_zero _).symm
  · rintro rfl
    simp

/-- The equivalent group-graded residual kernel is zero. -/
theorem groupGradedJointKernel_eq_bot : groupGradedJointKernel k I = ⊥ := by
  ext x
  change groupGradedJointBialgHom k I x = 0 ↔ x = 0
  constructor
  · intro hx
    apply groupGradedJointBialgHom_injective k I
    exact hx.trans (map_zero _).symm
  · rintro rfl
    simp

end
end MixedProjectionTensorKernelVanishing
end GaloisForLFunctions.HTGeometry
