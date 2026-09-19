import GaloisForLFunctions.RHTower.MaassRationalHeckeCorrespondenceL2
import GaloisForLFunctions.RHTower.IntegralSubgroupUnitaryRepresentation
import GaloisForLFunctions.RHTower.SelbergMaassEigenspaceQuotientL2
import GaloisForLFunctions.RHTower.MaassRationalHeckeFormalProduct

/-!
# Rational-conjugate quotient transport for the completed Maass model

A positive-determinant rational Hecke representative is normalized to `SL₂(ℝ)`.
Right multiplication by that normalization conjugates the principal congruence
quotient to its rational-conjugate quotient. This file proves the induced map is
continuous and Haar-quotient-measure preserving. It also lifts the finite-cover
and finite-fibre intertwiners to show that the resulting principal `L²` Hecke
endomorphism commutes with every real `SL₂` translation.
-/

namespace GaloisForLFunctions.RHTower

open UpperHalfPlane
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

noncomputable section

/-- The determinant-one normalization of a positive rational real matrix. -/
def rationalSL2Normalization (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) : SL2R :=
  ⟨(Real.sqrt ((g.map (algebraMap ℚ ℝ)).val.det))⁻¹ •
      (g.map (algebraMap ℚ ℝ)).val, by
    rw [Matrix.det_smul]
    norm_num
    have hsqrt : (Real.sqrt ((g.map (algebraMap ℚ ℝ)).val.det)) ^ 2 =
        (g.map (algebraMap ℚ ℝ)).val.det :=
      Real.sq_sqrt hg.le
    field_simp [Real.sqrt_ne_zero'.mpr hg]
    change (g.map (algebraMap ℚ ℝ)).val.det /
      (Real.sqrt ((g.map (algebraMap ℚ ℝ)).val.det)) ^ 2 = 1
    rw [hsqrt]
    field_simp⟩

@[simp] theorem rationalSL2Normalization_coe (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) :
    ((rationalSL2Normalization g hg : SL2R) : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt ((g.map (algebraMap ℚ ℝ)).val.det))⁻¹ •
        (g.map (algebraMap ℚ ℝ)).val :=
  rfl

end

end GaloisForLFunctions.RHTower


namespace GaloisForLFunctions.RHTower

open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

noncomputable section

private def normalizationScalarUnit (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) : ℝˣ :=
  Units.mk0 (Real.sqrt ((g.map (algebraMap ℚ ℝ)).val.det))⁻¹
    (inv_ne_zero (Real.sqrt_ne_zero'.mpr hg))

theorem rationalSL2Normalization_toGL (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) :
    Matrix.SpecialLinearGroup.toGL (rationalSL2Normalization g hg) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (normalizationScalarUnit g hg) *
        g.map (algebraMap ℚ ℝ) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((rationalSL2Normalization g hg : SL2R) : Matrix (Fin 2) (Fin 2) ℝ) i j =
    ((Matrix.scalar (Fin 2) (normalizationScalarUnit g hg : ℝ)) *
      (g.map (algebraMap ℚ ℝ)).val) i j
  rw [rationalSL2Normalization_coe]
  change ((Real.sqrt ((g.map (algebraMap ℚ ℝ)).val.det))⁻¹ •
      (g.map (algebraMap ℚ ℝ)).val) i j =
    (Matrix.diagonal (fun _ : Fin 2 => (normalizationScalarUnit g hg : ℝ)) *
      (g.map (algebraMap ℚ ℝ)).val) i j
  rw [← smul_eq_diagonal_mul]
  rfl

theorem rationalSL2Normalization_conj_cancel (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (x : SL2R) :
    g.map (algebraMap ℚ ℝ) *
        Matrix.SpecialLinearGroup.toGL ((rationalSL2Normalization g hg)⁻¹ * x *
          rationalSL2Normalization g hg) *
        (g.map (algebraMap ℚ ℝ))⁻¹ =
      Matrix.SpecialLinearGroup.toGL x := by
  have hnorm_inv : Matrix.SpecialLinearGroup.toGL (rationalSL2Normalization g hg)⁻¹ =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (normalizationScalarUnit g hg) *
        g.map (algebraMap ℚ ℝ))⁻¹ := by
    rw [map_inv, rationalSL2Normalization_toGL]
  rw [map_mul, map_mul, hnorm_inv, rationalSL2Normalization_toGL]
  rw [_root_.mul_inv_rev]
  have hcomm :
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (normalizationScalarUnit g hg))⁻¹ *
        Matrix.SpecialLinearGroup.toGL x =
      Matrix.SpecialLinearGroup.toGL x *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) (normalizationScalarUnit g hg))⁻¹ := by
    simpa only [map_inv] using
      (Matrix.GeneralLinearGroup.scalar_commute (normalizationScalarUnit g hg)⁻¹
        (Matrix.SpecialLinearGroup.toGL x))
  calc
    _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) (normalizationScalarUnit g hg))⁻¹ *
        Matrix.SpecialLinearGroup.toGL x *
        Matrix.GeneralLinearGroup.scalar (Fin 2) (normalizationScalarUnit g hg) := by group
    _ = _ := by rw [hcomm]; group

/-- The normalized inverse has the inverse projective action of the original
positive rational matrix on the upper half-plane. -/
theorem rationalSL2Normalization_inv_action_cancel (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (z : UpperHalfPlane) :
    g.map (algebraMap ℚ ℝ) • ((rationalSL2Normalization g hg)⁻¹ • z) = z := by
  change g.map (algebraMap ℚ ℝ) •
    ((Matrix.SpecialLinearGroup.toGL (rationalSL2Normalization g hg))⁻¹ • z) = z
  rw [← mul_smul, rationalSL2Normalization_toGL]
  rw [_root_.mul_inv_rev]
  have hcancel : g.map (algebraMap ℚ ℝ) *
      ((g.map (algebraMap ℚ ℝ))⁻¹ *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) (normalizationScalarUnit g hg))⁻¹) =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (normalizationScalarUnit g hg))⁻¹ := by
    group
  rw [hcancel]
  exact UpperHalfPlane.glScalar_smul (normalizationScalarUnit g hg)⁻¹ z

end

end GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.RHTower

open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise

noncomputable section

/-- Determinant normalization identifies the principal real source subgroup with
its rational conjugate inside `SL(2, ℝ)`. -/
def rationalSL2ConjugateSubgroupEquiv (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) :
    realImage (CongruenceSubgroup.Gamma (N + 1)) ≃*
      rationalConjugateSL2Group N g where
  toFun x := ⟨(rationalSL2Normalization g hg)⁻¹ * x.val *
      rationalSL2Normalization g hg, by
    change Matrix.SpecialLinearGroup.toGL ((rationalSL2Normalization g hg)⁻¹ * x.val *
      rationalSL2Normalization g hg) ∈ rationalConjugateGroup N g
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change g.map (algebraMap ℚ ℝ) *
        Matrix.SpecialLinearGroup.toGL ((rationalSL2Normalization g hg)⁻¹ * x.val *
          rationalSL2Normalization g hg) *
        (g.map (algebraMap ℚ ℝ))⁻¹ ∈ principalCongruenceGL N
    rw [rationalSL2Normalization_conj_cancel]
    change Matrix.SpecialLinearGroup.toGL x.val ∈ principalCongruenceGL N
    change x.val ∈ (principalCongruenceGL N).comap Matrix.SpecialLinearGroup.toGL
    rw [principalCongruenceGL_comap_sl2ToGL]
    exact x.property⟩
  invFun y := ⟨rationalSL2Normalization g hg * y.val *
      (rationalSL2Normalization g hg)⁻¹, by
    rw [← principalCongruenceGL_comap_sl2ToGL]
    change Matrix.SpecialLinearGroup.toGL (rationalSL2Normalization g hg * y.val *
      (rationalSL2Normalization g hg)⁻¹) ∈ principalCongruenceGL N
    have hy : g.map (algebraMap ℚ ℝ) * Matrix.SpecialLinearGroup.toGL y.val *
        (g.map (algebraMap ℚ ℝ))⁻¹ ∈ principalCongruenceGL N := by
      have hy' := y.property
      change Matrix.SpecialLinearGroup.toGL y.val ∈ rationalConjugateGroup N g at hy'
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
      exact hy'
    have hconj : Matrix.SpecialLinearGroup.toGL (rationalSL2Normalization g hg * y.val *
        (rationalSL2Normalization g hg)⁻¹) =
        g.map (algebraMap ℚ ℝ) * Matrix.SpecialLinearGroup.toGL y.val *
          (g.map (algebraMap ℚ ℝ))⁻¹ := by
      symm
      have h := rationalSL2Normalization_conj_cancel g hg
        (rationalSL2Normalization g hg * y.val * (rationalSL2Normalization g hg)⁻¹)
      convert h using 1 ; group
    rw [hconj]
    exact hy⟩
  left_inv x := by
    apply Subtype.ext
    group
  right_inv y := by
    apply Subtype.ext
    group
  map_mul' x y := by
    apply Subtype.ext
    change (rationalSL2Normalization g hg)⁻¹ * (x.val * y.val) *
        rationalSL2Normalization g hg =
      ((rationalSL2Normalization g hg)⁻¹ * x.val * rationalSL2Normalization g hg) *
        ((rationalSL2Normalization g hg)⁻¹ * y.val * rationalSL2Normalization g hg)
    group

end

end GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.RHTower

open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise

noncomputable section

/-- Right multiplication by the normalized matrix descends to the associated
principal and rational-conjugate quotient spaces. -/
def rationalSL2ConjugateQuotientEquiv (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) :
    SL2R ⧸ realImage (CongruenceSubgroup.Gamma (N + 1)) ≃
      SL2R ⧸ rationalConjugateSL2Group N g :=
  Quotient.congr (Equiv.mulRight (rationalSL2Normalization g hg)) (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    constructor
    · intro hxy
      have hmem : (rationalSL2Normalization g hg)⁻¹ * (x⁻¹ * y) *
          rationalSL2Normalization g hg ∈ rationalConjugateSL2Group N g :=
        (rationalSL2ConjugateSubgroupEquiv N g hg) ⟨x⁻¹ * y, hxy⟩ |>.property
      change (x * rationalSL2Normalization g hg)⁻¹ *
        (y * rationalSL2Normalization g hg) ∈ rationalConjugateSL2Group N g
      convert hmem using 1 ; group
    · intro hxy
      change (x * rationalSL2Normalization g hg)⁻¹ *
        (y * rationalSL2Normalization g hg) ∈ rationalConjugateSL2Group N g at hxy
      have hmem : (rationalSL2Normalization g hg) * ((x * rationalSL2Normalization g hg)⁻¹ *
          (y * rationalSL2Normalization g hg)) * (rationalSL2Normalization g hg)⁻¹ ∈
          realImage (CongruenceSubgroup.Gamma (N + 1)) :=
        (rationalSL2ConjugateSubgroupEquiv N g hg).symm
          ⟨(x * rationalSL2Normalization g hg)⁻¹ * (y * rationalSL2Normalization g hg), hxy⟩
          |>.property
      convert hmem using 1 ; group)

@[simp] theorem rationalSL2ConjugateQuotientEquiv_mk (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (x : SL2R) :
    rationalSL2ConjugateQuotientEquiv N g hg (QuotientGroup.mk x) =
      QuotientGroup.mk (x * rationalSL2Normalization g hg) :=
  rfl

end

end GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.RHTower

open MeasureTheory
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise

noncomputable section

/-- Opposite subgroups are equivalent in the reverse direction. -/
def opSubgroupEquiv {P R : Subgroup SL2R} (e : P ≃* R) : R.op ≃ P.op where
  toFun r :=
    let r' : R := ⟨r.val.unop, r.property⟩
    let p := e.symm r'
    ⟨MulOpposite.op p.val, p.property⟩
  invFun p :=
    let p' : P := ⟨p.val.unop, p.property⟩
    let r := e p'
    ⟨MulOpposite.op r.val, r.property⟩
  left_inv r := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    change ((e ⟨(e.symm ⟨r.val.unop, r.property⟩).val,
      (e.symm ⟨r.val.unop, r.property⟩).property⟩).val) = r.val.unop
    simp
  right_inv p := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    change ((e.symm ⟨(e ⟨p.val.unop, p.property⟩).val,
      (e ⟨p.val.unop, p.property⟩).property⟩).val) = p.val.unop
    simp

theorem rationalSL2Conjugate_image_isFundamentalDomain (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) :
    IsFundamentalDomain (rationalConjugateSL2Group N g).op
      ((Homeomorph.mulRight (rationalSL2Normalization g hg) : SL2R → SL2R) ''
        integralSubgroupFundamentalSet (CongruenceSubgroup.Gamma (N + 1))) realSL2Haar := by
  refine (integralSubgroupFundamentalSet_isFundamentalDomain
    (CongruenceSubgroup.Gamma (N + 1))).image_of_equiv
      (Homeomorph.mulRight (rationalSL2Normalization g hg)).toEquiv ?_ ?_ ?_
  · exact (measurePreserving_mul_right realSL2Haar
      (rationalSL2Normalization g hg)⁻¹).quasiMeasurePreserving
  · exact opSubgroupEquiv (rationalSL2ConjugateSubgroupEquiv N g hg)
  · intro r x
    change (x * (rationalSL2Normalization g hg * (r.val.unop : SL2R) *
      (rationalSL2Normalization g hg)⁻¹)) * rationalSL2Normalization g hg =
      (x * rationalSL2Normalization g hg) * (r.val.unop : SL2R)
    group

end

end GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise

noncomputable section

theorem rationalSL2ConjugateQuotientEquiv_continuous (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) :
    Continuous (rationalSL2ConjugateQuotientEquiv N g hg) := by
  rw [(QuotientGroup.isQuotientMap_mk
    (realImage (CongruenceSubgroup.Gamma (N + 1)))).continuous_iff]
  change Continuous (fun x : SL2R => QuotientGroup.mk
    (x * rationalSL2Normalization g hg))
  exact QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)

theorem rationalSL2ConjugateQuotientEquiv_measurePreserving (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) :
    MeasurePreserving (rationalSL2ConjugateQuotientEquiv N g hg)
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))
      (rationalConjugateSL2QuotientMeasure N g) := by
  let a := rationalSL2Normalization g hg
  let F := integralSubgroupFundamentalSet (CongruenceSubgroup.Gamma (N + 1))
  let F' := (Homeomorph.mulRight a : SL2R → SL2R) '' F
  let qP : SL2R → SL2R ⧸ realImage (CongruenceSubgroup.Gamma (N + 1)) := QuotientGroup.mk
  let qR : SL2R → SL2R ⧸ rationalConjugateSL2Group N g := QuotientGroup.mk
  let Q := rationalSL2ConjugateQuotientEquiv N g hg
  have hQ : Measurable Q := (rationalSL2ConjugateQuotientEquiv_continuous N g hg).measurable
  have hqP : Measurable qP := QuotientGroup.measurable_coe
  have hqR : Measurable qR := QuotientGroup.measurable_coe
  have hF : IsFundamentalDomain (realImage (CongruenceSubgroup.Gamma (N + 1))).op F
      realSL2Haar := integralSubgroupFundamentalSet_isFundamentalDomain _
  have hF' : IsFundamentalDomain (rationalConjugateSL2Group N g).op F'
      realSL2Haar := rationalSL2Conjugate_image_isFundamentalDomain N g hg
  have ha : MeasurePreserving (fun x : SL2R => x * a) realSL2Haar realSL2Haar :=
    realSL2Haar_rightTranslation a
  have haF : MeasurePreserving (fun x : SL2R => x * a)
      (realSL2Haar.restrict F) (realSL2Haar.restrict F') := by
    exact ha.restrict_image_emb (MeasurableEquiv.mulRight a).measurableEmbedding F
  have hcomp : Q ∘ qP = qR ∘ (fun x : SL2R => x * a) := by
    funext x
    exact rationalSL2ConjugateQuotientEquiv_mk N g hg x
  refine ⟨hQ, ?_⟩
  rw [hF.projection_respects_measure
      (μ := integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1))),
    hF'.projection_respects_measure (μ := rationalConjugateSL2QuotientMeasure N g)]
  calc
    Measure.map Q (Measure.map qP (realSL2Haar.restrict F)) =
        Measure.map (Q ∘ qP) (realSL2Haar.restrict F) :=
      Measure.map_map hQ hqP
    _ = Measure.map (qR ∘ fun x : SL2R => x * a) (realSL2Haar.restrict F) := by rw [hcomp]
    _ = Measure.map qR (Measure.map (fun x : SL2R => x * a) (realSL2Haar.restrict F)) :=
      (Measure.map_map hqR (MeasurableEquiv.mulRight a).measurable).symm
    _ = Measure.map qR (realSL2Haar.restrict F') := by rw [haF.map_eq]

end

end GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.RHTower

open MeasureTheory

noncomputable section

/-- The bounded rational Hecke correspondence, transported back to the principal
quotient through the canonical Haar isometry. -/
noncomputable def rationalHeckePrincipalLpEndomorphism (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) :
    Lp ℂ 2 (MaassQuotientL2.quotientMeasure N) →L[ℂ]
      Lp ℂ 2 (MaassQuotientL2.quotientMeasure N) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (rationalSL2ConjugateQuotientEquiv N g hg)
    (rationalSL2ConjugateQuotientEquiv_measurePreserving N g hg)).toContinuousLinearMap.comp
      (rationalHeckePrincipalToConjugateLpContinuousLinear N g)

/-- On the source Maass vector, the principal-quotient endomorphism is the
finite rational-conjugate fibre trace pulled back by the quotient isometry. -/
theorem rationalHeckePrincipalLpEndomorphism_source
    (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    rationalHeckePrincipalLpEndomorphism N g hg (MaassQuotientL2.sourceLp N f) =
      Lp.compMeasurePreserving (rationalSL2ConjugateQuotientEquiv N g hg)
        (rationalSL2ConjugateQuotientEquiv_measurePreserving N g hg)
        (rationalHeckeConjugateFiberTraceSourceLp N g f) := by
  unfold rationalHeckePrincipalLpEndomorphism
  change Lp.compMeasurePreserving (rationalSL2ConjugateQuotientEquiv N g hg)
    (rationalSL2ConjugateQuotientEquiv_measurePreserving N g hg)
    (rationalHeckePrincipalToConjugateLpContinuousLinear N g
      (MaassQuotientL2.sourceLp N f)) = _
  rw [rationalHeckePrincipalToConjugateLpContinuousLinear_source]

end

end GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.RHTower

open MeasureTheory Filter UpperHalfPlane
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise

noncomputable section

noncomputable def rationalConjugateSL2Unitary (N : ℕ) (g : GL (Fin 2) ℚ) (a : SL2R) :
    Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g) where
  toLinearEquiv := DistribMulAction.toLinearEquiv ℂ _ (DomMulAct.mk a⁻¹)
  norm_map' := DomMulAct.norm_smul_Lp _

theorem rationalConjugateSL2Unitary_ae_eq (N : ℕ) (g : GL (Fin 2) ℚ) (a : SL2R)
    (v : Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g)) :
    rationalConjugateSL2Unitary N g a v =ᵐ[rationalConjugateSL2QuotientMeasure N g]
      fun q => v (a⁻¹ • q) :=
  DomMulAct.smul_Lp_ae_eq (DomMulAct.mk a⁻¹) v

theorem subgroupQuotientProjection_smul {G : Type*} [Group G]
    (K Γ : Subgroup G) (hKΓ : K ≤ Γ) (a : G) (q : G ⧸ K) :
    subgroupQuotientProjection K Γ hKΓ (a • q) =
      a • subgroupQuotientProjection K Γ hKΓ q := by
  induction q using Quotient.inductionOn with
  | h x => rfl

theorem rationalSL2ConjugateQuotientEquiv_smul (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (a : SL2R)
    (q : SL2R ⧸ realImage (CongruenceSubgroup.Gamma (N + 1))) :
    rationalSL2ConjugateQuotientEquiv N g hg (a • q) =
      a • rationalSL2ConjugateQuotientEquiv N g hg q := by
  induction q using Quotient.inductionOn with
  | h x =>
    change QuotientGroup.mk ((a * x) * rationalSL2Normalization g hg) =
      QuotientGroup.mk (a * (x * rationalSL2Normalization g hg))
    rw [mul_assoc]


theorem integralFiniteCoverPullbackLp_intertwines_unitary
    (K Γ : Subgroup SL2Z) [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ)
    (a : SL2R) (f : Lp ℂ 2 (integralSubgroupQuotientMeasure Γ)) :
    integralFiniteCoverPullbackLp K Γ hKΓ (integralSubgroupUnitary Γ a f) =
      integralSubgroupUnitary K a (integralFiniteCoverPullbackLp K Γ hKΓ f) := by
  let P := subgroupQuotientProjection (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ)
  have hUbase := (integralSubgroupUnitary_ae_eq Γ a f).comp_tendsto
    (integralFiniteCoverProjection_quasiMeasurePreserving K Γ hKΓ).tendsto_ae
  have hpullshift := (coe_integralFiniteCoverPullbackLp K Γ hKΓ f).comp_tendsto
    (measurePreserving_smul a⁻¹ (integralSubgroupQuotientMeasure K)).quasiMeasurePreserving.tendsto_ae
  apply Lp.ext
  filter_upwards [coe_integralFiniteCoverPullbackLp K Γ hKΓ
      (integralSubgroupUnitary Γ a f), hUbase,
    integralSubgroupUnitary_ae_eq K a (integralFiniteCoverPullbackLp K Γ hKΓ f),
    hpullshift] with q hleft hU hright hpull
  rw [hleft, hU, hright]
  have hpull' : integralFiniteCoverPullbackLp K Γ hKΓ f (a⁻¹ • q) =
      f (P (a⁻¹ • q)) := hpull
  change f (a⁻¹ • P q) = integralFiniteCoverPullbackLp K Γ hKΓ f (a⁻¹ • q)
  rw [hpull']
  exact congrArg f (subgroupQuotientProjection_smul
    (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ) a⁻¹ q).symm


theorem rationalHeckeConjugateFiberTraceLp_intertwines_unitary
    (N : ℕ) (g : GL (Fin 2) ℚ) (a : SL2R)
    (f : Lp ℂ 2 (integralSubgroupQuotientMeasure
      (rationalHeckeIntegralIntersection N g))) :
    rationalHeckeConjugateFiberTraceLp N g
      (integralSubgroupUnitary (rationalHeckeIntegralIntersection N g) a f) =
      rationalConjugateSL2Unitary N g a (rationalHeckeConjugateFiberTraceLp N g f) := by
  let f₀ := AEStronglyMeasurable.mk f (Lp.aestronglyMeasurable f)
  let fa := AEStronglyMeasurable.mk
    (integralSubgroupUnitary (rationalHeckeIntegralIntersection N g) a f)
    (Lp.aestronglyMeasurable
      (integralSubgroupUnitary (rationalHeckeIntegralIntersection N g) a f))
  have hf₀ : StronglyMeasurable f₀ :=
    (Lp.aestronglyMeasurable f).stronglyMeasurable_mk
  have hfa : StronglyMeasurable fa :=
    (Lp.aestronglyMeasurable
      (integralSubgroupUnitary (rationalHeckeIntegralIntersection N g) a f)).stronglyMeasurable_mk
  have hfshift : (f : SL2R ⧸ realImage (rationalHeckeIntegralIntersection N g) → ℂ) ∘
      (fun q => a⁻¹ • q) =ᵐ[
        integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)]
      f₀ ∘ (fun q => a⁻¹ • q) := by
    change (f : SL2R ⧸ realImage (rationalHeckeIntegralIntersection N g) → ℂ) ∘
        (fun q => a⁻¹ • q) =ᵐ[
          integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)]
        AEStronglyMeasurable.mk f (Lp.aestronglyMeasurable f) ∘ (fun q => a⁻¹ • q)
    exact (Lp.aestronglyMeasurable f).ae_eq_mk.comp_tendsto
      (measurePreserving_smul a⁻¹
        (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g))).quasiMeasurePreserving.tendsto_ae
  have hleftRaw : f₀ ∘ (fun q => a⁻¹ • q) =
      subgroupQuotientLeftTranslate (rationalHeckeCommonCoverReal N g) a f₀ := by
    rfl
  have hfaeq : fa =ᵐ[integralSubgroupQuotientMeasure
      (rationalHeckeIntegralIntersection N g)]
      subgroupQuotientLeftTranslate (rationalHeckeCommonCoverReal N g) a f₀ := by
    calc
      fa =ᵐ[integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)]
          integralSubgroupUnitary (rationalHeckeIntegralIntersection N g) a f :=
        (Lp.aestronglyMeasurable
          (integralSubgroupUnitary (rationalHeckeIntegralIntersection N g) a f)).ae_eq_mk.symm
      _ =ᵐ[integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)]
          (f : SL2R ⧸ realImage (rationalHeckeIntegralIntersection N g) → ℂ) ∘
            (fun q => a⁻¹ • q) := by
        change integralSubgroupUnitary (rationalHeckeIntegralIntersection N g) a f =ᵐ[
          integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)]
            fun q => f (a⁻¹ • q)
        exact integralSubgroupUnitary_ae_eq (rationalHeckeIntegralIntersection N g) a f
      _ =ᵐ[integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)]
          f₀ ∘ (fun q => a⁻¹ • q) := hfshift
      _ =ᵐ[integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)]
          subgroupQuotientLeftTranslate (rationalHeckeCommonCoverReal N g) a f₀ :=
        EventuallyEq.of_eq hleftRaw
  have hleftStrong : StronglyMeasurable
      (subgroupQuotientLeftTranslate (rationalHeckeCommonCoverReal N g) a f₀) := by
    change StronglyMeasurable (fun q => f₀ (a⁻¹ • q))
    exact hf₀.comp_measurable (measurable_const_smul _)
  have htraceCongr := rationalHeckeConjugateFiberTrace_congr_ae_of_stronglyMeasurable
    N g fa (subgroupQuotientLeftTranslate (rationalHeckeCommonCoverReal N g) a f₀)
      hfa hleftStrong hfaeq
  have htraceShift : subgroupQuotientLeftTranslate (rationalConjugateSL2Group N g) a
      (rationalHeckeConjugateFiberTrace N g f₀) =ᵐ[
        rationalConjugateSL2QuotientMeasure N g]
      rationalConjugateSL2Unitary N g a (rationalHeckeConjugateFiberTraceLp N g f) := by
    have htracepull : rationalHeckeConjugateFiberTrace N g f₀ ∘ (fun q => a⁻¹ • q) =ᵐ[
        rationalConjugateSL2QuotientMeasure N g]
        (rationalHeckeConjugateFiberTraceLp N g f :
          SL2R ⧸ rationalConjugateSL2Group N g → ℂ) ∘ (fun q => a⁻¹ • q) := by
      change rationalHeckeConjugateFiberTrace N g
          (AEStronglyMeasurable.mk f (Lp.aestronglyMeasurable f)) ∘ (fun q => a⁻¹ • q) =ᵐ[
            rationalConjugateSL2QuotientMeasure N g]
          (rationalHeckeConjugateFiberTraceLp N g f :
            SL2R ⧸ rationalConjugateSL2Group N g → ℂ) ∘ (fun q => a⁻¹ • q)
      exact (coe_rationalHeckeConjugateFiberTraceLp N g f).symm.comp_tendsto
        (measurePreserving_smul a⁻¹
          (rationalConjugateSL2QuotientMeasure N g)).quasiMeasurePreserving.tendsto_ae
    have hunit : rationalConjugateSL2Unitary N g a
        (rationalHeckeConjugateFiberTraceLp N g f) =ᵐ[
          rationalConjugateSL2QuotientMeasure N g]
        (rationalHeckeConjugateFiberTraceLp N g f :
          SL2R ⧸ rationalConjugateSL2Group N g → ℂ) ∘ (fun q => a⁻¹ • q) := by
      change rationalConjugateSL2Unitary N g a
          (rationalHeckeConjugateFiberTraceLp N g f) =ᵐ[
            rationalConjugateSL2QuotientMeasure N g]
          fun q => rationalHeckeConjugateFiberTraceLp N g f (a⁻¹ • q)
      exact rationalConjugateSL2Unitary_ae_eq N g a
        (rationalHeckeConjugateFiberTraceLp N g f)
    have hrightRaw : subgroupQuotientLeftTranslate (rationalConjugateSL2Group N g) a
        (rationalHeckeConjugateFiberTrace N g f₀) =
        rationalHeckeConjugateFiberTrace N g f₀ ∘ (fun q => a⁻¹ • q) := by
      rfl
    exact (EventuallyEq.of_eq hrightRaw).trans (htracepull.trans hunit.symm)
  apply Lp.ext
  exact (coe_rationalHeckeConjugateFiberTraceLp N g
    (integralSubgroupUnitary (rationalHeckeIntegralIntersection N g) a f)).trans
      (htraceCongr.trans ((EventuallyEq.of_eq
        (rationalHeckeConjugateFiberTrace_intertwines_leftTranslate N g a f₀)).trans htraceShift))


theorem rationalSL2ConjugateLpTransport_intertwines_unitary
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (a : SL2R)
    (v : Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g)) :
    Lp.compMeasurePreserving (rationalSL2ConjugateQuotientEquiv N g hg)
      (rationalSL2ConjugateQuotientEquiv_measurePreserving N g hg)
      (rationalConjugateSL2Unitary N g a v) =
      integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) a
        (Lp.compMeasurePreserving (rationalSL2ConjugateQuotientEquiv N g hg)
          (rationalSL2ConjugateQuotientEquiv_measurePreserving N g hg) v) := by
  let Q := rationalSL2ConjugateQuotientEquiv N g hg
  let hQ := rationalSL2ConjugateQuotientEquiv_measurePreserving N g hg
  have hURpull := (rationalConjugateSL2Unitary_ae_eq N g a v).comp_tendsto
    hQ.quasiMeasurePreserving.tendsto_ae
  have hTshift := (Lp.coeFn_compMeasurePreserving v hQ).comp_tendsto
    (measurePreserving_smul a⁻¹
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))).quasiMeasurePreserving.tendsto_ae
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (rationalConjugateSL2Unitary N g a v) hQ, hURpull,
    integralSubgroupUnitary_ae_eq (CongruenceSubgroup.Gamma (N + 1)) a
      (Lp.compMeasurePreserving Q hQ v), hTshift] with q hleft hUR hright hT
  rw [hleft, hUR, hright]
  have hT' : Lp.compMeasurePreserving Q hQ v (a⁻¹ • q) =
      v (Q (a⁻¹ • q)) := hT
  rw [hT']
  exact congrArg v (rationalSL2ConjugateQuotientEquiv_smul N g hg a⁻¹ q).symm


theorem rationalHeckePrincipalToConjugateLpContinuousLinear_intertwines_unitary
    (N : ℕ) (g : GL (Fin 2) ℚ) (a : SL2R)
    (f : Lp ℂ 2 (MaassQuotientL2.quotientMeasure N)) :
    rationalHeckePrincipalToConjugateLpContinuousLinear N g
      (integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) a f) =
      rationalConjugateSL2Unitary N g a
        (rationalHeckePrincipalToConjugateLpContinuousLinear N g f) := by
  letI : (rationalHeckeIntegralIntersection N g).IsFiniteRelIndex
      (CongruenceSubgroup.Gamma (N + 1)) :=
    rationalHeckeIntegralIntersection_isFiniteRelIndex_principal N g
  unfold rationalHeckePrincipalToConjugateLpContinuousLinear
  change rationalHeckeConjugateFiberTraceLp N g
      (integralFiniteCoverPullbackLp (rationalHeckeIntegralIntersection N g)
        (CongruenceSubgroup.Gamma (N + 1))
        (rationalHeckeIntegralIntersection_le_principal N g)
        (integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) a f)) =
    rationalConjugateSL2Unitary N g a (rationalHeckeConjugateFiberTraceLp N g
      (integralFiniteCoverPullbackLp (rationalHeckeIntegralIntersection N g)
        (CongruenceSubgroup.Gamma (N + 1))
        (rationalHeckeIntegralIntersection_le_principal N g) f))
  rw [integralFiniteCoverPullbackLp_intertwines_unitary,
    rationalHeckeConjugateFiberTraceLp_intertwines_unitary]

theorem rationalHeckePrincipalLpEndomorphism_intertwines_unitary
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (a : SL2R)
    (f : Lp ℂ 2 (MaassQuotientL2.quotientMeasure N)) :
    rationalHeckePrincipalLpEndomorphism N g hg
      (integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) a f) =
      integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) a
        (rationalHeckePrincipalLpEndomorphism N g hg f) := by
  unfold rationalHeckePrincipalLpEndomorphism
  change Lp.compMeasurePreserving (rationalSL2ConjugateQuotientEquiv N g hg)
      (rationalSL2ConjugateQuotientEquiv_measurePreserving N g hg)
      (rationalHeckePrincipalToConjugateLpContinuousLinear N g
        (integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) a f)) =
    integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) a
      (Lp.compMeasurePreserving (rationalSL2ConjugateQuotientEquiv N g hg)
        (rationalSL2ConjugateQuotientEquiv_measurePreserving N g hg)
        (rationalHeckePrincipalToConjugateLpContinuousLinear N g f))
  rw [rationalHeckePrincipalToConjugateLpContinuousLinear_intertwines_unitary]
  exact rationalSL2ConjugateLpTransport_intertwines_unitary N g hg a
    (rationalHeckePrincipalToConjugateLpContinuousLinear N g f)

end

end GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.RHTower

open MeasureTheory Filter
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise

noncomputable section

theorem rationalHeckePrincipalLpEndomorphism_source_ae_glTraceQuotientLift
    (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    rationalHeckePrincipalLpEndomorphism N g hg (MaassQuotientL2.sourceLp N f) =ᵐ[
      MaassQuotientL2.quotientMeasure N]
      fun q => maassInvariantQuotientLift (rationalConjugateSL2Group N g)
        (rationalCommonCoverGLTraceSLInvariant N g f)
        (rationalSL2ConjugateQuotientEquiv N g hg q) := by
  let Q := rationalSL2ConjugateQuotientEquiv N g hg
  let hQ := rationalSL2ConjugateQuotientEquiv_measurePreserving N g hg
  calc
    rationalHeckePrincipalLpEndomorphism N g hg (MaassQuotientL2.sourceLp N f) =ᵐ[
        MaassQuotientL2.quotientMeasure N]
        Lp.compMeasurePreserving Q hQ (rationalHeckeConjugateFiberTraceSourceLp N g f) :=
      EventuallyEq.of_eq (congrArg
        (fun v : Lp ℂ 2 (MaassQuotientL2.quotientMeasure N) =>
          (v : SL2R ⧸ realImage (CongruenceSubgroup.Gamma (N + 1)) → ℂ))
        (rationalHeckePrincipalLpEndomorphism_source N g hg f))
    _ =ᵐ[MaassQuotientL2.quotientMeasure N]
        (rationalHeckeConjugateFiberTraceSourceLp N g f :
          SL2R ⧸ rationalConjugateSL2Group N g → ℂ) ∘ Q :=
      Lp.coeFn_compMeasurePreserving _ _
    _ =ᵐ[MaassQuotientL2.quotientMeasure N]
        (maassInvariantQuotientLift (rationalConjugateSL2Group N g)
          (rationalCommonCoverGLTraceSLInvariant N g f)) ∘ Q :=
      (coe_rationalHeckeConjugateFiberTraceSourceLp_eq_glTraceQuotientLift N g f).comp_tendsto
        hQ.quasiMeasurePreserving.tendsto_ae


/-- Pulling back the inverse rational conjugate intersection by `g` recovers
the common-cover subgroup for `g`. This is the subgroup identity behind the
inverse orientation of the transported quotient correspondence. -/
theorem rationalPullback_principal_inf_inverse_eq_commonCover
    (N : ℕ) (g : GL (Fin 2) ℚ) :
    rationalPullbackConjugateGroup
      (principalCongruenceGL N ⊓ rationalConjugateGroup N g⁻¹) g =
      principalCongruenceGL N ⊓ rationalConjugateGroup N g := by
  ext x
  simp only [rationalConjugateGroup, rationalPullbackConjugateGroup,
    Subgroup.mem_inf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul,
    Matrix.GeneralLinearGroup.map_inv]
  let A := g.map (algebraMap ℚ ℝ)
  have hact : (ConjAct.toConjAct A)⁻¹ • ((ConjAct.toConjAct A) • x) = x :=
    inv_smul_smul (ConjAct.toConjAct A) x
  constructor
  · rintro ⟨hconj, hx⟩
    refine ⟨?_, hconj⟩
    have hx' : (ConjAct.toConjAct A)⁻¹ • ((ConjAct.toConjAct A) • x) ∈
        principalCongruenceGL N := by
      exact hx
    rw [hact] at hx'
    exact hx'
  · rintro ⟨hx, hconj⟩
    refine ⟨hconj, ?_⟩
    change (ConjAct.toConjAct A)⁻¹ • ((ConjAct.toConjAct A) • x) ∈
      principalCongruenceGL N
    rw [hact]
    exact hx


/-- On the upper-half-plane section induced by determinant normalization, the
completed correspondence's finite common-cover trace is the ordinary rational
principal trace for the inverse rational representative.  The relative-coset
quotient is unchanged: both traces are indexed by the intersection of the
principal group with the inverse rational conjugate. -/
theorem rationalCommonCoverGLTrace_normalization_inverse_eq_principalTrace
    (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hgi : 0 < ((g⁻¹).map (algebraMap ℚ ℝ)).val.det)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (z : UpperHalfPlane) :
    (rationalCommonCoverGLTrace N g f).1 ((rationalSL2Normalization g hg)⁻¹ • z) =
      rationalPrincipalTraceFunction N g⁻¹ hgi lam
        (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f) z := by
  let P := principalCongruenceGL N
  let S := P ⊓ rationalConjugateGroup N g⁻¹
  let fGL := integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f
  let F := rationalPulledCommonCoverGLInvariant N g⁻¹ fGL
  letI : (rationalConjugateGroup N g⁻¹).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N g⁻¹
  letI : S.IsFiniteRelIndex P := by
    apply Subgroup.IsFiniteRelIndex.mk
    change (P ⊓ rationalConjugateGroup N g⁻¹).relIndex P ≠ 0
    rw [Subgroup.inf_relIndex_left]
    exact Subgroup.relIndex_ne_zero (H := rationalConjugateGroup N g⁻¹) (K := P)
  have hsource : rationalPullbackConjugateGroup S g =
      P ⊓ rationalConjugateGroup N g := by
    simpa only [S, P] using rationalPullback_principal_inf_inverse_eq_commonCover N g
  have hfun : (rationalMaassPullbackInvariant_general S g F).1 =
      (rationalCommonCoverGLInvariant N g f).1 := by
    funext w
    change f.1.1 ((g⁻¹).map (algebraMap ℚ ℝ) •
      (g.map (algebraMap ℚ ℝ) • w)) = f.1.1 w
    rw [← mul_smul, ← Matrix.GeneralLinearGroup.map_mul]
    simp
  letI : (rationalPullbackConjugateGroup S g).IsFiniteRelIndex
      (rationalConjugateGroup N g) := by
    change (rationalPullbackConjugateGroup S g).IsFiniteRelIndex
      (rationalPullbackConjugateGroup P g)
    exact rationalPullback_isFiniteRelIndex S P g
  letI : (P ⊓ rationalConjugateGroup N g).IsFiniteRelIndex
      (rationalConjugateGroup N g) := by
    simpa only [P] using rationalCommonCoverGL_isFiniteRelIndex N g
  have hleft : maassTraceFunction (H := rationalConjugateGroup N g)
      (rationalMaassPullbackInvariant_general S g F) =
      (rationalCommonCoverGLTrace N g f).1 := by
    apply maassTraceFunction_congr_source (by rw [hsource])
    exact hfun
  have hright : maassTraceFunction (H := P) F =
      rationalPrincipalTraceFunction N g⁻¹ hgi lam fGL := by
    change maassTraceFunction (H := P) F =
      maassTraceFunction (H := P) (rationalMaassPullbackInvariant N g⁻¹ fGL)
    apply maassTraceFunction_congr_source
    · ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · exact fun hx => hx.2
      · intro hx
        exact ⟨x.property, hx⟩
    · rfl
  have hbase := maassTrace_rationalPullback_baseChange S P g F
  calc
    (rationalCommonCoverGLTrace N g f).1 ((rationalSL2Normalization g hg)⁻¹ • z) =
        maassTraceFunction (H := rationalConjugateGroup N g)
          (rationalMaassPullbackInvariant_general S g F)
            ((rationalSL2Normalization g hg)⁻¹ • z) :=
      (congrFun hleft ((rationalSL2Normalization g hg)⁻¹ • z)).symm
    _ = (rationalMaassPullbackInvariant_general P g
          (maassTraceInvariant (H := P) F)).1 ((rationalSL2Normalization g hg)⁻¹ • z) :=
      congrFun hbase ((rationalSL2Normalization g hg)⁻¹ • z)
    _ = maassTraceFunction (H := P) F z := by
      change maassTraceFunction (H := P) F
        (g.map (algebraMap ℚ ℝ) • ((rationalSL2Normalization g hg)⁻¹ • z)) = _
      rw [rationalSL2Normalization_inv_action_cancel]
    _ = rationalPrincipalTraceFunction N g⁻¹ hgi lam fGL z :=
      congrFun hright z

/-- The transported bounded quotient correspondence acts on the literal Maass
source by the inverse formal principal trace after both are realized in the
actual quotient `L²` space. -/
theorem rationalHeckePrincipalLpEndomorphism_source_eq_toLpLinear_inverseTrace
    (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hgi : 0 < ((g⁻¹).map (algebraMap ℚ ℝ)).val.det)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    rationalHeckePrincipalLpEndomorphism N g hg (MaassQuotientL2.sourceLp N f) =
      PrincipalMaassEigenspaceL2.toLpLinear N
        (rationalPrincipalTraceLinear N g⁻¹ hgi lam
          (principalMaassCuspEigenformToHeckeEigenspace N lam f)) := by
  apply Lp.ext
  filter_upwards [rationalHeckePrincipalLpEndomorphism_source_ae_glTraceQuotientLift
      N g hg f,
    PrincipalMaassEigenspaceL2.toLp_ae N
      (rationalPrincipalTraceLinear N g⁻¹ hgi lam
        (principalMaassCuspEigenformToHeckeEigenspace N lam f))] with q hleft hright
  rw [hleft]
  change maassInvariantQuotientLift (rationalConjugateSL2Group N g)
      (rationalCommonCoverGLTraceSLInvariant N g f)
      (rationalSL2ConjugateQuotientEquiv N g hg q) =
    PrincipalMaassEigenspaceL2.toLp N
      (rationalPrincipalTraceLinear N g⁻¹ hgi lam
        (principalMaassCuspEigenformToHeckeEigenspace N lam f)) q
  rw [hright]
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [rationalSL2ConjugateQuotientEquiv_mk, maassInvariantQuotientLift_mk]
  change (rationalCommonCoverGLTrace N g f).1
      ((x * rationalSL2Normalization g hg)⁻¹ • UpperHalfPlane.I) =
    (rationalPrincipalTraceLinear N g⁻¹ hgi lam
      (principalMaassCuspEigenformToHeckeEigenspace N lam f)).1
        (x⁻¹ • UpperHalfPlane.I)
  rw [_root_.mul_inv_rev, mul_smul]
  change (rationalCommonCoverGLTrace N g f).1
      ((rationalSL2Normalization g hg)⁻¹ • (x⁻¹ • UpperHalfPlane.I)) =
    rationalPrincipalTraceFunction N g⁻¹ hgi lam
      (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f)
        (x⁻¹ • UpperHalfPlane.I)
  exact rationalCommonCoverGLTrace_normalization_inverse_eq_principalTrace N g hg hgi f
    (x⁻¹ • UpperHalfPlane.I)

/-- The completed rational correspondence agrees with the inverse formal
principal trace on the entire zero-inclusive principal Maass eigenspace in
the quotient `L²` realization. -/
theorem rationalHeckePrincipalLpEndomorphism_toLpLinear_eq_inverseTrace
    (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hgi : 0 < ((g⁻¹).map (algebraMap ℚ ℝ)).val.det)
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    rationalHeckePrincipalLpEndomorphism N g hg
      (PrincipalMaassEigenspaceL2.toLpLinear N u) =
      PrincipalMaassEigenspaceL2.toLpLinear N
        (rationalPrincipalTraceLinear N g⁻¹ hgi lam u) := by
  by_cases hu : u = 0
  · subst u
    simp only [LinearMap.map_zero, ContinuousLinearMap.map_zero]
  · let f := PrincipalMaassEigenspaceL2.toMaassCuspEigenform N u hu
    have hrecover : principalMaassCuspEigenformToHeckeEigenspace N lam f = u := by
      apply Subtype.ext
      rfl
    have hsource : PrincipalMaassEigenspaceL2.toLpLinear N u =
        MaassQuotientL2.sourceLp N f := by
      rw [← hrecover]
      exact PrincipalMaassEigenspaceL2.toLpLinear_principalMaassCuspEigenform N f
    calc
      rationalHeckePrincipalLpEndomorphism N g hg
          (PrincipalMaassEigenspaceL2.toLpLinear N u) =
          rationalHeckePrincipalLpEndomorphism N g hg (MaassQuotientL2.sourceLp N f) := by
        rw [hsource]
      _ = PrincipalMaassEigenspaceL2.toLpLinear N
          (rationalPrincipalTraceLinear N g⁻¹ hgi lam
            (principalMaassCuspEigenformToHeckeEigenspace N lam f)) :=
        rationalHeckePrincipalLpEndomorphism_source_eq_toLpLinear_inverseTrace N g hg hgi f
      _ = PrincipalMaassEigenspaceL2.toLpLinear N
          (rationalPrincipalTraceLinear N g⁻¹ hgi lam u) := by
        rw [hrecover]

/-- Two completed rational correspondences satisfy the inverse-oriented formal
Mackey product on every vector of the actual principal Maass `L²` carrier. -/
theorem rationalHeckePrincipalLpEndomorphism_comp_toLpLinear_eq_inverseMackey
    (N : ℕ) {lam : ℝ} (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det)
    (hgi : 0 < ((g⁻¹).map (algebraMap ℚ ℝ)).val.det)
    (hhi : 0 < ((h⁻¹).map (algebraMap ℚ ℝ)).val.det)
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    rationalHeckePrincipalLpEndomorphism N h hh
      (rationalHeckePrincipalLpEndomorphism N g hg
        (PrincipalMaassEigenspaceL2.toLpLinear N u)) =
      PrincipalMaassEigenspaceL2.toLpLinear N
        (rationalPrincipalHeckeCosetFinsuppAction N lam
          (rationalMackeyHeckeCosetFormalProduct N g⁻¹ h⁻¹ hgi hhi) u) := by
  calc
    rationalHeckePrincipalLpEndomorphism N h hh
        (rationalHeckePrincipalLpEndomorphism N g hg
          (PrincipalMaassEigenspaceL2.toLpLinear N u)) =
        rationalHeckePrincipalLpEndomorphism N h hh
          (PrincipalMaassEigenspaceL2.toLpLinear N
            (rationalPrincipalTraceLinear N g⁻¹ hgi lam u)) := by
      rw [rationalHeckePrincipalLpEndomorphism_toLpLinear_eq_inverseTrace N g hg hgi u]
    _ = PrincipalMaassEigenspaceL2.toLpLinear N
        (rationalPrincipalTraceLinear N h⁻¹ hhi lam
          (rationalPrincipalTraceLinear N g⁻¹ hgi lam u)) :=
      rationalHeckePrincipalLpEndomorphism_toLpLinear_eq_inverseTrace N h hh hhi
        (rationalPrincipalTraceLinear N g⁻¹ hgi lam u)
    _ = PrincipalMaassEigenspaceL2.toLpLinear N
        (rationalPrincipalHeckeCosetFinsuppAction N lam
          (rationalMackeyHeckeCosetFormalProduct N g⁻¹ h⁻¹ hgi hhi) u) := by
      rw [rationalMackeyHeckeCosetFormalProduct_action]
      rfl


end

end GaloisForLFunctions.RHTower
