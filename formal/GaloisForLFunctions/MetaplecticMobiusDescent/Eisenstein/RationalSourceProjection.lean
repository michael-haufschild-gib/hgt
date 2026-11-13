/-
The rational source projection adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.ResidualGaussFactorization
import GaloisForLFunctions.MetaplecticMobiusDescent.Reciprocity.RationalKubotaCharacter

/-!
# The rational source projection

Finite averaging transfers the cubic character to the rational extension of the level-three
kernel. The rational pullbacks `kernelRationalPullback` are isometries, and the projected
residual vector `cubicSourceResidualFunction` carries the opposite-cusp data `OppositeData`.
Analytic continuation identifies the unramified Gauss residues `unramifiedGaussResidue`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource

/-- The level-three subgroup inside its rational extension. -/
def levelThreeInRationalExtension : Subgroup rationalExtension :=
  levelThree.comap rationalExtension.subtype

instance levelThreeInRationalExtension_normal : levelThreeInRationalExtension.Normal where
  conj_mem n hn g := (levelThreeConjugate (g : SL(2, O)) ⟨(n : SL(2, O)), hn⟩).property

instance levelThreeInRationalExtension_finiteIndex : levelThreeInRationalExtension.FiniteIndex := by
  letI : levelThree.FiniteIndex := levelThree_finiteIndex
  change (levelThree.subgroupOf rationalExtension).FiniteIndex
  infer_instance

def rationalSourceLift : SL(2, ℤ) →* rationalExtension where
  toFun r := ⟨rationalEmbedding r, rational_mem_rationalExtension r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

def rationalSourceQuotient : SL(2, ℤ) →* (rationalExtension ⧸ levelThreeInRationalExtension) :=
  (QuotientGroup.mk' levelThreeInRationalExtension).comp rationalSourceLift

lemma rationalSourceQuotient_surjective : Function.Surjective rationalSourceQuotient := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective levelThreeInRationalExtension q
  obtain ⟨n, r, hr⟩ := g.property
  refine ⟨r, ?_⟩
  let n' : rationalExtension := ⟨(n : SL(2, O)), levelThree_le_rationalExtension n.property⟩
  have hg : g = n' * rationalSourceLift r := Subtype.ext hr.symm
  have hn : QuotientGroup.mk' levelThreeInRationalExtension n' = 1 :=
    (QuotientGroup.eq_one_iff n').mpr n.property
  change QuotientGroup.mk' levelThreeInRationalExtension (rationalSourceLift r) = _
  rw [hg, map_mul, hn, one_mul]

instance rationalSourceQuotientFintype : Fintype (rationalExtension ⧸ levelThreeInRationalExtension) :=
  Fintype.ofFinite _

/-- Every source coset has a rational representative, on which the character is trivial. -/
def rationalSourceSection (q : rationalExtension ⧸ levelThreeInRationalExtension) : SL(2, ℤ) :=
  (rationalSourceQuotient_surjective q).choose

lemma rationalSourceSection_spec (q : rationalExtension ⧸ levelThreeInRationalExtension) :
    rationalSourceQuotient (rationalSourceSection q) = q :=
  (rationalSourceQuotient_surjective q).choose_spec

lemma extendedComplexCharacter_sourceLift (r : SL(2, ℤ)) :
    extendedComplexCharacter (rationalSourceLift r) = 1 := extendedComplexCharacter_rational r

/-- Normalized finite averaging transfers the cubic character to the rational extension. -/
def rationalSourceProjection (f : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  (Fintype.card (rationalExtension ⧸ levelThreeInRationalExtension) : ℂ)⁻¹ *
    ∑ q : rationalExtension ⧸ levelThreeInRationalExtension,
      f (integralComplexMatrix (rationalEmbedding (rationalSourceSection q)) • w)

lemma rationalSourceSection_translate (f : HyperbolicSpace → ℂ)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w)
    (q : rationalExtension ⧸ levelThreeInRationalExtension) (g : rationalExtension) (w : HyperbolicSpace) :
    f (integralComplexMatrix (rationalEmbedding (rationalSourceSection q)) •
      (integralComplexMatrix (g : SL(2, O)) • w)) = extendedComplexCharacter g *
      f (integralComplexMatrix (rationalEmbedding (rationalSourceSection
        (q * QuotientGroup.mk' levelThreeInRationalExtension g))) • w) := by
  let r := rationalSourceSection q
  let s := rationalSourceSection (q * QuotientGroup.mk' levelThreeInRationalExtension g)
  let m : rationalExtension := rationalSourceLift r * g * (rationalSourceLift s)⁻¹
  have hm : m ∈ levelThreeInRationalExtension := by
    apply (QuotientGroup.eq_one_iff (N := levelThreeInRationalExtension) m).mp
    change QuotientGroup.mk' levelThreeInRationalExtension
      (rationalSourceLift r * g * (rationalSourceLift s)⁻¹) = 1
    rw [map_mul, map_mul, map_inv]
    change rationalSourceQuotient r * QuotientGroup.mk' levelThreeInRationalExtension g *
      (rationalSourceQuotient s)⁻¹ = 1
    rw [rationalSourceSection_spec, rationalSourceSection_spec, mul_inv_cancel]
  let n : levelThree := ⟨(m : SL(2, O)), hm⟩
  have hchar : complexCharacter n = extendedComplexCharacter g := by
    rw [← extendedComplexCharacter_restrict n]
    change extendedComplexCharacter (rationalSourceLift r * g * (rationalSourceLift s)⁻¹) = _
    rw [map_mul, map_mul, ← map_inv rationalSourceLift,
      extendedComplexCharacter_sourceLift, extendedComplexCharacter_sourceLift, one_mul, mul_one]
  have he : rationalEmbedding r * (g : SL(2, O)) = (n : SL(2, O)) * rationalEmbedding s := by
    change _ = (rationalEmbedding r * (g : SL(2, O)) * (rationalEmbedding s)⁻¹) * rationalEmbedding s
    group
  change f (integralComplexMatrix (rationalEmbedding r) •
    (integralComplexMatrix (g : SL(2, O)) • w)) =
      extendedComplexCharacter g * f (integralComplexMatrix (rationalEmbedding s) • w)
  rw [← mul_smul, ← map_mul, he, map_mul, integralComplexMatrix_levelThree, mul_smul, hf, hchar]

theorem rationalSourceProjection_automorphy (f : HyperbolicSpace → ℂ)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w)
    (g : rationalExtension) (w : HyperbolicSpace) :
    rationalSourceProjection f (integralComplexMatrix (g : SL(2, O)) • w) =
      extendedComplexCharacter g * rationalSourceProjection f w := by
  unfold rationalSourceProjection
  simp_rw [rationalSourceSection_translate f hf]
  rw [← Finset.mul_sum]
  rw [Function.Bijective.sum_comp
    (Group.mulRight_bijective (QuotientGroup.mk' levelThreeInRationalExtension g))
    (fun q => f (integralComplexMatrix (rationalEmbedding (rationalSourceSection q)) • w))]
  ring

lemma rationalSourceProjection_fixed (f : HyperbolicSpace → ℂ)
    (hf : ∀ g : rationalExtension, ∀ w,
      f (integralComplexMatrix (g : SL(2, O)) • w) = extendedComplexCharacter g * f w)
    (w : HyperbolicSpace) : rationalSourceProjection f w = f w := by
  have he (q : rationalExtension ⧸ levelThreeInRationalExtension) :
      f (integralComplexMatrix (rationalEmbedding (rationalSourceSection q)) • w) = f w := by
    have h := hf (rationalSourceLift (rationalSourceSection q)) w
    rw [extendedComplexCharacter_sourceLift, one_mul] at h
    exact h
  have hc : (Fintype.card (rationalExtension ⧸ levelThreeInRationalExtension) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [rationalSourceProjection, he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hc _

lemma rationalSourceProjection_idempotent (f : HyperbolicSpace → ℂ)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w) :
    rationalSourceProjection (rationalSourceProjection f) = rationalSourceProjection f := by
  funext w
  exact rationalSourceProjection_fixed _ (rationalSourceProjection_automorphy f hf) w

lemma rationalSourceProjection_continuous (f : HyperbolicSpace → ℂ) (hf : Continuous f) :
    Continuous (rationalSourceProjection f) := by
  apply continuous_const.mul
  apply continuous_finsetSum
  intro q hq
  exact hf.comp (continuous_hyperbolic_action _)

/-- The residual vector projected to the rational extension of the cubic group. -/
def cubicSourceResidualFunction : HyperbolicSpace → ℂ := rationalSourceProjection cubicResidualFunction

lemma cubicSourceResidualFunction_continuous : Continuous cubicSourceResidualFunction :=
  rationalSourceProjection_continuous _ cubicResidualFunction_continuous

theorem cubicSourceResidualFunction_automorphy (g : rationalExtension) (w : HyperbolicSpace) :
    cubicSourceResidualFunction (integralComplexMatrix (g : SL(2, O)) • w) =
      extendedComplexCharacter g * cubicSourceResidualFunction w :=
  rationalSourceProjection_automorphy _ cubicResidualFunction_automorphy g w

theorem cubicSourceResidualFunction_rational (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    cubicSourceResidualFunction (integralComplexMatrix (rationalEmbedding r) • w) =
      cubicSourceResidualFunction w := by
  have h := cubicSourceResidualFunction_automorphy (rationalSourceLift r) w
  rw [extendedComplexCharacter_sourceLift, one_mul] at h
  exact h

/-- Conjugation by the rational extension preserves the metaplectic kernel. -/
def kernelRationalConjugate (g : rationalExtension) : globalKubotaKernel ≃* globalKubotaKernel where
  toFun n := ⟨(g : SL(2, O)) * (n : SL(2, O)) * (g : SL(2, O))⁻¹,
    globalKubotaKernel_conjugate g n n.property⟩
  invFun n := ⟨(g⁻¹ : rationalExtension) * (n : SL(2, O)) * (g⁻¹ : rationalExtension)⁻¹,
    globalKubotaKernel_conjugate g⁻¹ n n.property⟩
  left_inv n := by apply Subtype.ext; simp only [Subgroup.coe_inv, inv_inv]; group
  right_inv n := by apply Subtype.ext; simp only [Subgroup.coe_inv, inv_inv]; group
  map_mul' n m := by apply Subtype.ext; simp only [Subgroup.coe_mul]; group

lemma rational_action_respects_kernel (g : rationalExtension) (u v : HyperbolicSpace)
    (h : (integralOrbitRel globalKubotaKernel).r u v) :
    (integralOrbitRel globalKubotaKernel).r
      (integralComplexMatrix (g : SL(2, O)) • u) (integralComplexMatrix (g : SL(2, O)) • v) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨kernelRationalConjugate g n, ?_⟩
  change integralComplexMatrix ((g : SL(2, O)) * (n : SL(2, O)) * (g : SL(2, O))⁻¹) •
    (integralComplexMatrix (g : SL(2, O)) • u) = integralComplexMatrix (g : SL(2, O)) • v
  rw [map_mul, map_mul, map_inv, mul_smul, mul_smul, inv_smul_smul, hn]

def kernelRationalAction (g : rationalExtension) : KernelQuotient → KernelQuotient :=
  Quotient.map' (fun w => integralComplexMatrix (g : SL(2, O)) • w) (rational_action_respects_kernel g)

lemma kernelRationalAction_mk (g : rationalExtension) (w : HyperbolicSpace) :
    kernelRationalAction g (integralOrbitProjection globalKubotaKernel w) =
      integralOrbitProjection globalKubotaKernel (integralComplexMatrix (g : SL(2, O)) • w) := rfl

lemma kernelRationalAction_continuous (g : rationalExtension) : Continuous (kernelRationalAction g) :=
  (continuous_hyperbolic_action (integralComplexMatrix (g : SL(2, O)))).quotient_map'
    (rational_action_respects_kernel g)

lemma kernelRationalAction_fundamentalDomain (g : rationalExtension) :
    IsFundamentalDomain globalKubotaKernel
      ((fun w : HyperbolicSpace => integralComplexMatrix (g : SL(2, O)) • w) ''
        hyperbolicFundamentalSet globalKubotaKernel) hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain globalKubotaKernel
    globalKubotaKernel_le_levelThree hyperbolicVolume).image_of_equiv
    (MulAction.toPerm (integralComplexMatrix (g : SL(2, O))))
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm (integralComplexMatrix (g : SL(2, O)))).symm
      hyperbolicVolume hyperbolicVolume from
      (measurePreserving_smul (integralComplexMatrix (g : SL(2, O)))⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    (kernelRationalConjugate g⁻¹).toEquiv
  intro n w
  change integralComplexMatrix (g : SL(2, O)) •
    (integralComplexMatrix ((g⁻¹ : rationalExtension) * (n : SL(2, O)) * (g⁻¹ : rationalExtension)⁻¹) • w) =
      integralComplexMatrix (n : SL(2, O)) • (integralComplexMatrix (g : SL(2, O)) • w)
  simp only [Subgroup.coe_inv, map_mul, map_inv, inv_inv, mul_smul, smul_inv_smul]

/-- The finite rational action preserves quotient volume, hence its pullback is an isometry. -/
lemma kernelRationalAction_measurePreserving (g : rationalExtension) :
    MeasurePreserving (kernelRationalAction g) (integralQuotientVolume globalKubotaKernel)
      (integralQuotientVolume globalKubotaKernel) := by
  refine ⟨(kernelRationalAction_continuous g).measurable, ?_⟩
  let act : HyperbolicSpace → HyperbolicSpace := fun w => integralComplexMatrix (g : SL(2, O)) • w
  have hmap := (measurePreserving_smul (integralComplexMatrix (g : SL(2, O))) hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul _) (hyperbolicFundamentalSet globalKubotaKernel)
  have heq : kernelRationalAction g ∘ integralOrbitProjection globalKubotaKernel =
      integralOrbitProjection globalKubotaKernel ∘ act := rfl
  change Measure.map (kernelRationalAction g)
    (Measure.map (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel))) = _
  rw [Measure.map_map (kernelRationalAction_continuous g).measurable
    (measurable_integralOrbitProjection _), heq,
    ← Measure.map_map (measurable_integralOrbitProjection _) (continuous_hyperbolic_action _).measurable]
  change Measure.map (integralOrbitProjection globalKubotaKernel)
    (Measure.map act (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel))) = _
  rw [hmap.map_eq]
  exact integralQuotientVolume_independent globalKubotaKernel globalKubotaKernel_le_levelThree _
    (kernelRationalAction_fundamentalDomain g)

def kernelRationalPullback (g : rationalExtension) : KernelQuotientL2 →ₗᵢ[ℂ] KernelQuotientL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (kernelRationalAction g) (kernelRationalAction_measurePreserving g)

lemma kernelRationalPullback_ae (g : rationalExtension) (F : KernelQuotientL2) :
    kernelRationalPullback g F =ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => F (kernelRationalAction g q) :=
  Lp.coeFn_compMeasurePreserving F (kernelRationalAction_measurePreserving g)

/-- The same rational average on the actual quotient Hilbert space. -/
def kernelRationalSourceProjection : KernelQuotientL2 →L[ℂ] KernelQuotientL2 :=
  (Fintype.card (rationalExtension ⧸ levelThreeInRationalExtension) : ℂ)⁻¹ •
    ∑ q : rationalExtension ⧸ levelThreeInRationalExtension,
      (kernelRationalPullback (rationalSourceLift (rationalSourceSection q))).toContinuousLinearMap

lemma kernelRationalSourceProjection_apply (F : KernelQuotientL2) :
    kernelRationalSourceProjection F =
      (Fintype.card (rationalExtension ⧸ levelThreeInRationalExtension) : ℂ)⁻¹ •
        ∑ q : rationalExtension ⧸ levelThreeInRationalExtension,
          kernelRationalPullback (rationalSourceLift (rationalSourceSection q)) F := by
  simp only [kernelRationalSourceProjection, smul_apply, _root_.sum_apply]
  rfl

lemma kernelRationalSourceProjection_ae (F : KernelQuotientL2) :
    kernelRationalSourceProjection F =ᵐ[integralQuotientVolume globalKubotaKernel]
      fun x => (Fintype.card (rationalExtension ⧸ levelThreeInRationalExtension) : ℂ)⁻¹ *
        ∑ q : rationalExtension ⧸ levelThreeInRationalExtension,
          F (kernelRationalAction (rationalSourceLift (rationalSourceSection q)) x) := by
  let c : ℂ := (Fintype.card (rationalExtension ⧸ levelThreeInRationalExtension) : ℂ)⁻¹
  let A (q : rationalExtension ⧸ levelThreeInRationalExtension) : KernelQuotientL2 :=
    kernelRationalPullback (rationalSourceLift (rationalSourceSection q)) F
  have he : kernelRationalSourceProjection F = c • ∑ q, A q := kernelRationalSourceProjection_apply F
  rw [he]
  have hall := ae_all_iff.mpr (fun q => kernelRationalPullback_ae
    (rationalSourceLift (rationalSourceSection q)) F)
  filter_upwards [Lp.coeFn_smul c (∑ q, A q), Lp.coeFn_fun_finsetSum Finset.univ A, hall] with x hc hs hx
  rw [hc, Pi.smul_apply, smul_eq_mul, hs]
  change c * ∑ q, A q x = _
  congr 1
  exact Finset.sum_congr rfl (fun q _ => hx q)

lemma rationalSourceProjection_congr_ae (f g : HyperbolicSpace → ℂ)
    (h : f =ᵐ[hyperbolicVolume] g) :
    rationalSourceProjection f =ᵐ[hyperbolicVolume] rationalSourceProjection g := by
  have hall := ae_all_iff.mpr (fun q : rationalExtension ⧸ levelThreeInRationalExtension =>
    (measurePreserving_smul (integralComplexMatrix (rationalEmbedding (rationalSourceSection q)))
      hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp h)
  filter_upwards [hall] with w hw
  unfold rationalSourceProjection
  congr 1
  exact Finset.sum_congr rfl (fun q _ => hw q)

lemma kernelRationalSourceProjection_representative (F : KernelQuotientL2) (f : HyperbolicSpace → ℂ)
    (hf : (fun w => F (integralOrbitProjection globalKubotaKernel w)) =ᵐ[hyperbolicVolume] f) :
    (fun w => kernelRationalSourceProjection F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] rationalSourceProjection f := by
  have he := kernelProjection_quasiMeasurePreserving.ae_eq_comp (kernelRationalSourceProjection_ae F)
  change (fun w => kernelRationalSourceProjection F (integralOrbitProjection globalKubotaKernel w))
    =ᵐ[hyperbolicVolume] rationalSourceProjection (fun w => F (integralOrbitProjection globalKubotaKernel w)) at he
  exact he.trans (rationalSourceProjection_congr_ae _ _ hf)

theorem cubicSourceResidualFunction_represents_projection :
    (fun w => kernelRationalSourceProjection cubicEisensteinResidue
      (integralOrbitProjection globalKubotaKernel w)) =ᵐ[hyperbolicVolume] cubicSourceResidualFunction :=
  kernelRationalSourceProjection_representative _ _ cubicEisensteinResidue_continuous_representative

/-- Finite averaging of isometries is a contraction on the actual quotient space. -/
theorem kernelRationalSourceProjection_norm_le (F : KernelQuotientL2) :
    ‖kernelRationalSourceProjection F‖ ≤ ‖F‖ := by
  have hc : 0 < (Fintype.card (rationalExtension ⧸ levelThreeInRationalExtension) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  rw [kernelRationalSourceProjection_apply, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card (rationalExtension ⧸ levelThreeInRationalExtension) : ℝ)⁻¹ *
        ∑ q : rationalExtension ⧸ levelThreeInRationalExtension,
          ‖kernelRationalPullback (rationalSourceLift (rationalSourceSection q)) F‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hc.le)
    _ = ‖F‖ := by
      simp only [LinearIsometry.norm_map, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact inv_mul_cancel_left₀ hc.ne' _

/-- Rational upper translations act on the actual cusp rows by conjugation. -/
def rationalUnipotent (t : ℤ) : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

lemma rationalUnipotent_neg (t : ℤ) : rationalUnipotent (-t) = (rationalUnipotent t)⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalUnipotent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

lemma rationalUnipotent_embedding (t : ℤ) :
    (rationalEmbedding (rationalUnipotent t) : Matrix (Fin 2) (Fin 2) O) = !![1, (t : O); 0, 1] := by
  apply Matrix.ext
  intro i j
  change (Int.castRingHom O) ((!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j) = _
  fin_cases i <;> fin_cases j <;> simp

lemma row_unipotent_conjugate (t : ℤ) (M : levelThree) :
    row (levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M) =
      Matrix.vecMul (row M) (rationalEmbedding (rationalUnipotent t) : SL(2, O)) := by
  change ((rationalEmbedding (rationalUnipotent (-t)) * (M : SL(2, O)) *
      (rationalEmbedding (rationalUnipotent (-t)))⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) 1 = _
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    rationalUnipotent_embedding, Matrix.adjugate_fin_two]
  funext j
  fin_cases j <;> simp [row, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

def cuspUnipotentTranslate (t : ℤ) : CuspCosets → CuspCosets :=
  Quotient.map (fun M => levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M) (by
    intro M N h
    change row (levelThreeConjugate _ M) = row (levelThreeConjugate _ N)
    rw [row_unipotent_conjugate, row_unipotent_conjugate, show row M = row N from h])

lemma cuspUnipotentTranslate_inverse (t : ℤ) (x : CuspCosets) :
    cuspUnipotentTranslate (-t) (cuspUnipotentTranslate t x) = x := by
  induction x using Quotient.inductionOn with
  | _ M =>
    change cosetOf (levelThreeConjugate (rationalEmbedding (rationalUnipotent (- -t)))
      (levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M)) = cosetOf M
    rw [neg_neg, rationalUnipotent_neg, map_inv, ← levelThreeConjugate_mul,
      mul_inv_cancel, levelThreeConjugate_one]

def cuspUnipotentEquiv (t : ℤ) : CuspCosets ≃ CuspCosets where
  toFun := cuspUnipotentTranslate t
  invFun := cuspUnipotentTranslate (-t)
  left_inv := cuspUnipotentTranslate_inverse t
  right_inv x := by simpa only [neg_neg] using cuspUnipotentTranslate_inverse (-t) x

lemma cosetRow_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    cosetRow (cuspUnipotentEquiv t x) =
      Matrix.vecMul (cosetRow x) (rationalEmbedding (rationalUnipotent t) : SL(2, O)) := by
  induction x using Quotient.inductionOn with
  | _ M => exact row_unipotent_conjugate t M

lemma cosetCharacter_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    cosetCharacter (cuspUnipotentEquiv t x) = cosetCharacter x := by
  induction x using Quotient.inductionOn with
  | _ M => exact complexCharacter_conjugate_rational (rationalUnipotent (-t)) M

lemma embeddedRow_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    embeddedRow (cuspUnipotentEquiv t x) = Matrix.vecMul (embeddedRow x)
      (integralComplexMatrix (rationalEmbedding (rationalUnipotent t)) : SL(2, ℂ)) := by
  funext j
  simp only [embeddedRow, Function.comp_def, cosetRow_cuspUnipotentEquiv,
    Matrix.vecMul, dotProduct, map_sum, map_mul]
  rfl

/-- Integral horizontal translation reindexes the series, without a convergence hypothesis. -/
theorem eisenstein_unipotent (t : ℤ) (g : SL(2, ℂ)) (s : ℂ) :
    eisenstein (integralComplexMatrix (rationalEmbedding (rationalUnipotent t)) * g) s = eisenstein g s := by
  have he (x : CuspCosets) :
      summand (integralComplexMatrix (rationalEmbedding (rationalUnipotent t)) * g) s x =
        summand g s (cuspUnipotentEquiv t x) := by
    rw [summand, summand, cosetCharacter_cuspUnipotentEquiv,
      embeddedRow_cuspUnipotentEquiv, ← rowOperator_apply, rowOperator_mul]
  unfold eisenstein
  simp_rw [he]
  exact (cuspUnipotentEquiv t).tsum_eq _

theorem hyperbolicEisenstein_unipotent (t : ℤ) (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (integralComplexMatrix (rationalEmbedding (rationalUnipotent t)) • w) =
      hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with
  | _ g => exact eisenstein_unipotent t g s

/-- The trivial bound counts the invertible residue classes. -/
lemma cubicUnitGaussSum_norm_le (h c : O) (hc : c ≠ 0) (hp : lambda ^ 2 ∣ c - 1) :
    ‖cubicUnitGaussSum h c‖ ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
  letI : Finite (O ⧸ Ideal.span {c}) := (Ideal.span {c}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr hc)
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  letI : Fintype (CubicUnitResidue c) := Fintype.ofFinite _
  have hnorm (r : CubicUnitResidue c) :
      ‖ringComplex (symbol (principalResidueRep c r.1) c) *
        residueAdditive (3 * h) c (principalResidueRep c r.1)‖ = 1 := by
    have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {c}) (principalResidueRep c r.1)) := by
      rw [principalResidueRep_spec]
      exact r.2
    rw [norm_mul, symbol_norm_one _ c hp ((isUnit_quotient_span_iff c _).mp hu).symm]
    simp only [residueAdditive, tracePhase_norm, one_mul]
  rw [cubicUnitGaussSum, tsum_fintype]
  calc
    _ ≤ ∑ r : CubicUnitResidue c,
        ‖ringComplex (symbol (principalResidueRep c r.1) c) *
          residueAdditive (3 * h) c (principalResidueRep c r.1)‖ := norm_sum_le _ _
    _ = (Fintype.card (CubicUnitResidue c) : ℝ) := by simp only [hnorm, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    _ ≤ (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) := by exact_mod_cast Fintype.card_subtype_le (IsUnit : (O ⧸ Ideal.span {c}) → Prop)
    _ = _ := by
      change (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = (Nat.card (O ⧸ Ideal.span {c}) : ℝ)
      rw [Nat.card_eq_fintype_card]

lemma unramifiedNormWeight_mul_norm (s : ℂ) (I : GoodIdeal) :
    ‖unramifiedNormWeight s I.1‖ * (Ideal.absNorm I.1 : ℝ) =
      ‖unramifiedNormWeight (s - 1) I.1‖ := by
  have hn : 0 < ‖ringComplex (primaryIdealGenerator I.1)‖ :=
    norm_pos_iff.mpr (ringComplex_ne_zero I.2)
  rw [norm_unramifiedNormWeight, norm_unramifiedNormWeight,
    ← primaryIdealGenerator_norm_sq I.1 I.2, ← Real.rpow_natCast _ 2,
    ← Real.rpow_add hn]
  congr 1
  simp only [Complex.sub_re, Complex.one_re, Nat.cast_ofNat]
  ring

/-- Absolute convergence holds in the same half-plane as the Eisenstein source. -/
theorem unramifiedCubicGaussSeries_summable_norm (s : ℂ) (hs : 2 < s.re) (h : O) :
    Summable (fun I : GoodIdeal =>
      ‖unramifiedNormWeight s I.1 * cubicUnitGaussSum h (primaryIdealGenerator I.1)‖) := by
  have hsum := (unramifiedNormWeight_summable_norm (s - 1) (by
    simp only [Complex.sub_re, Complex.one_re]; linarith)).subtype
      (fun I : Ideal O => primaryIdealGenerator I ≠ 0)
  apply hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  calc
    _ ≤ ‖unramifiedNormWeight s I.1‖ * (Ideal.absNorm I.1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hb := cubicUnitGaussSum_norm_le h (primaryIdealGenerator I.1) I.2
        (primaryIdealGenerator_spec I.1 I.2).2
      simpa only [(primaryIdealGenerator_spec I.1 I.2).1] using hb
    _ = _ := unramifiedNormWeight_mul_norm s I

/-- CRT on invertible classes, with no choice of compatible representatives. -/
def cubicUnitCRTEquiv (a b : O) (hab : IsCoprime a b) :
    CubicUnitResidue (a * b) ≃ CubicUnitResidue a × CubicUnitResidue b :=
  ((quotientProductEquiv a b hab).toEquiv.subtypeEquiv (fun q => by
    rw [← MulEquiv.isUnit_map (quotientProductEquiv a b hab) (x := q), Prod.isUnit_iff]
    rfl)).trans
      Equiv.subtypeProdEquivProd

lemma cubicUnitCRT_rep_left (a b : O) (hab : IsCoprime a b) (r : CubicUnitResidue (a * b)) :
    a ∣ principalResidueRep (a * b) r.1 - principalResidueRep a (cubicUnitCRTEquiv a b hab r).1.1 := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [principalResidueRep_spec]
  exact congrArg (fun x => (quotientProductEquiv a b hab x).1) (principalResidueRep_spec (a * b) r.1)

lemma cubicUnitCRT_rep_right (a b : O) (hab : IsCoprime a b) (r : CubicUnitResidue (a * b)) :
    b ∣ principalResidueRep (a * b) r.1 - principalResidueRep b (cubicUnitCRTEquiv a b hab r).2.1 := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [principalResidueRep_spec]
  exact congrArg (fun x => (quotientProductEquiv a b hab x).2) (principalResidueRep_spec (a * b) r.1)

lemma residueAdditive_unit_crt (h a b α β d : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hbez : α * b + β * a = 1) :
    residueAdditive (3 * h) (a * b) d =
      residueAdditive (3 * (h * α)) a d * residueAdditive (3 * (h * β)) b d := by
  unfold residueAdditive
  rw [← AddChar.map_add_eq_mul]
  congr 1
  have hae := ringComplex_ne_zero ha
  have hbe := ringComplex_ne_zero hb
  have he := congrArg ringComplex hbez
  simp only [map_add, map_mul, map_one] at he
  simp only [cuspFrequency, map_mul, map_ofNat]
  field_simp [hae, hbe, ringComplex_ne_zero traceLambda_ne_zero]
  linear_combination -(ringComplex h * ringComplex d) * he

lemma cubicUnitGaussSum_crt (h a b α β : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hbez : α * b + β * a = 1) :
    cubicUnitGaussSum h (a * b) = cubicUnitGaussSum (h * α) a * cubicUnitGaussSum (h * β) b := by
  have hab : IsCoprime a b := ⟨β, α, by linear_combination hbez⟩
  letI : Finite (O ⧸ Ideal.span {a}) := (Ideal.span {a}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr ha)
  letI : Finite (O ⧸ Ideal.span {b}) := (Ideal.span {b}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr hb)
  letI : Finite (O ⧸ Ideal.span {a * b}) := (Ideal.span {a * b}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha hb))
  letI : Fintype (CubicUnitResidue a) := Fintype.ofFinite _
  letI : Fintype (CubicUnitResidue b) := Fintype.ofFinite _
  letI : Fintype (CubicUnitResidue (a * b)) := Fintype.ofFinite _
  have hpoint (r : CubicUnitResidue (a * b)) :
      ringComplex (symbol (principalResidueRep (a * b) r.1) (a * b)) *
        residueAdditive (3 * h) (a * b) (principalResidueRep (a * b) r.1) =
      (ringComplex (symbol (principalResidueRep a (cubicUnitCRTEquiv a b hab r).1.1) a) *
        residueAdditive (3 * (h * α)) a (principalResidueRep a (cubicUnitCRTEquiv a b hab r).1.1)) *
      (ringComplex (symbol (principalResidueRep b (cubicUnitCRTEquiv a b hab r).2.1) b) *
        residueAdditive (3 * (h * β)) b (principalResidueRep b (cubicUnitCRTEquiv a b hab r).2.1)) := by
    rw [symbol_mul_denominator, map_mul, residueAdditive_unit_crt h a b α β _ ha hb hbez,
      symbol_congr (cubicUnitCRT_rep_left a b hab r), symbol_congr (cubicUnitCRT_rep_right a b hab r),
      residueAdditive_three_congr (h * α) a _ _ ha (cubicUnitCRT_rep_left a b hab r),
      residueAdditive_three_congr (h * β) b _ _ hb (cubicUnitCRT_rep_right a b hab r)]
    ring
  rw [cubicUnitGaussSum, cubicUnitGaussSum, cubicUnitGaussSum]
  calc
    _ = ∑' r : CubicUnitResidue (a * b),
        (ringComplex (symbol (principalResidueRep a (cubicUnitCRTEquiv a b hab r).1.1) a) *
          residueAdditive (3 * (h * α)) a (principalResidueRep a (cubicUnitCRTEquiv a b hab r).1.1)) *
        (ringComplex (symbol (principalResidueRep b (cubicUnitCRTEquiv a b hab r).2.1) b) *
          residueAdditive (3 * (h * β)) b (principalResidueRep b (cubicUnitCRTEquiv a b hab r).2.1)) := tsum_congr hpoint
    _ = ∑' r : CubicUnitResidue a × CubicUnitResidue b,
        (ringComplex (symbol (principalResidueRep a r.1.1) a) *
          residueAdditive (3 * (h * α)) a (principalResidueRep a r.1.1)) *
        (ringComplex (symbol (principalResidueRep b r.2.1) b) *
          residueAdditive (3 * (h * β)) b (principalResidueRep b r.2.1)) :=
      (cubicUnitCRTEquiv a b hab).tsum_eq (fun r : CubicUnitResidue a × CubicUnitResidue b =>
        (ringComplex (symbol (principalResidueRep a r.1.1) a) *
          residueAdditive (3 * (h * α)) a (principalResidueRep a r.1.1)) *
        (ringComplex (symbol (principalResidueRep b r.2.1) b) *
          residueAdditive (3 * (h * β)) b (principalResidueRep b r.2.1)))
    _ = _ := by
      simp only [tsum_fintype, Fintype.sum_prod_type]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]

/-- Coprime Gauss factors carry exactly the reciprocal cubic-symbol twist. -/
theorem cubicUnitGaussSum_coprime_product (h a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : IsCoprime a b) :
    cubicUnitGaussSum h (a * b) =
      ringComplex (symbol b a) * ringComplex (symbol a b) * cubicUnitGaussSum h a * cubicUnitGaussSum h b := by
  obtain ⟨β, α, hbez⟩ := hab
  have hbez' : α * b + β * a = 1 := by linear_combination hbez
  have hab' : IsCoprime a b := ⟨β, α, hbez⟩
  have hleft := cubicUnitGaussSum_frequency_twist (h * α) a b ha hab'
  have hright := cubicUnitGaussSum_frequency_twist (h * β) b a hb hab'.symm
  have hA : a ∣ (h * α) * b - h := ⟨-h * β, by linear_combination h * hbez'⟩
  have hB : b ∣ (h * β) * a - h := ⟨-h * α, by linear_combination h * hbez'⟩
  rw [cubicUnitGaussSum_frequency_congr _ h a ha hA] at hleft
  rw [cubicUnitGaussSum_frequency_congr _ h b hb hB] at hright
  rw [cubicUnitGaussSum_crt h a b α β ha hb hbez', ← hleft, ← hright]
  ring

/-- A reciprocal cubic twist is absorbed by the frequency `9ah`. -/
lemma cubicUnitGaussSum_ramified_twist (h a b : O) (hb : b ≠ 0)
    (hp : lambda ^ 2 ∣ b - 1) (hab : IsCoprime (3 * a) b) :
    ringComplex (symbol a b) * ringComplex (symbol (3 * a) b) * cubicUnitGaussSum h b =
      cubicUnitGaussSum (9 * h * a) b := by
  have ht : IsCoprime b (9 * a) := by
    have h3 := hab.of_mul_left_left
    have ha := hab.of_mul_left_right
    have hn : (9 : O) = 3 * 3 := by norm_num
    rw [hn]
    exact ((h3.mul_left h3).mul_left ha).symm
  have he := cubicUnitGaussSum_frequency_twist h b (9 * a) hb ht
  have hc : ringComplex (symbol a b) * ringComplex (symbol (3 * a) b) *
      ringComplex (symbol (9 * a) b) = 1 := by
    rw [← map_mul, ← map_mul, ← symbol_mul_numerator, ← symbol_mul_numerator]
    rw [show a * (3 * a) * (9 * a) = (3 * a) ^ 3 by ring,
      symbol_pow_numerator _ b hp, symbol_cube_of_isCoprime _ b hp hab, map_one]
  calc
    _ = (ringComplex (symbol a b) * ringComplex (symbol (3 * a) b)) *
        (ringComplex (symbol (9 * a) b) * cubicUnitGaussSum (h * (9 * a)) b) := by rw [he]
    _ = cubicUnitGaussSum (h * (9 * a)) b := by rw [← mul_assoc, hc, one_mul]
    _ = _ := by rw [show h * (9 * a) = 9 * h * a by ring]

/-- The ramified arithmetic factor changes only the unramified frequency. -/
theorem arithmeticResidueSum_ramified_gauss (h : O) (u : Oˣ) (n : ℕ) (hn : 2 ≤ n)
    (b : O) (hb : lambda ^ 2 ∣ b - 1) :
    arithmeticResidueSum h (((u : O) * lambda ^ n) * b) =
      arithmeticResidueSum h ((u : O) * lambda ^ n) *
        cubicUnitGaussSum (9 * h * ((u : O) * lambda ^ n)) b := by
  rw [arithmeticResidueSum_ramified_split h u n hn b hb]
  have he := cubicUnitGaussSum_ramified_twist h ((u : O) * lambda ^ n) b
    (primary_ne_zero b hb) hb (ramified_primary_coprime u n b hb)
  rw [← he]
  ring

lemma ramifiedLower_norm_sq (u : Oˣ) (n : ℕ) (I : GoodIdeal) :
    ‖ringComplex (ramifiedLower u n I)‖ ^ 2 = ((3 ^ (n + 2) * Ideal.absNorm I.1 : ℕ) : ℝ) := by
  rw [ringComplex_norm_sq_eq_absNorm_span]
  unfold ramifiedLower
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul, ramifiedElement_absNorm,
    (primaryIdealGenerator_spec I.1 I.2).1]

lemma arithmeticDirichletTerm_ramified_gauss (s : ℂ) (h : O) (u : Oˣ) (n : ℕ) (I : GoodIdeal) :
    arithmeticDirichletTerm s h (ramifiedLowerMap (u, n, I)).1 =
      (((3 ^ (n + 2) : ℕ) : ℂ) ^ (-s) * arithmeticResidueSum h ((u : O) * lambda ^ (n + 2))) *
        (unramifiedNormWeight s I.1 *
          cubicUnitGaussSum (9 * h * ((u : O) * lambda ^ (n + 2))) (primaryIdealGenerator I.1)) := by
  change arithmeticDirichletTerm s h ⟨ramifiedLower u n I, ramifiedLower_level u n I⟩ = _
  rw [arithmeticDirichletTerm, if_neg (ramifiedLower_ne_zero u n I)]
  have hweight : ((‖ringComplex (ramifiedLower u n I)‖ ^ 2 : ℝ) : ℂ) ^ (-s) =
      ((3 ^ (n + 2) : ℕ) : ℂ) ^ (-s) * unramifiedNormWeight s I.1 := by
    rw [unramifiedNormWeight_of_good s I.1 I.2, ramifiedLower_norm_sq, Complex.ofReal_natCast, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _
  dsimp only at *
  rw [hweight]
  dsimp only [ramifiedLower]
  rw [arithmeticResidueSum_ramified_gauss h u (n + 2) (by omega) _ (primaryIdealGenerator_spec I.1 I.2).2]
  ring

/-- Exact finite Gauss-series decomposition of each nonconstant scattering mode. -/
theorem arithmeticDirichletSeries_finite_gauss (s : ℂ) (hs : 2 < s.re) (h : O) (hh : h ≠ 0) :
    arithmeticDirichletSeries s h =
      ∑' u : Oˣ, ∑ n ∈ Finset.range (ramifiedFrequencyBound h + 1),
        (((3 ^ (n + 2) : ℕ) : ℂ) ^ (-s) * arithmeticResidueSum h ((u : O) * lambda ^ (n + 2))) *
          unramifiedCubicGaussSeries s (9 * h * ((u : O) * lambda ^ (n + 2))) := by
  rw [arithmeticDirichletSeries_finite_ramified s hs h hh]
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro n hn
  rw [unramifiedCubicGaussSeries, ← tsum_mul_left]
  exact tsum_congr (fun I => arithmeticDirichletTerm_ramified_gauss s h u n I)

/-- Translation by a multiple of the base preserves units modulo every positive power. -/
def cubicUnitPowerShift (p : O) (n : ℕ) (w : O)
    (r : CubicUnitResidue (p ^ (n + 1))) : CubicUnitResidue (p ^ (n + 1)) :=
  ⟨Ideal.Quotient.mk (Ideal.span {p ^ (n + 1)}) (principalResidueRep _ r.1 + p * w), by
    apply (isUnit_quotient_span_iff _ _).mpr
    have hcop : IsCoprime (p ^ (n + 1)) (principalResidueRep _ r.1) := by
      apply (isUnit_quotient_span_iff _ _).mp
      rw [principalResidueRep_spec]
      exact r.2
    obtain ⟨a, b, hab⟩ := hcop
    have hbase : IsCoprime p (principalResidueRep (p ^ (n + 1)) r.1 + p * w) := by
      refine ⟨a * p ^ n - b * w, b, ?_⟩
      linear_combination hab - a * (pow_succ p n)
    exact hbase.pow_left⟩

lemma cubicUnitPowerShift_injective (p : O) (n : ℕ) (w : O) :
    Function.Injective (cubicUnitPowerShift p n w) := by
  intro r t hrt
  apply Subtype.ext
  have he := congrArg Subtype.val hrt
  change Ideal.Quotient.mk (Ideal.span {p ^ (n + 1)}) (principalResidueRep _ r.1 + p * w) =
    Ideal.Quotient.mk (Ideal.span {p ^ (n + 1)}) (principalResidueRep _ t.1 + p * w) at he
  simp only [map_add, principalResidueRep_spec] at he
  exact add_right_cancel he

lemma cubicUnitPowerShift_rep (p : O) (n : ℕ) (w : O) (r : CubicUnitResidue (p ^ (n + 1))) :
    p ^ (n + 1) ∣ principalResidueRep _ (cubicUnitPowerShift p n w r).1 -
      (principalResidueRep _ r.1 + p * w) := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  exact principalResidueRep_spec _ _

lemma cubicUnitGaussSum_power_eigen (h p : O) (hp : p ≠ 0) (n : ℕ) (w : O) :
    residueAdditive (3 * h) (p ^ (n + 1)) (p * w) * cubicUnitGaussSum h (p ^ (n + 1)) =
      cubicUnitGaussSum h (p ^ (n + 1)) := by
  letI : Finite (O ⧸ Ideal.span {p ^ (n + 1)}) := (Ideal.span {p ^ (n + 1)}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ hp))
  let e : CubicUnitResidue (p ^ (n + 1)) ≃ CubicUnitResidue (p ^ (n + 1)) :=
    Equiv.ofBijective (cubicUnitPowerShift p n w)
      ⟨cubicUnitPowerShift_injective p n w, Finite.surjective_of_injective (cubicUnitPowerShift_injective p n w)⟩
  have hrep (r : CubicUnitResidue (p ^ (n + 1))) :
      p ^ (n + 1) ∣ principalResidueRep _ (e r).1 - (principalResidueRep _ r.1 + p * w) :=
    cubicUnitPowerShift_rep p n w r
  have hs (r : CubicUnitResidue (p ^ (n + 1))) :
      symbol (principalResidueRep _ (e r).1) (p ^ (n + 1)) =
        symbol (principalResidueRep _ r.1) (p ^ (n + 1)) := by
    rw [symbol_congr (hrep r), symbol_pow_denominator, symbol_pow_denominator]
    congr 1
    exact symbol_congr ⟨w, by ring⟩
  unfold cubicUnitGaussSum
  rw [← tsum_mul_left]
  calc
    _ = ∑' r : CubicUnitResidue (p ^ (n + 1)),
        ringComplex (symbol (principalResidueRep _ (e r).1) (p ^ (n + 1))) *
          residueAdditive (3 * h) (p ^ (n + 1)) (principalResidueRep _ (e r).1) := by
      apply tsum_congr
      intro r
      rw [hs, residueAdditive_three_congr h _ _ _ (pow_ne_zero _ hp) (hrep r),
        residueAdditive_add]
      ring
    _ = _ := e.tsum_eq (fun r : CubicUnitResidue (p ^ (n + 1)) =>
      ringComplex (symbol (principalResidueRep _ r.1) (p ^ (n + 1))) *
        residueAdditive (3 * h) (p ^ (n + 1)) (principalResidueRep _ r.1))

/-- A Gauss sum modulo `p^(n+1)` is supported on frequencies divisible by `p^n`. -/
theorem cubicUnitGaussSum_power_support (h p : O) (hp : p ≠ 0) (n : ℕ)
    (hG : cubicUnitGaussSum h (p ^ (n + 1)) ≠ 0) : p ^ n ∣ h := by
  have hp' := ringComplex_ne_zero hp
  have hphase (w : O) : residueAdditive (3 * h) (p ^ (n + 1)) (p * w) = 1 :=
    mul_right_cancel₀ hG ((cubicUnitGaussSum_power_eigen h p hp n w).trans (one_mul _).symm)
  obtain ⟨q, hq⟩ := tracePhase_dual_lattice (ringComplex h / ringComplex (p ^ n)) (by
    intro w
    convert hphase w using 1
    unfold residueAdditive cuspFrequency
    simp only [map_mul, map_pow, map_ofNat, pow_succ]
    congr 1
    field_simp)
  refine ⟨q, ?_⟩
  apply ringComplex_injective
  rw [map_mul, hq]
  field_simp [ringComplex_ne_zero (pow_ne_zero n hp)]

lemma cubicUnitGaussSum_power_vanish (h p : O) (hp : p ≠ 0) (n : ℕ) (hh : ¬ p ^ n ∣ h) :
    cubicUnitGaussSum h (p ^ (n + 1)) = 0 := by
  by_contra hG
  exact hh (cubicUnitGaussSum_power_support h p hp n hG)

lemma residueTraceQuotientChar_mulShift (h c : O) (hc : c ≠ 0) :
    residueTraceQuotientChar h c hc =
      (residueTraceQuotientChar 1 c hc).mulShift (Ideal.Quotient.mk (Ideal.span {c}) h) := by
  ext x
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [AddChar.mulShift_apply, ← map_mul, residueTraceQuotientChar_mk, residueTraceQuotientChar_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul, map_ofNat, map_one]
  congr 1
  ring

/-- The actual prime cubic character, embedded in the complex numbers. -/
def primeCubicMulChar (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) :
    MulChar (O ⧸ Ideal.span {p}) ℂ := by
  letI : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  exact (cubicChar (Ideal.span {p}) hg).ringHomComp ringComplex

lemma primeCubicMulChar_mk (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) (d : O) :
    primeCubicMulChar p hp hprimary (Ideal.Quotient.mk (Ideal.span {p}) d) = ringComplex (symbol d p) := by
  letI : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  rw [symbol_prime p hp hprimary, primeValue_eq _ hg]
  rfl

/-- The prime Gauss factors use the same geometric trace phase as the scattering series. -/
def primeCubicGauss (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) (e : ℕ) (h : O) : ℂ :=
  ∑' x : O ⧸ Ideal.span {p}, (primeCubicMulChar p hp hprimary ^ e) x * residueTraceQuotientChar h p hp.ne_zero x

lemma primeCubicGauss_one_eq (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) (h : O) :
    primeCubicGauss p hp hprimary 1 h = cubicUnitGaussSum h p := by
  let F : (O ⧸ Ideal.span {p}) → ℂ := fun x =>
    primeCubicMulChar p hp hprimary x * residueTraceQuotientChar h p hp.ne_zero x
  have hsup : Function.support F ⊆ {x | IsUnit x} := by
    intro x hx
    by_contra hn
    exact hx (by dsimp [F]; rw [MulChar.map_nonunit _ hn, zero_mul])
  change (∑' x : O ⧸ Ideal.span {p}, (primeCubicMulChar p hp hprimary ^ 1) x *
    residueTraceQuotientChar h p hp.ne_zero x) = _
  rw [pow_one]
  change (∑' x, F x) = _
  rw [← tsum_subtype_eq_of_support_subset hsup, cubicUnitGaussSum]
  apply tsum_congr
  intro x
  have hx := principalResidueRep_spec p x.1
  conv_lhs => rw [← hx]
  change primeCubicMulChar p hp hprimary (Ideal.Quotient.mk _ (principalResidueRep p x.1)) *
    residueTraceQuotientChar h p hp.ne_zero (Ideal.Quotient.mk _ (principalResidueRep p x.1)) = _
  rw [primeCubicMulChar_mk, residueTraceQuotientChar_mk]

/-- Cubing the geometric prime Gauss sum erases every invertible frequency twist. -/
theorem cubicUnitGaussSum_prime_cube (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    cubicUnitGaussSum h p ^ 3 = -ringComplex p * (Ideal.absNorm (Ideal.span {p}) : ℂ) := by
  letI : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  letI : Finite (O ⧸ Ideal.span {p}) := (Ideal.span {p}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  letI : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {p}) h) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact hph (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hshift : residueTraceQuotientChar h p hp.ne_zero =
      (residueTraceQuotientChar 1 p hp.ne_zero).mulShift hu.unit := by
    rw [residueTraceQuotientChar_mulShift, hu.unit_spec]
  have he : cubicUnitGaussSum h p =
      gaussSum ((cubicChar (Ideal.span {p}) hg).ringHomComp ringComplex)
        (residueTraceQuotientChar h p hp.ne_zero) := by
    rw [← primeCubicGauss_one_eq p hp hprimary h]
    simp only [primeCubicGauss, pow_one, tsum_fintype, gaussSum]
    rfl
  rw [he, hshift]
  exact (cubicGauss_cube_mulShift ringComplex (Ideal.span {p}) hg
    (residueTraceQuotientChar 1 p hp.ne_zero) hu.unit).trans
      (cubicGauss_cube ringComplex ringComplex_injective (Ideal.span {p}) hg p rfl hprimary
        (residueTraceQuotientChar 1 p hp.ne_zero) (residueTraceQuotientChar_primitive p hp.ne_zero))

lemma finite_tsum_comp_addHom {R S : Type*} [AddGroup R] [AddGroup S] [Finite R] [Finite S]
    (f : R →+ S) (hf : Function.Surjective f) (F : S → ℂ) :
    (∑' x : R, F (f x)) = (Nat.card f.ker : ℂ) * ∑' y : S, F y := by
  letI : Fintype R := Fintype.ofFinite _
  letI : Fintype S := Fintype.ofFinite _
  letI : Fintype f.ker := Fintype.ofFinite _
  rw [tsum_fintype, tsum_fintype, ← Fintype.sum_fiberwise' f F]
  have hc (y : S) : Fintype.card {x : R // f x = y} = Fintype.card f.ker :=
    Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf y)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, Nat.card_eq_fintype_card]
  rw [Finset.mul_sum]

/-- Reduction of a principal modulus to a divisor. -/
def conductorReduction (a b : O) : (O ⧸ Ideal.span {a * b}) →+* (O ⧸ Ideal.span {a}) :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right a b))

lemma conductorReduction_surjective (a b : O) : Function.Surjective (conductorReduction a b) :=
  Ideal.Quotient.factor_surjective _

lemma conductorReduction_kernel_card (a b : O) (ha : a ≠ 0) :
    Nat.card (conductorReduction a b).toAddMonoidHom.ker = Ideal.absNorm (Ideal.span {b}) := by
  have hc := card_ring_eq_card_mul_kernel (conductorReduction a b) (conductorReduction_surjective a b)
  change Ideal.absNorm (Ideal.span {a * b}) =
    Ideal.absNorm (Ideal.span {a}) * Nat.card (conductorReduction a b).toAddMonoidHom.ker at hc
  have hnorm : Ideal.absNorm (Ideal.span {a * b}) =
      Ideal.absNorm (Ideal.span {a}) * Ideal.absNorm (Ideal.span {b}) := by
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  rw [hnorm] at hc
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr ha))) hc.symm

/-- Finite Fourier transform of a weight whose conductor divides the modulus. -/
def conductorTraceSum (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (h : O) : ℂ :=
  ∑' x : O ⧸ Ideal.span {a * b}, F (conductorReduction a b x) *
    residueTraceQuotientChar h (a * b) (mul_ne_zero ha hb) x

lemma residueTraceQuotientChar_conductor_lift (a b k : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (x : O ⧸ Ideal.span {a * b}) :
    residueTraceQuotientChar (b * k) (a * b) (mul_ne_zero ha hb) x =
      residueTraceQuotientChar k a ha (conductorReduction a b x) := by
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
  change residueTraceQuotientChar (b * k) (a * b) _ (Ideal.Quotient.mk _ d) =
    residueTraceQuotientChar k a ha (Ideal.Quotient.mk _ d)
  rw [residueTraceQuotientChar_mk, residueTraceQuotientChar_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul, map_ofNat]
  congr 1
  field_simp [ringComplex_ne_zero ha, ringComplex_ne_zero hb]

/-- Lifting a frequency multiplies its finite Fourier transform by the kernel cardinality. -/
theorem conductorTraceSum_lift (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (k : O) :
    conductorTraceSum a b ha hb F (b * k) =
      (Ideal.absNorm (Ideal.span {b}) : ℂ) *
        ∑' x : O ⧸ Ideal.span {a}, F x * residueTraceQuotientChar k a ha x := by
  letI : Finite (O ⧸ Ideal.span {a}) := (Ideal.span {a}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr ha)
  letI : Finite (O ⧸ Ideal.span {a * b}) := (Ideal.span {a * b}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha hb))
  have he := finite_tsum_comp_addHom (conductorReduction a b).toAddMonoidHom
    (conductorReduction_surjective a b) (fun x => F x * residueTraceQuotientChar k a ha x)
  rw [conductorReduction_kernel_card a b ha] at he
  calc
    _ = ∑' x : O ⧸ Ideal.span {a * b}, F (conductorReduction a b x) *
        residueTraceQuotientChar k a ha (conductorReduction a b x) := by
      apply tsum_congr
      intro x
      exact congrArg (fun z => F (conductorReduction a b x) * z)
        (residueTraceQuotientChar_conductor_lift a b k ha hb x)
    _ = _ := he

lemma conductorReduction_power_unit (p : O) (n : ℕ) (x : O ⧸ Ideal.span {p * p ^ n}) :
    IsUnit (conductorReduction p (p ^ n) x) ↔ IsUnit x := by
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
  change IsUnit (Ideal.Quotient.mk (Ideal.span {p}) d) ↔
    IsUnit (Ideal.Quotient.mk (Ideal.span {p * p ^ n}) d)
  rw [isUnit_quotient_span_iff, isUnit_quotient_span_iff]
  constructor
  · intro h
    rw [← pow_succ']
    exact h.pow_left
  · rintro ⟨a, b, hab⟩
    refine ⟨a * p ^ n, b, ?_⟩
    linear_combination hab

lemma cubicUnitGaussSum_prime_power_conductor (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (n : ℕ) (h : O) :
    cubicUnitGaussSum h (p ^ (n + 1)) =
      conductorTraceSum p (p ^ n) hp.ne_zero (pow_ne_zero _ hp.ne_zero)
        (fun x => (primeCubicMulChar p hp hprimary ^ (n + 1)) x) h := by
  let χ := primeCubicMulChar p hp hprimary
  let F : (O ⧸ Ideal.span {p * p ^ n}) → ℂ := fun x =>
    (χ ^ (n + 1)) (conductorReduction p (p ^ n) x) *
      residueTraceQuotientChar h (p * p ^ n) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero)) x
  have hsup : Function.support F ⊆ {x | IsUnit x} := by
    intro x hx
    by_contra hn
    have hh : ¬ IsUnit (conductorReduction p (p ^ n) x) :=
      fun hh => hn ((conductorReduction_power_unit p n x).mp hh)
    exact hx (by dsimp [F]; rw [MulChar.map_nonunit _ hh, zero_mul])
  rw [pow_succ' p n]
  change cubicUnitGaussSum h (p * p ^ n) = ∑' x, F x
  rw [← tsum_subtype_eq_of_support_subset hsup, cubicUnitGaussSum]
  apply tsum_congr
  intro x
  let d := principalResidueRep (p * p ^ n) x.1
  have hd : Ideal.Quotient.mk (Ideal.span {p * p ^ n}) d = x.1 := principalResidueRep_spec _ _
  change ringComplex (symbol d (p * p ^ n)) * residueAdditive (3 * h) (p * p ^ n) d = F x.1
  rw [← hd]
  change _ = (χ ^ (n + 1)) (Ideal.Quotient.mk (Ideal.span {p}) d) *
    residueTraceQuotientChar h (p * p ^ n) _ (Ideal.Quotient.mk _ d)
  rw [MulChar.pow_apply' _ (Nat.succ_ne_zero n), primeCubicMulChar_mk,
    residueTraceQuotientChar_mk, ← pow_succ' p n, symbol_pow_denominator, map_pow]

/-- Prime-power Gauss sums reduce exactly to a residue-field sum with the correct character power. -/
theorem cubicUnitGaussSum_prime_power_lift (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (n : ℕ) (h : O) :
    cubicUnitGaussSum (p ^ n * h) (p ^ (n + 1)) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n * primeCubicGauss p hp hprimary (n + 1) h := by
  rw [cubicUnitGaussSum_prime_power_conductor p hp hprimary n,
    conductorTraceSum_lift p (p ^ n) hp.ne_zero (pow_ne_zero _ hp.ne_zero)]
  rw [← Ideal.span_singleton_pow, map_pow, Nat.cast_pow]
  rfl

lemma primeCubicMulChar_cube (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) :
    primeCubicMulChar p hp hprimary ^ 3 = 1 := by
  letI : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  change ((cubicChar (Ideal.span {p}) hg).ringHomComp ringComplex) ^ 3 = 1
  rw [MulChar.ringHomComp_pow, cubicChar_pow_three, MulChar.ringHomComp_one]

lemma primeCubicGauss_mod_three (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (e : ℕ) (h : O) :
    primeCubicGauss p hp hprimary e h = primeCubicGauss p hp hprimary (e % 3) h := by
  have he : primeCubicMulChar p hp hprimary ^ e = primeCubicMulChar p hp hprimary ^ (e % 3) := by
    calc
      _ = primeCubicMulChar p hp hprimary ^ (e % 3 + 3 * (e / 3)) := by rw [Nat.mod_add_div]
      _ = _ := by rw [pow_add, pow_mul, primeCubicMulChar_cube, one_pow, mul_one]
  unfold primeCubicGauss
  rw [he]

/-- The cubic identity gives the exact square-root size at a nonzero prime frequency. -/
theorem cubicUnitGaussSum_prime_norm (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    ‖cubicUnitGaussSum h p‖ = ‖ringComplex p‖ := by
  have hc := congrArg norm (cubicUnitGaussSum_prime_cube p hp hprimary h hph)
  simp only [norm_pow, norm_mul, norm_neg, Complex.norm_natCast] at hc
  rw [← ringComplex_norm_sq_eq_absNorm_span] at hc
  have hp' : 0 < ‖ringComplex p‖ := norm_pos_iff.mpr (ringComplex_ne_zero hp.ne_zero)
  have hg : 0 ≤ ‖cubicUnitGaussSum h p‖ := norm_nonneg _
  have hpos : 0 < ‖cubicUnitGaussSum h p‖ ^ 2 +
      ‖cubicUnitGaussSum h p‖ * ‖ringComplex p‖ + ‖ringComplex p‖ ^ 2 := by positivity
  have he : (‖cubicUnitGaussSum h p‖ - ‖ringComplex p‖) *
      (‖cubicUnitGaussSum h p‖ ^ 2 + ‖cubicUnitGaussSum h p‖ * ‖ringComplex p‖ + ‖ringComplex p‖ ^ 2) = 0 := by
    nlinarith only [hc]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hpos.ne')

lemma primeCubicMulChar_ne_one (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) :
    primeCubicMulChar p hp hprimary ≠ 1 := by
  letI : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  change (cubicChar (Ideal.span {p}) hg).ringHomComp ringComplex ≠ 1
  exact (MulChar.ringHomComp_ne_one_iff ringComplex_injective).mpr (cubicChar_ne_one _ hg)

lemma primeCubicMulChar_order (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) :
    orderOf (primeCubicMulChar p hp hprimary) = 3 := by
  have hd := orderOf_dvd_of_pow_eq_one (primeCubicMulChar_cube p hp hprimary)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact False.elim (primeCubicMulChar_ne_one p hp hprimary (orderOf_eq_one_iff.mp h1))
  · exact h3

lemma primeCubicMulChar_pow_eq_one (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) (e : ℕ) :
    primeCubicMulChar p hp hprimary ^ e = 1 ↔ 3 ∣ e := by
  rw [← orderOf_dvd_iff_pow_eq_one, primeCubicMulChar_order]

lemma primeCubicGauss_eq_gaussSum (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (e : ℕ) (h : O) [Fintype (O ⧸ Ideal.span {p})] :
    primeCubicGauss p hp hprimary e h =
      gaussSum (primeCubicMulChar p hp hprimary ^ e) (residueTraceQuotientChar h p hp.ne_zero) := by
  simp only [primeCubicGauss, tsum_fintype, gaussSum]

lemma residueTraceQuotientChar_ne_one (c h : O) (hc : c ≠ 0) (hh : ¬ c ∣ h) :
    residueTraceQuotientChar h c hc ≠ 1 := by
  rw [residueTraceQuotientChar_mulShift]
  apply residueTraceQuotientChar_primitive c hc
  intro hz
  exact hh (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))

/-- At zero frequency only the trivial character power survives. -/
theorem primeCubicGauss_of_dvd (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (e : ℕ) (h : O) (hph : p ∣ h) :
    primeCubicGauss p hp hprimary e h =
      if 3 ∣ e then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1 else 0 := by
  letI : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  letI : Finite (O ⧸ Ideal.span {p}) := (Ideal.span {p}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  letI : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hh : Ideal.Quotient.mk (Ideal.span {p}) h = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hph)
  rw [primeCubicGauss_eq_gaussSum, residueTraceQuotientChar_mulShift, hh, AddChar.mulShift_zero]
  split_ifs with he
  · rw [(primeCubicMulChar_pow_eq_one p hp hprimary e).mpr he, gaussSum_one_one,
      Nat.card_units, Nat.cast_sub (Nat.succ_le_of_lt Nat.card_pos), Nat.cast_one]
    rfl
  · exact gaussSum_one_right (fun hχ => he ((primeCubicMulChar_pow_eq_one p hp hprimary e).mp hχ))

lemma primeCubicGauss_trivial_nonzero (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (e : ℕ) (he : 3 ∣ e) (h : O) (hph : ¬ p ∣ h) : primeCubicGauss p hp hprimary e h = -1 := by
  letI : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  letI : Finite (O ⧸ Ideal.span {p}) := (Ideal.span {p}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  letI : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primeCubicGauss_eq_gaussSum, (primeCubicMulChar_pow_eq_one p hp hprimary e).mpr he]
  exact gaussSum_one_left (residueTraceQuotientChar_ne_one p h hp.ne_zero hph)

/-- The two nontrivial cubic Gauss factors multiply to the residue-field cardinality. -/
theorem primeCubicGauss_one_mul_two (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (h : O) (hph : ¬ p ∣ h) :
    primeCubicGauss p hp hprimary 1 h * primeCubicGauss p hp hprimary 2 h =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) := by
  letI : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  letI : Finite (O ⧸ Ideal.span {p}) := (Ideal.span {p}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  letI : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hψ : (residueTraceQuotientChar h p hp.ne_zero).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one (residueTraceQuotientChar_ne_one p h hp.ne_zero hph)
  have he := gaussSum_mul_gaussSum_pow_orderOf_sub_one (primeCubicMulChar_ne_one p hp hprimary) hψ
  rw [primeCubicMulChar_order] at he
  have hm := MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) (primeCubicMulChar_cube p hp hprimary)
  rw [hm, one_mul] at he
  change _ = (Nat.card (O ⧸ Ideal.span {p}) : ℂ)
  simpa only [primeCubicGauss_eq_gaussSum, pow_one, Nat.reduceSub, Nat.card_eq_fintype_card] using he

lemma cubicUnitGaussSum_frequency_dvd (h c : O) (hc : c ≠ 0) (hh : c ∣ h) :
    cubicUnitGaussSum h c = cubicUnitGaussSum 0 c :=
  cubicUnitGaussSum_frequency_congr h 0 c hc (by simpa only [sub_zero] using hh)

lemma cubicUnitGaussSum_prime_power_zero (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) (n : ℕ) :
    cubicUnitGaussSum 0 (p ^ (n + 1)) =
      if 3 ∣ n + 1 then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        ((Ideal.absNorm (Ideal.span {p}) : ℂ) - 1) else 0 := by
  have he := cubicUnitGaussSum_prime_power_lift p hp hprimary n 0
  simp only [mul_zero] at he
  rw [he, primeCubicGauss_of_dvd p hp hprimary (n + 1) 0 (dvd_zero _)]
  split_ifs <;> ring

/-- Reciprocity absorbs the coprime cubic twist into one frequency. -/
theorem cubicUnitGaussSum_primary_product (h a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpa : lambda ^ 2 ∣ a - 1) (hpb : lambda ^ 2 ∣ b - 1) (hab : IsCoprime a b) :
    cubicUnitGaussSum h (a * b) = cubicUnitGaussSum h a * cubicUnitGaussSum (h * a) b := by
  have ht := cubicUnitGaussSum_frequency_twist h b a hb hab.symm
  have hc : ringComplex (symbol a b) ^ 3 = 1 := by
    rw [← map_pow, symbol_cube_of_isCoprime a b hpb hab, map_one]
  rw [cubicUnitGaussSum_coprime_product h a b ha hb hab, symbol_reciprocity b a hpb hpa,
    ← ht]
  calc
    _ = ringComplex (symbol a b) ^ 3 *
        (cubicUnitGaussSum h a * cubicUnitGaussSum (h * a) b) := by ring
    _ = _ := by rw [hc, one_mul]

/-- Unramified ideals with the chosen prime factor removed. -/
abbrev PrimeDeletedIdeal (p : O) := {I : GoodIdeal // ¬ (Ideal.span {p} : Ideal O) ∣ I.1}

def unramifiedPrimeDeletedSeries (p : O) (s : ℂ) (h : O) : ℂ :=
  ∑' I : PrimeDeletedIdeal p,
    unramifiedNormWeight s I.1.1 * cubicUnitGaussSum h (primaryIdealGenerator I.1.1)

lemma primaryIdealGenerator_pow (I : Ideal O) (n : ℕ) :
    primaryIdealGenerator (I ^ n) = primaryIdealGenerator I ^ n := map_pow primaryIdealGeneratorHom I n

lemma gaussPrimeIdeal_prime (p : O) (hp : Prime p) : Prime (Ideal.span {p} : Ideal O) :=
  Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp)

def gaussPrimeFactorMap (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (q : ℕ × PrimeDeletedIdeal p) : GoodIdeal :=
  ⟨(Ideal.span {p}) ^ q.1 * q.2.1.1, by
    rw [primaryIdealGenerator_mul, primaryIdealGenerator_pow,
      primaryIdealGenerator_span p hp.ne_zero hprimary]
    exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) q.2.1.2⟩

lemma gaussPrimeFactorMap_bijective (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) :
    Function.Bijective (gaussPrimeFactorMap p hp hprimary) := by
  let P : Ideal O := Ideal.span {p}
  have hP : Prime P := gaussPrimeIdeal_prime p hp
  constructor
  · rintro ⟨n, I⟩ ⟨m, J⟩ heq
    have he : P ^ n * I.1.1 = P ^ m * J.1.1 := congrArg Subtype.val heq
    have hn : n = m := by
      have hm := congrArg (multiplicity P) he
      rw [prime_power_remainder_multiplicity hP I.2,
        prime_power_remainder_multiplicity hP J.2] at hm
      exact hm
    subst m
    have hIJ : I = J := Subtype.ext (Subtype.ext (mul_left_cancel₀ (pow_ne_zero n hP.ne_zero) he))
    subst J
    rfl
  · intro I
    obtain ⟨J, hJ, hnot⟩ := (FiniteMultiplicity.of_prime_left hP
      (primaryIdealGenerator_ne_zero_ideal I.1 I.2)).exists_eq_pow_mul_and_not_dvd
    have hgood : primaryIdealGenerator J ≠ 0 := by
      intro hz
      apply I.2
      rw [hJ, primaryIdealGenerator_mul, hz, mul_zero]
    exact ⟨(multiplicity P I.1, ⟨⟨J, hgood⟩, hnot⟩), Subtype.ext hJ.symm⟩

def gaussPrimeFactorEquiv (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) :
    ℕ × PrimeDeletedIdeal p ≃ GoodIdeal :=
  Equiv.ofBijective (gaussPrimeFactorMap p hp hprimary) (gaussPrimeFactorMap_bijective p hp hprimary)

lemma primeDeleted_generator_coprime (p : O) (hp : Prime p) (I : PrimeDeletedIdeal p) :
    IsCoprime p (primaryIdealGenerator I.1.1) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  apply I.2
  rw [Ideal.dvd_iff_le, ← (primaryIdealGenerator_spec I.1.1 I.1.2).1,
    Ideal.span_singleton_le_span_singleton]
  exact hd

lemma primary_pow_congruence (p : O) (hprimary : lambda ^ 2 ∣ p - 1) (n : ℕ) :
    lambda ^ 2 ∣ p ^ n - 1 := by
  simpa only [one_pow] using hprimary.trans (sub_dvd_pow_sub_pow p 1 n)

lemma gaussPrimeFactor_term (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (s : ℂ) (h : O) (n : ℕ) (I : PrimeDeletedIdeal p) :
    unramifiedNormWeight s (gaussPrimeFactorMap p hp hprimary (n, I)).1 *
        cubicUnitGaussSum h (primaryIdealGenerator (gaussPrimeFactorMap p hp hprimary (n, I)).1) =
      unramifiedNormWeight s (Ideal.span {p}) ^ n * cubicUnitGaussSum h (p ^ n) *
        (unramifiedNormWeight s I.1.1 * cubicUnitGaussSum (h * p ^ n) (primaryIdealGenerator I.1.1)) := by
  change unramifiedNormWeight s ((Ideal.span {p}) ^ n * I.1.1) *
    cubicUnitGaussSum h (primaryIdealGenerator ((Ideal.span {p}) ^ n * I.1.1)) = _
  rw [primaryIdealGenerator_mul, primaryIdealGenerator_pow,
    primaryIdealGenerator_span p hp.ne_zero hprimary,
    cubicUnitGaussSum_primary_product h (p ^ n) (primaryIdealGenerator I.1.1)
      (pow_ne_zero _ hp.ne_zero) I.1.2 (primary_pow_congruence p hprimary n)
      (primaryIdealGenerator_spec I.1.1 I.1.2).2 (primeDeleted_generator_coprime p hp I).pow_left,
    map_mul, map_pow]
  ring

/-- Splitting off one prime gives its exact local expansion, with an absolutely convergent remainder. -/
theorem unramifiedCubicGaussSeries_prime_reindex (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (s : ℂ) (hs : 2 < s.re) (h : O) :
    unramifiedCubicGaussSeries s h =
      ∑' n : ℕ, unramifiedNormWeight s (Ideal.span {p}) ^ n * cubicUnitGaussSum h (p ^ n) *
        unramifiedPrimeDeletedSeries p s (h * p ^ n) := by
  let F : GoodIdeal → ℂ := fun I =>
    unramifiedNormWeight s I.1 * cubicUnitGaussSum h (primaryIdealGenerator I.1)
  have hsum : Summable F := (unramifiedCubicGaussSeries_summable_norm s hs h).of_norm
  let e := gaussPrimeFactorEquiv p hp hprimary
  have hpull : Summable (fun q : ℕ × PrimeDeletedIdeal p => F (e q)) := e.summable_iff.mpr hsum
  change (∑' I, F I) = _
  rw [← e.tsum_eq F, hpull.tsum_prod]
  apply tsum_congr
  intro n
  change (∑' I : PrimeDeletedIdeal p,
    unramifiedNormWeight s (gaussPrimeFactorMap p hp hprimary (n, I)).1 *
      cubicUnitGaussSum h (primaryIdealGenerator (gaussPrimeFactorMap p hp hprimary (n, I)).1)) = _
  simp_rw [gaussPrimeFactor_term p hp hprimary s h n]
  exact tsum_mul_left

lemma unramifiedPrimeDeletedSeries_cube_shift (p : O) (hp : Prime p) (s : ℂ) (h : O) :
    unramifiedPrimeDeletedSeries p s (h * p ^ 3) = unramifiedPrimeDeletedSeries p s h := by
  apply tsum_congr
  intro I
  congr 1
  exact cubicUnitGaussSum_cube_shift h _ p I.1.2
    (primaryIdealGenerator_spec I.1.1 I.1.2).2 (primeDeleted_generator_coprime p hp I).symm

@[simp] lemma cubicUnitGaussSum_one (h : O) : cubicUnitGaussSum h 1 = 1 := by
  letI : Subsingleton (O ⧸ Ideal.span {(1 : O)}) :=
    Ideal.Quotient.subsingleton_iff.mpr (by simp)
  let r : CubicUnitResidue (1 : O) := ⟨1, isUnit_one⟩
  rw [cubicUnitGaussSum, tsum_eq_single r (fun b hb => False.elim (hb (Subsingleton.elim b r)))]
  rw [symbol_one, map_one, one_mul,
    residueAdditive_three_congr h 1 _ 0 one_ne_zero (one_dvd _)]
  simp only [residueAdditive, map_zero, mul_zero, zero_div, AddChar.map_zero_eq_one]

lemma cubicUnitGaussSum_prime_power_too_large (p : O) (hp : Prime p)
    (h : O) (hph : ¬ p ∣ h) (a k : ℕ) (hk : a + 1 < k) :
    cubicUnitGaussSum (h * p ^ a) (p ^ k) = 0 := by
  by_contra hG
  cases k with
  | zero => omega
  | succ n =>
    have hd := cubicUnitGaussSum_power_support (h * p ^ a) p hp.ne_zero n hG
    have hd' : p ^ (a + 1) ∣ p ^ a * h := by
      rw [mul_comm]
      exact (pow_dvd_pow p (by omega : a + 1 ≤ n)).trans hd
    rw [pow_succ] at hd'
    exact hph ((mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)).mp hd')

lemma unramifiedPrimeDeletedSeries_pow_mod (p : O) (hp : Prime p) (s : ℂ) (h : O) (n : ℕ) :
    unramifiedPrimeDeletedSeries p s (h * p ^ n) =
      unramifiedPrimeDeletedSeries p s (h * p ^ (n % 3)) := by
  apply tsum_congr
  intro I
  congr 1
  have he : p ^ n = p ^ (n % 3) * (p ^ (n / 3)) ^ 3 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [he, ← mul_assoc]
  exact cubicUnitGaussSum_cube_shift _ _ _ I.1.2
    (primaryIdealGenerator_spec I.1.1 I.1.2).2 (primeDeleted_generator_coprime p hp I).symm.pow_right

/-- At a frequency of valuation `a`, the prime expansion ends at exponent `a+1`. -/
theorem unramifiedCubicGaussSeries_prime_finite (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (s : ℂ) (hs : 2 < s.re) (h : O) (hph : ¬ p ∣ h) (a : ℕ) :
    unramifiedCubicGaussSeries s (h * p ^ a) =
      ∑ k ∈ Finset.range (a + 2), unramifiedNormWeight s (Ideal.span {p}) ^ k *
        cubicUnitGaussSum (h * p ^ a) (p ^ k) * unramifiedPrimeDeletedSeries p s (h * p ^ a * p ^ k) := by
  rw [unramifiedCubicGaussSeries_prime_reindex p hp hprimary s hs]
  apply tsum_eq_sum
  intro k hk
  have hk' : a + 1 < k := by
    have hh : a + 2 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    omega
  rw [cubicUnitGaussSum_prime_power_too_large p hp h hph a k hk', mul_zero, zero_mul]

/-- The local recurrence follows from the four supported Gauss factors and cubic periodicity. -/
theorem unramifiedCubicGaussSeries_prime_recurrence (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (s : ℂ) (hs : 2 < s.re) (h : O) (hph : ¬ p ∣ h) :
    unramifiedCubicGaussSeries s (h * p ^ 3) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        unramifiedCubicGaussSeries s h -
      unramifiedNormWeight s (Ideal.span {p}) * primeCubicGauss p hp hprimary 1 h *
        unramifiedCubicGaussSeries s (h * p) := by
  let q : ℂ := Ideal.absNorm (Ideal.span {p})
  have hg0 (k : ℕ) (hk : k ≤ 3) :
      cubicUnitGaussSum (h * p ^ 3) (p ^ k) = cubicUnitGaussSum 0 (p ^ k) :=
    cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
      ((pow_dvd_pow p hk).trans (dvd_mul_left (p ^ 3) h))
  have hg1 : cubicUnitGaussSum (h * p ^ 3) p = 0 := by
    have he := hg0 1 (by omega)
    simp only [pow_one] at he
    rw [he]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2 : cubicUnitGaussSum (h * p ^ 3) (p ^ 2) = 0 := by
    rw [hg0 2 (by omega)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hg3 : cubicUnitGaussSum (h * p ^ 3) (p ^ 3) = q ^ 2 * (q - 1) := by
    rw [hg0 3 le_rfl]
    simpa only [Nat.reduceAdd, dvd_refl, ite_true] using cubicUnitGaussSum_prime_power_zero p hp hprimary 2
  have hg4 : cubicUnitGaussSum (h * p ^ 3) (p ^ 4) = q ^ 3 * primeCubicGauss p hp hprimary 1 h := by
    have he := cubicUnitGaussSum_prime_power_lift p hp hprimary 3 h
    rw [primeCubicGauss_mod_three p hp hprimary 4] at he
    simpa only [mul_comm (p ^ 3) h, Nat.reduceMod] using he
  have hj1 : cubicUnitGaussSum (h * p) p = 0 := by
    rw [cubicUnitGaussSum_frequency_dvd _ p hp.ne_zero (dvd_mul_left p h)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hj2 : cubicUnitGaussSum (h * p) (p ^ 2) = q * primeCubicGauss p hp hprimary 2 h := by
    simpa only [pow_one, mul_comm p h] using cubicUnitGaussSum_prime_power_lift p hp hprimary 1 h
  have e0 := unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 0
  have e1 := unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 1
  have e3 := unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    cubicUnitGaussSum_one, mul_one, one_mul, hg1, hg2, hg3, hg4, hj1, hj2,
    mul_zero, zero_mul, add_zero] at e0 e1 e3
  rw [show h * p * p ^ 2 = h * p ^ 3 by ring, unramifiedPrimeDeletedSeries_cube_shift p hp] at e1
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp,
    show h * p ^ 3 * p ^ 3 = h * p ^ 6 by ring,
    show h * p ^ 3 * p ^ 4 = h * p ^ 7 by ring,
    unramifiedPrimeDeletedSeries_pow_mod p hp s h 6,
    unramifiedPrimeDeletedSeries_pow_mod p hp s h 7] at e3
  simp only [Nat.reduceMod, pow_zero, pow_one, mul_one] at e3
  rw [e3, e0, e1, ← primeCubicGauss_one_eq p hp hprimary h]
  have hg := primeCubicGauss_one_mul_two p hp hprimary h hph
  change _ = q at hg
  change _ = (1 + q ^ 3 * _) * _ - _
  linear_combination unramifiedNormWeight s (Ideal.span {p}) ^ 3 * q *
    unramifiedPrimeDeletedSeries p s h * hg

lemma primeCubicGauss_add_three (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (e : ℕ) (h : O) : primeCubicGauss p hp hprimary (e + 3) h = primeCubicGauss p hp hprimary e h := by
  unfold primeCubicGauss
  rw [pow_add, primeCubicMulChar_cube, mul_one]

/-- Increasing both conductor and frequency by a cube scales every positive conductor term by `N(p)^3`. -/
lemma cubicUnitGaussSum_prime_cube_shift_pos (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (n : ℕ) (h : O) :
    cubicUnitGaussSum (h * p ^ 3) (p ^ (n + 4)) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * cubicUnitGaussSum h (p ^ (n + 1)) := by
  by_cases hd : p ^ n ∣ h
  · obtain ⟨r, rfl⟩ := hd
    rw [show p ^ n * r * p ^ 3 = p ^ (n + 3) * r by rw [pow_add]; ring,
      show n + 4 = (n + 3) + 1 by omega,
      cubicUnitGaussSum_prime_power_lift p hp hprimary (n + 3) r,
      cubicUnitGaussSum_prime_power_lift p hp hprimary n r,
      show n + 3 + 1 = (n + 1) + 3 by omega, primeCubicGauss_add_three, pow_add]
    ring
  · have hlow := cubicUnitGaussSum_power_vanish h p hp.ne_zero n hd
    have hhigh : cubicUnitGaussSum (h * p ^ 3) (p ^ (n + 4)) = 0 := by
      rw [show n + 4 = (n + 3) + 1 by omega]
      apply cubicUnitGaussSum_power_vanish _ p hp.ne_zero (n + 3)
      intro hh
      have he : p ^ 3 * p ^ n ∣ p ^ 3 * h := by
        simpa only [pow_add, mul_comm, mul_left_comm, mul_assoc] using hh
      exact hd ((mul_dvd_mul_iff_left (pow_ne_zero 3 hp.ne_zero)).mp he)
    rw [hhigh, hlow, mul_zero]

lemma cubicUnitGaussSum_prime_cube_shift (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (k : ℕ) (h : O) :
    cubicUnitGaussSum (h * p ^ 3) (p ^ (k + 3)) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * cubicUnitGaussSum h (p ^ k) -
        if k = 0 then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 2 else 0 := by
  cases k with
  | zero =>
    rw [Nat.zero_add, cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
      (dvd_mul_left (p ^ 3) h)]
    have he := cubicUnitGaussSum_prime_power_zero p hp hprimary 2
    simp only [Nat.reduceAdd, dvd_refl, ite_true] at he
    rw [he]
    simp only [pow_zero, cubicUnitGaussSum_one, mul_one, ite_true]
    ring
  | succ n =>
    simpa only [show n + 1 + 3 = n + 4 by omega, Nat.succ_ne_zero, ite_false, sub_zero] using
      cubicUnitGaussSum_prime_cube_shift_pos p hp hprimary n h

/-- Compact support needed to test the continued source at a rationally translated cusp. -/
def rationalCuspCompact (g : rationalExtension) : Set KernelQuotient :=
  kernelRationalAction g '' kernelCuspAverageCompact

lemma rationalCuspCompact_isCompact (g : rationalExtension) : IsCompact (rationalCuspCompact g) :=
  kernelCuspAverageCompact_isCompact.image (kernelRationalAction_continuous g)

def rationalCuspFourier (h : O) (g : rationalExtension) : KernelQuotientL2 →L[ℂ] ℂ :=
  (kernelCuspFourier h).comp (kernelRationalPullback g).toContinuousLinearMap

lemma rationalCuspFourier_integral (h : O) (g : rationalExtension) (F : KernelQuotientL2) :
    rationalCuspFourier h g F = ∫ w in cuspPeriodStrip 5 6,
      F (kernelRationalAction g (integralOrbitProjection globalKubotaKernel w)) *
        cuspFourierPhase h w ∂hyperbolicVolume := by
  rw [rationalCuspFourier, ContinuousLinearMap.comp_apply, kernelCuspFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp
    (ae_restrict_of_ae (kernelRationalPullback_ae g F) (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z : ℂ => z * cuspFourierPhase h w) hw

lemma rationalCuspFourier_restrict (h : O) (g : rationalExtension) (F : KernelQuotientL2) :
    rationalCuspFourier h g (kernelMassRestrictionCLM (rationalCuspCompact g)
      (rationalCuspCompact_isCompact g).measurableSet F) = rationalCuspFourier h g F := by
  rw [rationalCuspFourier_integral, rationalCuspFourier_integral]
  have hsource := (kernelRationalAction_measurePreserving g).quasiMeasurePreserving.ae_eq_comp
    (kernelMassRestriction_coe (rationalCuspCompact g) (rationalCuspCompact_isCompact g).measurableSet F)
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he, ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  have hmem : kernelRationalAction g (integralOrbitProjection globalKubotaKernel w) ∈ rationalCuspCompact g :=
    ⟨_, kernelCuspStripSet_subset_compact ⟨w, hwm, rfl⟩, rfl⟩
  exact congrArg (fun z : ℂ => z * cuspFourierPhase h w) (hw.trans (Set.indicator_of_mem hmem _))

/-- The continued scalar source tested at an arbitrary cusp in the rational extension. -/
def rationalCuspFamily (h : O) (g : rationalExtension)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (s : ℂ) : ℂ :=
  rationalCuspFourier h g
    (kernelLocalCorrectedSeed (rationalCuspCompact g) (rationalCuspCompact_isCompact g) a b ha hab s)

lemma rationalCuspFamily_meromorphicAt (h : O) (g : rationalExtension)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    MeromorphicAt (rationalCuspFamily h g a b ha hab) (4 / 3 : ℂ) :=
  meromorphicAt_clm (rationalCuspFourier h g)
    (kernelLocalCorrectedSeed_meromorphicAt _ (rationalCuspCompact_isCompact g) a b ha hab)

lemma rationalCuspFamily_analyticAt_nonreal (h : O) (g : rationalExtension)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (s : ℂ) (hs : s.re ≠ 1) (hi : s.im ≠ 0) :
    AnalyticAt ℂ (rationalCuspFamily h g a b ha hab) s :=
  (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (rationalCuspFourier h g) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _ (rationalCuspCompact_isCompact g) a b ha hab s hs hi) rfl

lemma rationalCuspFamily_residue_limit (h : O) (g : rationalExtension)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun s : ℂ => (s - 4 / 3) * rationalCuspFamily h g a b ha hab s)
      (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (rationalCuspFourier h g (kernelEisensteinResidueVector a b ha hab))) := by
  have he := (rationalCuspFourier h g).continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit _ (rationalCuspCompact_isCompact g) a b ha hab)
  simpa only [Function.comp_def, map_smul, smul_eq_mul, rationalCuspFourier_restrict,
    rationalCuspFamily] using he

lemma rationalCuspFamily_actual_integral (h : O) (g : rationalExtension)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (s : ℂ) :
    rationalCuspFamily h g a b ha hab s = ∫ w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s (kernelRationalAction g (integralOrbitProjection globalKubotaKernel w)) *
        cuspFourierPhase h w ∂hyperbolicVolume := by
  rw [rationalCuspFamily, rationalCuspFourier_integral]
  have hsource := (kernelRationalAction_measurePreserving g).quasiMeasurePreserving.ae_eq_comp
    (kernelLocalCorrectedSeed_ae_eq _ (rationalCuspCompact_isCompact g) a b ha hab s)
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he, ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  have hmem : kernelRationalAction g (integralOrbitProjection globalKubotaKernel w) ∈ rationalCuspCompact g :=
    ⟨_, kernelCuspStripSet_subset_compact ⟨w, hwm, rfl⟩, rfl⟩
  exact congrArg (fun z : ℂ => z * cuspFourierPhase h w) (hw.trans (Set.indicator_of_mem hmem _))

theorem rationalCuspFamily_initial (h : O) (g : rationalExtension)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (ha1 : 1 < a) (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    rationalCuspFamily h g a b ha hab s = ∫ w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (integralComplexMatrix (g : SL(2, O)) • w) *
        cuspFourierPhase h w ∂hyperbolicVolume := by
  have hcorrected : kernelCorrectedSeed a b ha hab s =ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s (by linarith) := by
    filter_upwards [kernelEisensteinL2Correction_initial_overlap a b ha1 hab s hs hi] with q hq
    change kernelQuotientSeed a b s q + kernelEisensteinL2Correction a b ha hab s q = _
    rw [hq]
    ring
  have hsource := (kernelRationalAction_measurePreserving g).quasiMeasurePreserving.ae_eq_comp hcorrected
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s := kernelCuspStripSet))
  rw [rationalCuspFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z : ℂ => z * cuspFourierPhase h w)
    (hw.trans (by dsimp only [Function.comp_def]; rw [kernelRationalAction_mk, kernelQuotientEisenstein_mk]))

/-- Rows at the opposite cusp, indexed directly by their unramified denominator ideal. -/
abbrev OppositeData := Σ I : GoodIdeal, {x : O // IsCoprime (primaryIdealGenerator I.1) x}

def oppositeDataToPrimitive (q : OppositeData) : PrimitiveRow :=
  ⟨![-3 * q.2.1, primaryIdealGenerator q.1.1], by
    change IsCoprime (-3 * q.2.1) (primaryIdealGenerator q.1.1) ∧
      (3 : O) ∣ -3 * q.2.1 ∧ (3 : O) ∣ primaryIdealGenerator q.1.1 - 1
    have hp := (primaryIdealGenerator_spec q.1.1 q.1.2).2
    refine ⟨?_, ⟨-q.2.1, by ring⟩, three_dvd_primary_sub_one _ hp⟩
    simpa only [neg_mul] using ((primary_coprime_three _ hp).mul_right q.2.2).symm.neg_left⟩

lemma oppositeDataToPrimitive_bijective : Function.Bijective oppositeDataToPrimitive := by
  constructor
  · rintro ⟨I, x⟩ ⟨J, y⟩ he
    have hr := congrArg Subtype.val he
    have hI : I = J := primaryIdealGenerator_injective_good (congrFun hr 1)
    subst J
    have hx : x = y := by
      apply Subtype.ext
      exact mul_left_cancel₀ (by norm_num : -(3 : O) ≠ 0) (congrFun hr 0)
    subst y
    rfl
  · intro r
    obtain ⟨t, ht⟩ := r.2.2.1
    have hp : lambda ^ 2 ∣ r.1 1 - 1 := lambda_sq_dvd_three.trans r.2.2.2
    have hd := primary_ne_zero (r.1 1) hp
    let I : GoodIdeal := ⟨Ideal.span {r.1 1}, by
      rw [primaryIdealGenerator_span _ hd hp]
      exact hd⟩
    have hI : primaryIdealGenerator I.1 = r.1 1 := primaryIdealGenerator_span _ hd hp
    have hc : IsCoprime (primaryIdealGenerator I.1) (-t) := by
      rw [hI]
      have he : IsCoprime (r.1 1) (3 * t) := by simpa only [ht] using r.2.1.symm
      exact he.of_mul_right_right.neg_right
    refine ⟨⟨I, ⟨-t, hc⟩⟩, Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change -3 * (-t) = r.1 0
      rw [ht]
      ring
    · exact hI

def oppositeDataEquiv : OppositeData ≃ PrimitiveRow :=
  Equiv.ofBijective oppositeDataToPrimitive oppositeDataToPrimitive_bijective

def oppositeMatrix : SL(2, ℂ) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

lemma rowOperator_opposite (v : Fin 2 → ℂ) : rowOperator oppositeMatrix v = ![v 1, -v 0] := by
  rw [rowOperator_apply]
  funext i
  fin_cases i <;> simp [oppositeMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

def oppositeEisenstein (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) : ℂ :=
  eisenstein (oppositeMatrix * upperSection z v hv) s

lemma rowHeight_eq_shiftedHeightKernel (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ)
    (c d : O) (hc : c ≠ 0) :
    ((v / (‖ringComplex c * z + ringComplex d‖ ^ 2 + ‖ringComplex c‖ ^ 2 * v ^ 2) : ℝ) : ℂ) ^ s =
      ((‖ringComplex c‖ ^ 2 : ℝ) : ℂ) ^ (-s) *
        shiftedHeightKernel v s (ringComplex d / ringComplex c) z := by
  have hc' := ringComplex_ne_zero hc
  have hn : 0 < ‖ringComplex c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc')
  have hfac : ringComplex c * z + ringComplex d = ringComplex c * (z + ringComplex d / ringComplex c) := by
    field_simp
  have he : v / (‖ringComplex c * z + ringComplex d‖ ^ 2 + ‖ringComplex c‖ ^ 2 * v ^ 2) =
      ((‖ringComplex c‖ ^ 2 * v) * (1 + ‖(z + ringComplex d / ringComplex c) / (v : ℂ)‖ ^ 2))⁻¹ := by
    rw [hfac, norm_mul, mul_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg hv.le]
    field_simp
    ring
  unfold shiftedHeightKernel hyperbolicKernel
  rw [he, Complex.ofReal_inv, inv_cpow_ofReal_nonneg (by positivity), ← Complex.cpow_neg,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (mul_nonneg hn.le hv.le) (by positivity),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hn.le hv.le]
  ring

def oppositeTerm (z : ℂ) (v : ℝ) (s : ℂ) (c x : O) : ℂ :=
  ringComplex (symbol (3 * x) c) *
    ((v / (‖ringComplex c * z + ringComplex (3 * x)‖ ^ 2 + ‖ringComplex c‖ ^ 2 * v ^ 2) : ℝ) : ℂ) ^ s

lemma oppositeTerm_eq_shifted (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ)
    (c x : O) (hc : c ≠ 0) :
    oppositeTerm z v s c x =
      (ringComplex (symbol (3 * x) c) * ((‖ringComplex c‖ ^ 2 : ℝ) : ℂ) ^ (-s)) *
        shiftedHeightKernel v s (ringComplex (3 * x) / ringComplex c) z := by
  rw [oppositeTerm, rowHeight_eq_shiftedHeightKernel z v hv s c (3 * x) hc]
  ring

lemma opposite_summand (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (q : OppositeData) :
    summand (oppositeMatrix * upperSection z v hv) s (primitiveRowEquiv.symm (oppositeDataEquiv q)) =
      oppositeTerm z v s (primaryIdealGenerator q.1.1) q.2.1 := by
  let r : Fin 2 → ℂ := ![ringComplex (primaryIdealGenerator q.1.1), ringComplex (3 * q.2.1)]
  have hr : rowOperator oppositeMatrix (embeddedRow (primitiveRowEquiv.symm (oppositeDataEquiv q))) = r := by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_opposite]
    funext i
    fin_cases i <;> simp [oppositeDataEquiv, Equiv.ofBijective_apply, oppositeDataToPrimitive, r, map_mul]
  have hr0 : r ≠ 0 := by
    intro he
    exact ringComplex_ne_zero q.1.2 (congrFun he 0)
  have hp := heightDenominator_pos z v hv r hr0
  have hphase : (cosetCharacter (primitiveRowEquiv.symm (oppositeDataEquiv q)))⁻¹ =
      ringComplex (symbol (3 * q.2.1) (primaryIdealGenerator q.1.1)) := by
    rw [inverse_cosetCharacter_eq_row_symbol, primitiveRowEquiv_symm_row]
    change ringComplex (symbol (-3 * q.2.1) (primaryIdealGenerator q.1.1)) = _
    rw [neg_mul, symbol_neg_numerator _ _ (primaryIdealGenerator_spec q.1.1 q.1.2).2]
  rw [summand, ← rowOperator_mul, hr, rowEnergy_upperSection, hphase]
  change _ = ringComplex (symbol (3 * q.2.1) (primaryIdealGenerator q.1.1)) *
    ((v / heightDenominator z v r : ℝ) : ℂ) ^ s
  have hi : ((v / heightDenominator z v r : ℝ) : ℂ) = (((heightDenominator z v r / v : ℝ) : ℂ))⁻¹ := by
    simp only [Complex.ofReal_div, inv_div]
  rw [hi, inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le), Complex.cpow_neg]

theorem oppositeEisenstein_eq_rows (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) :
    oppositeEisenstein z v hv s = ∑' q : OppositeData,
      oppositeTerm z v s (primaryIdealGenerator q.1.1) q.2.1 := by
  let e := oppositeDataEquiv.trans primitiveRowEquiv.symm
  change (∑' x : CuspCosets, summand (oppositeMatrix * upperSection z v hv) s x) = _
  rw [← e.tsum_eq (fun x => summand (oppositeMatrix * upperSection z v hv) s x)]
  exact tsum_congr (opposite_summand z v hv s)

abbrev CoprimeElement (c : O) := {x : O // IsCoprime c x}

def cubicResidueElementMap (c : O) (q : CubicUnitResidue c × O) : CoprimeElement c :=
  ⟨principalResidueRep c q.1.1 + c * q.2, by
    apply (isUnit_quotient_span_iff c _).mp
    have hc : Ideal.Quotient.mk (Ideal.span {c}) c = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simpa only [map_add, map_mul, hc, zero_mul, add_zero, principalResidueRep_spec] using q.1.2⟩

lemma cubicResidueElementMap_bijective (c : O) (hc : c ≠ 0) :
    Function.Bijective (cubicResidueElementMap c) := by
  have hmod (r : CubicUnitResidue c) (n : O) :
      Ideal.Quotient.mk (Ideal.span {c}) (principalResidueRep c r.1 + c * n) = r.1 := by
    have hz : Ideal.Quotient.mk (Ideal.span {c}) c = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [map_add, map_mul, hz, zero_mul, add_zero, principalResidueRep_spec]
  constructor
  · rintro ⟨r, n⟩ ⟨t, m⟩ he
    have he' := congrArg Subtype.val he
    change principalResidueRep c r.1 + c * n = principalResidueRep c t.1 + c * m at he'
    have hr : r = t := Subtype.ext (by
      simpa only [hmod] using congrArg (Ideal.Quotient.mk (Ideal.span {c})) he')
    subst t
    have hn : n = m := mul_left_cancel₀ hc (add_left_cancel he')
    subst m
    rfl
  · intro x
    let r : CubicUnitResidue c := ⟨Ideal.Quotient.mk (Ideal.span {c}) x.1,
      (isUnit_quotient_span_iff c x.1).mpr x.2⟩
    have hd : c ∣ x.1 - principalResidueRep c r.1 :=
      Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
        (principalResidueRep_spec c r.1).symm)
    obtain ⟨n, hn⟩ := hd
    refine ⟨(r, n), Subtype.ext ?_⟩
    change principalResidueRep c r.1 + c * n = x.1
    linear_combination -hn

def cubicResidueElementEquiv (c : O) (hc : c ≠ 0) : CubicUnitResidue c × O ≃ CoprimeElement c :=
  Equiv.ofBijective (cubicResidueElementMap c) (cubicResidueElementMap_bijective c hc)

lemma oppositeTerm_shift (z : ℂ) (v : ℝ) (s : ℂ) (c x n : O) :
    oppositeTerm z v s c (x + c * n) = oppositeTerm (z + 3 * ringComplex n) v s c x := by
  have hs : symbol (3 * (x + c * n)) c = symbol (3 * x) c := symbol_congr ⟨3 * n, by ring⟩
  have he : ringComplex c * z + ringComplex (3 * (x + c * n)) =
      ringComplex c * (z + 3 * ringComplex n) + ringComplex (3 * x) := by
    simp only [map_mul, map_add, map_ofNat]
    ring
  rw [oppositeTerm, oppositeTerm, hs, he]

def oppositeGaussSum (h c : O) : ℂ :=
  ∑' r : CubicUnitResidue c, ringComplex (symbol (3 * principalResidueRep c r.1) c) *
    residueAdditive h c (3 * principalResidueRep c r.1)

lemma oppositeGaussSum_eq (h c : O) (hc : c ≠ 0) (hp : lambda ^ 2 ∣ c - 1) :
    oppositeGaussSum h c = cubicUnitGaussSum (9 * h) c := by
  have he : oppositeGaussSum h c = ringComplex (symbol 3 c) * cubicUnitGaussSum h c := by
    rw [oppositeGaussSum, cubicUnitGaussSum, ← tsum_mul_left]
    apply tsum_congr
    intro r
    rw [symbol_mul_numerator, map_mul]
    have ht : residueAdditive h c (3 * principalResidueRep c r.1) =
        residueAdditive (3 * h) c (principalResidueRep c r.1) := by
      unfold residueAdditive cuspFrequency
      simp only [map_mul, map_ofNat]
      congr 1
      ring
    rw [ht]
    ring
  rw [he]
  have ht := cubicUnitGaussSum_ramified_twist h 1 c hc hp
    (by simpa only [mul_one] using (primary_coprime_three c hp).symm)
  simpa only [symbol_one_numerator c hp, map_one, one_mul, mul_one] using ht

lemma continuous_inverse_fixed_left_operator (a : SL(2, ℂ)) (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => rowOperator (a * upperSection z v hv)⁻¹) := by
  have he (z : ℂ) : rowOperator (a * upperSection z v hv)⁻¹ =
      (rowOperator a⁻¹).comp (rowOperator (upperSection z v hv)⁻¹) := by
    ext u
    simp only [mul_inv_rev, ContinuousLinearMap.comp_apply, rowOperator_mul]
  simp_rw [he]
  exact continuous_const.clm_comp (continuous_inverse_upper_operator v hv)

lemma exists_fixed_left_rowBound (a : SL(2, ℂ)) (v : ℝ) (hv : 0 < v) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ periodDomain, rowBound (a * upperSection z v hv) ≤ C := by
  have hc : Continuous (fun z : ℂ => rowBound (a * upperSection z v hv)) :=
    continuous_const.mul (continuous_const.add (continuous_inverse_fixed_left_operator a v hv).norm)
  let R : ℝ := ∑ i : Fin 2, ‖periodBasis i‖
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hc.continuousOn
  refine ⟨max 1 C, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro z hz
  apply (hC ?_).trans (le_max_right _ _)
  exact ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using norm_mem_periodDomain z hz, rfl⟩

lemma continuous_fixed_left_summand (a : SL(2, ℂ)) (v : ℝ) (hv : 0 < v) (s : ℂ) (x : CuspCosets) :
    Continuous (fun z : ℂ => summand (a * upperSection z v hv) s x) := by
  simp_rw [summand, ← rowOperator_mul, rowEnergy_upperSection]
  apply continuous_const.mul
  apply Continuous.cpow
  · apply Complex.continuous_ofReal.comp
    unfold heightDenominator
    fun_prop
  · exact continuous_const
  · intro z
    apply Complex.ofReal_mem_slitPlane.mpr
    exact div_pos (heightDenominator_pos z v hv _ (rowOperator_ne_zero a _ (embeddedRow_ne_zero x))) hv

/-- A fixed change of cusp preserves the summable integral-row majorant. -/
lemma fixed_left_summable_majorant (a : SL(2, ℂ)) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    ∃ M : CuspCosets → ℝ, Summable M ∧ (∀ x, 0 ≤ M x) ∧
      ∀ z ∈ periodDomain, ∀ x, ‖summand (a * upperSection z v hv) s x‖ ≤ M x := by
  obtain ⟨C, hC, hbound⟩ := exists_fixed_left_rowBound a v hv
  refine ⟨fun x => C ^ (2 * s.re) * ‖rowCoordinates (cosetRow x)‖ ^ (-(2 * s.re)), ?_, ?_, ?_⟩
  · exact ((summable_integer_four_rpow (2 * s.re) (by linarith)).comp_injective
      (rowCoordinates_injective.comp cosetRow_injective)).mul_left _
  · intro x
    positivity
  · intro z hz x
    apply (norm_summand_bound (a * upperSection z v hv) s (by linarith) x).trans
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (rowBound_pos _).le (hbound z hz) (by linarith)) (by positivity)

theorem hasSum_integral_fixed_left_Eisenstein (a : SL(2, ℂ)) (v : ℝ) (hv : 0 < v)
    (s freq : ℂ) (hs : 2 < s.re) :
    HasSum (fun x : CuspCosets => ∫ z in periodDomain,
      summand (a * upperSection z v hv) s x * tracePhase (-freq * z))
      (∫ z in periodDomain, eisenstein (a * upperSection z v hv) s * tracePhase (-freq * z)) := by
  letI : Countable CuspCosets := (rowCoordinates_injective.comp cosetRow_injective).countable
  letI := periodDomain_finiteMeasure
  obtain ⟨M, hM, _, hbound⟩ := fixed_left_summable_majorant a v hv s hs
  have hchar : Continuous (fun z : ℂ => tracePhase (-freq * z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2 * Real.pi * Complex.I *
      ((-freq * z) + starRingEnd ℂ (-freq * z))))
    fun_prop
  exact hasSum_integral_of_dominated_convergence (μ := volume.restrict periodDomain)
    (fun (x : CuspCosets) (_ : ℂ) => M x)
    (fun x => ((continuous_fixed_left_summand a v hv s x).mul hchar).aestronglyMeasurable.restrict)
    (fun x => (ae_restrict_mem periodDomain_measurable).mono fun z hz => by
      simpa only [Pi.mul_apply, norm_mul, tracePhase_norm, mul_one] using hbound z hz x)
    (Eventually.of_forall fun _ => hM) (integrable_const (∑' x, M x))
    (Eventually.of_forall fun z => (summable_summand (a * upperSection z v hv) s hs).hasSum.mul_right
      (tracePhase (-freq * z)))

def oppositeIntegral (v : ℝ) (s freq : ℂ) (c x : O) : ℂ :=
  ∫ z in periodDomain, oppositeTerm z v s c x * tracePhase (-freq * z)

theorem hasSum_oppositeIntegrals (v : ℝ) (hv : 0 < v) (s freq : ℂ) (hs : 2 < s.re) :
    HasSum (fun q : OppositeData => oppositeIntegral v s freq (primaryIdealGenerator q.1.1) q.2.1)
      (∫ z in periodDomain, oppositeEisenstein z v hv s * tracePhase (-freq * z)) := by
  have he := (oppositeDataEquiv.trans primitiveRowEquiv.symm).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein oppositeMatrix v hv s freq hs)
  apply he.congr_fun
  intro q
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only [Equiv.trans_apply]
    rw [opposite_summand]

lemma oppositeTerm_integrable (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (c x : O) (hc : c ≠ 0) : Integrable (fun z => oppositeTerm z v s c x) := by
  simp_rw [oppositeTerm_eq_shifted _ v hv s c x hc]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma oppositeIntegral_sum_translate (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (h c x : O) (hc : c ≠ 0) :
    (∑' n : O, oppositeIntegral v s (cuspFrequency h) c (x + c * n)) =
      ∫ z : ℂ, oppositeTerm z v s c x * tracePhase (-cuspFrequency h * z) := by
  have hi := trace_mul_integrable (fun z => oppositeTerm z v s c x)
    (oppositeTerm_integrable v hv s hs c x hc) (cuspFrequency h)
  rw [integral_eq_period_integrals _ hi]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only [oppositeIntegral]
    rw [oppositeTerm_shift, cuspFrequency_negative_period]

lemma oppositeTerm_fourier_integral (v : ℝ) (hv : 0 < v) (s freq : ℂ)
    (c x : O) (hc : c ≠ 0) :
    (∫ z : ℂ, oppositeTerm z v s c x * tracePhase (-freq * z)) =
      ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (freq * v)) * ((‖ringComplex c‖ ^ 2 : ℝ) : ℂ) ^ (-s) *
        (ringComplex (symbol (3 * x) c) * tracePhase (freq * ringComplex (3 * x) / ringComplex c)) := by
  simp_rw [oppositeTerm_eq_shifted _ v hv s c x hc, mul_assoc]
  rw [integral_const_mul, integral_const_mul,
    traceIntegral_shiftedHeightKernel v hv s (ringComplex (3 * x) / ringComplex c) freq]
  ring_nf

lemma oppositeDenominator_integral_formula (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re)
    (h : O) (I : GoodIdeal) :
    (∑' x : CoprimeElement (primaryIdealGenerator I.1),
      oppositeIntegral v s (cuspFrequency h) (primaryIdealGenerator I.1) x.1) =
      ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (cuspFrequency h * v)) *
        (unramifiedNormWeight s I.1 * cubicUnitGaussSum (9 * h) (primaryIdealGenerator I.1)) := by
  let c := primaryIdealGenerator I.1
  let F : CoprimeElement c → ℂ := fun x => oppositeIntegral v s (cuspFrequency h) c x.1
  have hf : Summable F := (hasSum_oppositeIntegrals v hv s (cuspFrequency h) hs).summable.sigma_factor I
  let e := cubicResidueElementEquiv c I.2
  have hsum : Summable (fun q : CubicUnitResidue c × O => F (e q)) := e.summable_iff.mpr hf
  change (∑' x, F x) = _
  rw [← e.tsum_eq F, hsum.tsum_prod]
  change (∑' r : CubicUnitResidue c, ∑' n : O,
    oppositeIntegral v s (cuspFrequency h) c (principalResidueRep c r.1 + c * n)) = _
  simp_rw [oppositeIntegral_sum_translate v hv s (by linarith) h c _ I.2,
    oppositeTerm_fourier_integral v hv s (cuspFrequency h) c _ I.2]
  have he : ((‖ringComplex c‖ ^ 2 : ℝ) : ℂ) ^ (-s) = unramifiedNormWeight s I.1 := by
    rw [unramifiedNormWeight_of_good s I.1 I.2, primaryIdealGenerator_norm_sq I.1 I.2,
      Complex.ofReal_natCast]
  rw [he, ← oppositeGaussSum_eq h c I.2 (primaryIdealGenerator_spec I.1 I.2).2]
  change (∑' r : CubicUnitResidue c, _ *
    (ringComplex (symbol (3 * principalResidueRep c r.1) c) * residueAdditive h c (3 * principalResidueRep c r.1))) = _
  rw [tsum_mul_left]
  unfold oppositeGaussSum
  ring

lemma unramifiedCubicGaussSeries_twentySeven (s : ℂ) (h : O) :
    unramifiedCubicGaussSeries s (27 * h) = unramifiedCubicGaussSeries s h := by
  apply tsum_congr
  intro I
  congr 1
  have hp := (primaryIdealGenerator_spec I.1 I.2).2
  simpa only [show (3 : O) ^ 3 = 27 by norm_num, mul_comm h 27] using
    cubicUnitGaussSum_cube_shift h (primaryIdealGenerator I.1) 3 I.2 hp (primary_coprime_three _ hp)

/-- Fourier unfolding at the opposite cusp gives the ordinary unramified Gauss series. -/
theorem oppositeEisenstein_fourier (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) (h : O) :
    (∫ z in periodDomain, oppositeEisenstein z v hv s * tracePhase (-cuspFrequency h * z)) =
      ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (cuspFrequency h * v)) *
        unramifiedCubicGaussSeries s (9 * h) := by
  have he := hasSum_oppositeIntegrals v hv s (cuspFrequency h) hs
  rw [← he.tsum_eq, he.summable.tsum_sigma]
  simp_rw [oppositeDenominator_integral_formula v hv s hs h]
  exact tsum_mul_left

def primeExpansionTerm (p : O) (s : ℂ) (h : O) (k : ℕ) : ℂ :=
  unramifiedNormWeight s (Ideal.span {p}) ^ k * cubicUnitGaussSum h (p ^ k) *
    unramifiedPrimeDeletedSeries p s (h * p ^ k)

lemma primeExpansionTerm_summable (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (s : ℂ) (hs : 2 < s.re) (h : O) : Summable (primeExpansionTerm p s h) := by
  let F : GoodIdeal → ℂ := fun I =>
    unramifiedNormWeight s I.1 * cubicUnitGaussSum h (primaryIdealGenerator I.1)
  have hf : Summable F := (unramifiedCubicGaussSeries_summable_norm s hs h).of_norm
  let e := gaussPrimeFactorEquiv p hp hprimary
  have he : Summable (fun q : ℕ × PrimeDeletedIdeal p => F (e q)) := e.summable_iff.mpr hf
  apply he.prod.congr
  intro n
  change (∑' I : PrimeDeletedIdeal p,
    unramifiedNormWeight s (gaussPrimeFactorMap p hp hprimary (n, I)).1 *
      cubicUnitGaussSum h (primaryIdealGenerator (gaussPrimeFactorMap p hp hprimary (n, I)).1)) = _
  simp_rw [gaussPrimeFactor_term p hp hprimary s h n]
  exact tsum_mul_left

lemma primeExpansionTerm_cube_shift (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (s : ℂ) (h : O) (k : ℕ) :
    primeExpansionTerm p s (h * p ^ 3) (k + 3) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3 *
        primeExpansionTerm p s h k -
      if k = 0 then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 2 * unramifiedNormWeight s (Ideal.span {p}) ^ 3 *
        unramifiedPrimeDeletedSeries p s h else 0 := by
  have hv : unramifiedPrimeDeletedSeries p s (h * p ^ 3 * p ^ (k + 3)) =
      unramifiedPrimeDeletedSeries p s (h * p ^ k) := by
    rw [show h * p ^ 3 * p ^ (k + 3) = (h * p ^ k * p ^ 3) * p ^ 3 by rw [pow_add]; ring,
      unramifiedPrimeDeletedSeries_cube_shift p hp, unramifiedPrimeDeletedSeries_cube_shift p hp]
  unfold primeExpansionTerm
  rw [cubicUnitGaussSum_prime_cube_shift p hp hprimary k h, hv, pow_add]
  split_ifs with hk
  · subst k
    simp only [pow_zero, mul_one, cubicUnitGaussSum_one]
    ring
  · ring

/-- The conductor shift gives a cubic recurrence at every frequency, including zero. -/
theorem unramifiedCubicGaussSeries_cube_step (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (s : ℂ) (hs : 2 < s.re) (h : O) :
    unramifiedCubicGaussSeries s (h * p ^ 3) =
      (1 - (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 2 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        unramifiedPrimeDeletedSeries p s h +
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3 *
        unramifiedCubicGaussSeries s h := by
  have hzero (k : ℕ) (hk : k ≤ 3) :
      cubicUnitGaussSum (h * p ^ 3) (p ^ k) = cubicUnitGaussSum 0 (p ^ k) :=
    cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
      ((pow_dvd_pow p hk).trans (dvd_mul_left (p ^ 3) h))
  have hg1 : cubicUnitGaussSum (h * p ^ 3) p = 0 := by
    have he := hzero 1 (by omega)
    simp only [pow_one] at he
    rw [he]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2 : cubicUnitGaussSum (h * p ^ 3) (p ^ 2) = 0 := by
    rw [hzero 2 (by omega)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hsmall : (∑ k ∈ Finset.range 3, primeExpansionTerm p s (h * p ^ 3) k) =
      unramifiedPrimeDeletedSeries p s h := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, primeExpansionTerm,
      pow_zero, pow_one, cubicUnitGaussSum_one, mul_one, one_mul, zero_add, hg1, hg2,
      mul_zero, zero_mul, add_zero]
    exact unramifiedPrimeDeletedSeries_cube_shift p hp s h
  have hsum := primeExpansionTerm_summable p hp hprimary s hs h
  have hsum' := primeExpansionTerm_summable p hp hprimary s hs (h * p ^ 3)
  rw [unramifiedCubicGaussSeries_prime_reindex p hp hprimary s hs (h * p ^ 3)]
  change (∑' k, primeExpansionTerm p s (h * p ^ 3) k) = _
  rw [← hsum'.sum_add_tsum_nat_add 3, hsmall]
  simp_rw [primeExpansionTerm_cube_shift p hp hprimary s h]
  rw [(hsum.mul_left _).tsum_sub (hasSum_ite_eq (0 : ℕ)
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 2 * unramifiedNormWeight s (Ideal.span {p}) ^ 3 *
        unramifiedPrimeDeletedSeries p s h)).summable,
    tsum_mul_left, tsum_ite_eq]
  have he : (∑' k, primeExpansionTerm p s h k) = unramifiedCubicGaussSeries s h :=
    (unramifiedCubicGaussSeries_prime_reindex p hp hprimary s hs h).symm
  rw [he]
  ring

theorem unramifiedCubicGaussSeries_cube_recurrence (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (s : ℂ) (hs : 2 < s.re) (h : O) :
    unramifiedCubicGaussSeries s (h * p ^ 6) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        unramifiedCubicGaussSeries s (h * p ^ 3) -
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3 *
        unramifiedCubicGaussSeries s h := by
  have hfirst := unramifiedCubicGaussSeries_cube_step p hp hprimary s hs h
  have hsecond := unramifiedCubicGaussSeries_cube_step p hp hprimary s hs (h * p ^ 3)
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp,
    show h * p ^ 3 * p ^ 3 = h * p ^ 6 by ring] at hsecond
  linear_combination hsecond - hfirst

def oppositeSource : rationalExtension := rationalSourceLift ModularGroup.S

lemma oppositeSource_matrix : integralComplexMatrix (oppositeSource : SL(2, O)) = oppositeMatrix := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [oppositeSource, rationalSourceLift, rationalEmbedding, integralComplexMatrix,
      Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_S, oppositeMatrix]

lemma hyperbolicEisenstein_opposite_upper (s : ℂ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    hyperbolicEisenstein s (integralComplexMatrix (oppositeSource : SL(2, O)) • upperPoint z v hv) =
      oppositeEisenstein z v hv s := by
  rw [oppositeSource_matrix]
  rfl

theorem opposite_cusp_fourier_average (s : ℂ) (hs : 2 < s.re) (h : O) :
    (∫ w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (integralComplexMatrix (oppositeSource : SL(2, O)) • w) *
        cuspFourierPhase h w ∂hyperbolicVolume) =
      unramifiedCubicGaussSeries s (9 * h) * cuspWhittakerHeightFactor s h := by
  let g : HyperbolicSpace → ℂ := fun w =>
    hyperbolicEisenstein s (integralComplexMatrix (oppositeSource : SL(2, O)) • w) * cuspFourierPhase h w
  have hg : Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  have he : (∫ v in Set.Icc (5 : ℝ) 6,
      (∫ z in periodDomain, g (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3) =
      ∫ v in Set.Icc (5 : ℝ) 6, unramifiedCubicGaussSeries s (9 * h) *
        ((v : ℂ) ^ (-s - 1) * sourceFourierKernel s (cuspFrequency h * v)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv.1
    have hvz : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv0.ne'
    have hslice : (∫ z in periodDomain, g (cuspCoordinateLift (v, z))) =
        ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (cuspFrequency h * v)) *
          unramifiedCubicGaussSeries s (9 * h) := by
      simp_rw [g, cuspCoordinateLift_positive v _ hv0, hyperbolicEisenstein_opposite_upper,
        cuspFourierPhase, hyperbolicHorizontal_upperPoint]
      exact oppositeEisenstein_fourier v hv0 s hs h
    have hp : (v : ℂ) ^ (-s - 1) = (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
      rw [show -s - 1 = (2 - s) - 3 by ring, Complex.cpow_sub _ _ hvz]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [hslice, hp]
    ring
  rw [he, integral_const_mul]
  rfl

lemma rationalCuspFamily_opposite_initial (h : O) (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    rationalCuspFamily (3 * h) oppositeSource 2 3 (by norm_num) (by norm_num) s =
      unramifiedCubicGaussSeries s h * cuspWhittakerHeightFactor s (3 * h) := by
  rw [rationalCuspFamily_initial (3 * h) oppositeSource 2 3
    (by norm_num) (by norm_num) (by norm_num) s hs hi,
    opposite_cusp_fourier_average s (by linarith),
    show (9 : O) * (3 * h) = 27 * h by ring, unramifiedCubicGaussSeries_twentySeven]

/-- Meromorphic continuation supplied by the opposite-cusp test of the actual resolvent. -/
def continuedUnramifiedGauss (h : O) (s : ℂ) : ℂ :=
  rationalCuspFamily (3 * h) oppositeSource 2 3 (by norm_num) (by norm_num) s /
    cuspWhittakerHeightFactor s (3 * h)

def unramifiedGaussResidue (h : O) : ℂ :=
  rationalCuspFourier (3 * h) oppositeSource cubicEisensteinResidue /
    cuspWhittakerHeightFactor (4 / 3 : ℂ) (3 * h)

theorem continuedUnramifiedGauss_meromorphicAt_center (h : O) :
    MeromorphicAt (continuedUnramifiedGauss h) (4 / 3 : ℂ) :=
  (rationalCuspFamily_meromorphicAt (3 * h) oppositeSource 2 3 (by norm_num) (by norm_num)).div
    (cuspWhittakerHeightFactor_analyticAt (3 * h) (4 / 3) (by norm_num)).meromorphicAt

theorem continuedUnramifiedGauss_meromorphicOn_upper (h : O) :
    MeromorphicOn (continuedUnramifiedGauss h) {s : ℂ | 1 < s.re ∧ 0 < s.im} := by
  intro s hs
  exact (rationalCuspFamily_analyticAt_nonreal (3 * h) oppositeSource 2 3
    (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').meromorphicAt.div
      (cuspWhittakerHeightFactor_analyticAt (3 * h) s hs.1).meromorphicAt

theorem continuedUnramifiedGauss_residue_limit (h : O) :
    Tendsto (fun s : ℂ => (s - 4 / 3) * continuedUnramifiedGauss h s)
      (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (unramifiedGaussResidue h)) := by
  have hd : Tendsto (fun s : ℂ => cuspWhittakerHeightFactor s (3 * h))
      (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (cuspWhittakerHeightFactor (4 / 3 : ℂ) (3 * h))) :=
    (cuspWhittakerHeightFactor_analyticAt (3 * h) (4 / 3) (by norm_num)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have he := (rationalCuspFamily_residue_limit (3 * h) oppositeSource 2 3
    (by norm_num) (by norm_num)).div hd (cuspWhittakerHeightFactor_center_ne_zero (3 * h))
  convert he using 1
  · funext s
    simp only [continuedUnramifiedGauss, Pi.div_apply]
    ring
  · rfl

theorem continuedUnramifiedGauss_initial (h : O) (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im)
    (hH : cuspWhittakerHeightFactor s (3 * h) ≠ 0) :
    continuedUnramifiedGauss h s = unramifiedCubicGaussSeries s h := by
  rw [continuedUnramifiedGauss, rationalCuspFamily_opposite_initial h s hs hi, mul_div_cancel_right₀ _ hH]

lemma unramifiedCubicGaussSeries_prime_two_power (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (s : ℂ) (hs : 2 < s.re) (h : O) (hph : ¬ p ∣ h) :
    unramifiedCubicGaussSeries s (h * p ^ 2) =
      (1 - (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 2 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        unramifiedPrimeDeletedSeries p s (h * p ^ 2) := by
  have he := unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 2
  have hg1 : cubicUnitGaussSum (h * p ^ 2) p = 0 := by
    rw [cubicUnitGaussSum_frequency_dvd _ p hp.ne_zero
      ((dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)).trans (dvd_mul_left (p ^ 2) h))]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2 : cubicUnitGaussSum (h * p ^ 2) (p ^ 2) = 0 := by
    rw [cubicUnitGaussSum_frequency_dvd _ (p ^ 2) (pow_ne_zero _ hp.ne_zero) (dvd_mul_left (p ^ 2) h)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hg3 : cubicUnitGaussSum (h * p ^ 2) (p ^ 3) = -(Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 2 := by
    have hh := cubicUnitGaussSum_prime_power_lift p hp hprimary 2 h
    rw [primeCubicGauss_trivial_nonzero p hp hprimary 3 (dvd_refl 3) h hph] at hh
    simpa only [mul_comm (p ^ 2) h, mul_neg_one] using hh
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    cubicUnitGaussSum_one, mul_one, one_mul, hg1, hg2, hg3, mul_zero, zero_mul, add_zero] at he
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp] at he
  exact he.trans (by ring)

lemma unramifiedCubicGaussSeries_square_cube (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (s : ℂ) (hs : 2 < s.re) (h : O) (hph : ¬ p ∣ h) :
    unramifiedCubicGaussSeries s (h * p ^ 5) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        unramifiedCubicGaussSeries s (h * p ^ 2) := by
  have he := unramifiedCubicGaussSeries_cube_step p hp hprimary s hs (h * p ^ 2)
  rw [← unramifiedCubicGaussSeries_prime_two_power p hp hprimary s hs h hph,
    show h * p ^ 2 * p ^ 3 = h * p ^ 5 by ring] at he
  exact he.trans (by ring)

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
