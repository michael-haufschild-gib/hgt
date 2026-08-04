import GaloisForLFunctions.RHTower.CCMRationalNonunitalStrongCyclicClassSpaceAction
import GaloisForLFunctions.RHTower.CCMRationalStrongCyclicTopology
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Faithful embedding of the literal nonunital strong target

One global unitization of continuous ideal fields embeds into continuous
fields of fibrewise unitizations.  The scalar coordinate is forced to be
constant, so this map identifies the literal Definition 4.9 ambient algebra
with a proper subalgebra of the larger pointwise-unitized field algebra.

The map is proved injective, as are all of its finite cyclic tensor powers.
It preserves diagonal trace and therefore restricts to a faithful cyclic
map from the literal strong target into the previously constructed
pointwise-field strong module.  This map is used only to inherit the verified
projective/LF graph topology; it does not alter the exact augmentation
kernel.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev IdealField :=
  CCMRationalContinuousTraceNormIdealField
private abbrev FieldUnit :=
  CCMRationalContinuousTraceNormIdealFieldUnitization
private abbrev PointwiseField :=
  CCMRationalContinuousTraceNormField
private abbrev Ideal := CCMRationalMoritaTraceNormOperator
private abbrev FibreUnit := CCMRationalMoritaTraceNormL1Unitization

private theorem ccmRationalMoritaTraceNormL1_ofLp_one :
    WithLp.ofLp (1 : FibreUnit) =
      (1 : Unitization ℂ Ideal) := by
  exact map_one (WithLp.unitizationAlgEquiv ℂ)

private theorem ccmRationalMoritaTraceNormL1_ofLp_inr (T : Ideal) :
    WithLp.ofLp (ccmRationalMoritaTraceNormL1InrHom T) =
      (T : Unitization ℂ Ideal) :=
  rfl

/-- Canonical inclusion of a single globally unitized ideal field into the
algebra of pointwise fibre unitizations. -/
def ccmRationalNonunitalFieldToPointwiseAlgHom :
    FieldUnit →ₐ[ℂ] PointwiseField :=
  Unitization.lift ccmRationalContinuousTraceNormOperatorFieldInrHom

@[simp]
theorem ccmRationalNonunitalFieldToPointwiseAlgHom_apply
    (x : FieldUnit) (b : Section) :
    ccmRationalNonunitalFieldToPointwiseAlgHom x b =
      ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation b x := by
  induction x using Unitization.ind with
  | inl_add_inr z F =>
      simp [ccmRationalNonunitalFieldToPointwiseAlgHom,
        ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation,
        ccmRationalContinuousTraceNormOperatorFieldInrHom]
      rw [Algebra.smul_def, mul_one]
      rfl

@[simp]
theorem ccmRationalNonunitalFieldToPointwiseAlgHom_apply_fst
    (x : FieldUnit) (b : Section) :
    (WithLp.ofLp (ccmRationalNonunitalFieldToPointwiseAlgHom x b)).fst =
      x.fst := by
  induction x using Unitization.ind with
  | inl_add_inr z F =>
      simp [ccmRationalNonunitalFieldToPointwiseAlgHom,
        ccmRationalContinuousTraceNormOperatorFieldInrHom,
        ccmRationalContinuousTraceNormOperatorFieldInr,
        ccmRationalMoritaTraceNormL1_ofLp_one]
      change (WithLp.ofLp
        (ccmRationalMoritaTraceNormL1InrHom (F b))).fst = 0
      rw [ccmRationalMoritaTraceNormL1_ofLp_inr]
      rfl

@[simp]
theorem ccmRationalNonunitalFieldToPointwiseAlgHom_apply_snd
    (x : FieldUnit) (b : Section) :
    (WithLp.ofLp (ccmRationalNonunitalFieldToPointwiseAlgHom x b)).snd =
      x.snd b := by
  induction x using Unitization.ind with
  | inl_add_inr z F =>
      simp [ccmRationalNonunitalFieldToPointwiseAlgHom,
        ccmRationalContinuousTraceNormOperatorFieldInrHom,
        ccmRationalContinuousTraceNormOperatorFieldInr,
        ccmRationalMoritaTraceNormL1_ofLp_one]
      change (WithLp.ofLp
        (ccmRationalMoritaTraceNormL1InrHom (F b))).snd = F b
      rw [ccmRationalMoritaTraceNormL1_ofLp_inr]
      rfl

/-- Global unitization inclusion is faithful: one evaluation recovers the
global scalar and all evaluations recover the ideal field. -/
theorem ccmRationalNonunitalFieldToPointwiseAlgHom_injective :
    Function.Injective ccmRationalNonunitalFieldToPointwiseAlgHom := by
  intro x y hxy
  apply Unitization.ext
  · have h := congrArg
      (fun F : PointwiseField => (WithLp.ofLp (F 1)).fst) hxy
    simpa only [ccmRationalNonunitalFieldToPointwiseAlgHom_apply_fst] using h
  · apply ContinuousMap.ext
    intro b
    have h := congrArg
      (fun F : PointwiseField => (WithLp.ofLp (F b)).snd) hxy
    simpa only [ccmRationalNonunitalFieldToPointwiseAlgHom_apply_snd] using h

/-- Every finite cyclic tensor power of the global-unitization inclusion is
injective. -/
theorem ccmRationalNonunitalFieldToPointwiseCyclicDegree_injective
    (n : ℕ) :
    Function.Injective
      (cyclicBarAlgHomDegree
        ccmRationalNonunitalFieldToPointwiseAlgHom n) := by
  have hfker :
      ccmRationalNonunitalFieldToPointwiseAlgHom.toLinearMap.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      ccmRationalNonunitalFieldToPointwiseAlgHom_injective
  obtain ⟨g, hg⟩ :=
    LinearMap.exists_leftInverse_of_injective
      ccmRationalNonunitalFieldToPointwiseAlgHom.toLinearMap hfker
  let G : Fin (n + 1) → (PointwiseField →ₗ[ℂ] FieldUnit) := fun _ => g
  have hleft :
      (PiTensorProduct.map G).comp
          (cyclicBarAlgHomDegree
            ccmRationalNonunitalFieldToPointwiseAlgHom n) =
        LinearMap.id := by
    rw [cyclicBarAlgHomDegree, ← PiTensorProduct.map_comp]
    have hmaps :
        (fun i : Fin (n + 1) =>
          G i ∘ₗ ccmRationalNonunitalFieldToPointwiseAlgHom.toLinearMap) =
          (fun _ : Fin (n + 1) => (LinearMap.id : FieldUnit →ₗ[ℂ] FieldUnit)) := by
      funext i
      exact hg
    rw [hmaps, PiTensorProduct.map_id]
  apply Function.LeftInverse.injective
  intro x
  change PiTensorProduct.map G
      (cyclicBarAlgHomDegree
        ccmRationalNonunitalFieldToPointwiseAlgHom n x) = x
  have := LinearMap.congr_fun hleft x
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using this

/-- Pointwise normalized traces agree under the faithful inclusion. -/
theorem ccmRationalNonunitalFieldPointTrace_embedding
    (b : Section) (x : FieldUnit) :
    ccmRationalContinuousTraceNormPointTrace b
        (ccmRationalNonunitalFieldToPointwiseAlgHom x) =
      ccmRationalNonunitalFieldPointTrace b x := by
  rw [ccmRationalContinuousTraceNormPointTrace_apply,
    ccmRationalNonunitalFieldPointTrace_apply,
    ccmRationalNonunitalFieldToPointwiseAlgHom_apply]

/-- Main-diagonal trace is unchanged by inclusion into pointwise-unitized
fields. -/
theorem ccmRationalNonunitalStrongDiagonalTrace_embedding
    (n : ℕ) (x : CyclicBarTensor ℂ FieldUnit n) :
    ccmRationalStrongDiagonalTrace n
        (cyclicBarAlgHomDegree
          ccmRationalNonunitalFieldToPointwiseAlgHom n x) =
      ccmRationalNonunitalStrongDiagonalTrace n x := by
  funext b
  have hproduct := LinearMap.congr_fun
    (cyclicBarTotalProduct_algHom
      ccmRationalNonunitalFieldToPointwiseAlgHom n) x
  have hproduct' :
      cyclicBarTotalProduct n
          (cyclicBarAlgHomDegree
            ccmRationalNonunitalFieldToPointwiseAlgHom n x) =
        ccmRationalNonunitalFieldToPointwiseAlgHom
          (cyclicBarTotalProduct n x) := by
    change _ =
      ccmRationalNonunitalFieldToPointwiseAlgHom.toLinearMap
        (cyclicBarTotalProduct n x)
    simpa only [LinearMap.comp_apply] using hproduct.symm
  change ccmRationalContinuousTraceNormPointTrace b
      (cyclicBarTotalProduct n
        (cyclicBarAlgHomDegree
          ccmRationalNonunitalFieldToPointwiseAlgHom n x)) = _
  rw [hproduct', ccmRationalNonunitalFieldPointTrace_embedding]
  rfl

/-- Degreewise faithful inclusion of literal strong chains into the larger
pointwise-field strong module. -/
def ccmRationalNonunitalStrongCyclicEmbeddingDegree (n : ℕ) :
    CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n →ₗ[ℂ]
      CCMRationalStrongCyclicTarget.simplicial.degree n where
  toFun x :=
    ⟨cyclicBarAlgHomDegree
        ccmRationalNonunitalFieldToPointwiseAlgHom n x.1, by
      change ccmRationalStrongDiagonalTrace n
          (cyclicBarAlgHomDegree
            ccmRationalNonunitalFieldToPointwiseAlgHom n x.1) ∈
        CCMRationalStrongClassSpaceScalarTarget
      rw [ccmRationalNonunitalStrongDiagonalTrace_embedding]
      exact
        (mem_ccmRationalNonunitalStrongCyclicTarget_iff n x.1).mp x.2 |>.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add
      (cyclicBarAlgHomDegree
        ccmRationalNonunitalFieldToPointwiseAlgHom n) x.1 y.1
  map_smul' z x := by
    apply Subtype.ext
    exact map_smul
      (cyclicBarAlgHomDegree
        ccmRationalNonunitalFieldToPointwiseAlgHom n) z x.1

@[simp]
theorem ccmRationalNonunitalStrongCyclicEmbeddingDegree_coe
    (n : ℕ)
    (x : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :
    (ccmRationalNonunitalStrongCyclicEmbeddingDegree n x).1 =
      cyclicBarAlgHomDegree
        ccmRationalNonunitalFieldToPointwiseAlgHom n x.1 :=
  rfl

theorem ccmRationalNonunitalStrongCyclicEmbeddingDegree_injective
    (n : ℕ) :
    Function.Injective
      (ccmRationalNonunitalStrongCyclicEmbeddingDegree n) := by
  intro x y hxy
  apply Subtype.ext
  apply ccmRationalNonunitalFieldToPointwiseCyclicDegree_injective n
  exact congrArg Subtype.val hxy

def ccmRationalNonunitalStrongCyclicEmbeddingComponent :
    ∀ j : SimplexCategoryGenRelᵒᵖ,
      CCMRationalNonunitalStrongCyclicTarget.simplicial.obj j ⟶
        CCMRationalStrongCyclicTarget.simplicial.obj j
  | .op (.mk n) =>
      ModuleCat.ofHom (ccmRationalNonunitalStrongCyclicEmbeddingDegree n)

def ccmRationalNonunitalStrongCyclicEmbeddingSimplicial :
    CCMRationalNonunitalStrongCyclicTarget.simplicial ⟶
      CCMRationalStrongCyclicTarget.simplicial where
  app := ccmRationalNonunitalStrongCyclicEmbeddingComponent
  naturality {j k} h := by
    rcases j with ⟨⟨j⟩⟩
    rcases k with ⟨⟨k⟩⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hambient :=
      (cyclicBarAlgHomSimplicialHom
        ccmRationalNonunitalFieldToPointwiseAlgHom).naturality h
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hambient) x.1

/-- Faithful cyclic inclusion of literal Definition 4.9 into the larger
pointwise-field strong cyclic module. -/
def ccmRationalNonunitalStrongCyclicEmbedding :
    CyclicModule.Hom CCMRationalNonunitalStrongCyclicTarget
      CCMRationalStrongCyclicTarget where
  simplicial := ccmRationalNonunitalStrongCyclicEmbeddingSimplicial
  cyclic_naturality n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hambient :=
      (cyclicBarAlgHomCyclicHom
        ccmRationalNonunitalFieldToPointwiseAlgHom).cyclic_naturality n
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hambient) x.1

end GaloisForLFunctions.RHTower
