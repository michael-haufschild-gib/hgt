import GaloisForLFunctions.HeckeKreinToeplitz.Index.OneNegativeDirection
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Completing algebraic index-one isometries

An algebraic isometry of the form on `H × ℂ` is automatically bounded.
Its scalar coordinate is controlled by pairing against the inverse image
of `(0,1)`; preservation of the square then controls its positive component.
Consequently it extends to an isometry on the completed positive space.
-/

noncomputable section
set_option autoImplicit false
open Complex UniformSpace
open scoped ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.HeckeKreinToeplitz.IndexOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_pairing_le (v w : H × ℂ) :
    ‖pairing v w‖ ≤ (‖v.1‖ + ‖v.2‖) * ‖w‖ := by
  calc
    ‖pairing v w‖ ≤ ‖inner ℂ v.1 w.1‖ + ‖conj v.2 * w.2‖ := norm_sub_le _ _
    _ ≤ ‖v.1‖ * ‖w.1‖ + ‖v.2‖ * ‖w.2‖ := by
      rw [norm_mul, norm_conj]
      exact add_le_add (norm_inner_le_norm (𝕜 := ℂ) v.1 w.1) le_rfl
    _ ≤ ‖v.1‖ * ‖w‖ + ‖v.2‖ * ‖w‖ := add_le_add
      (mul_le_mul_of_nonneg_left (norm_fst_le w) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (norm_snd_le w) (norm_nonneg _))
    _ = _ := (add_mul _ _ _).symm

/-- Every algebraic form-isometry is bounded in the product norm. -/
theorem exists_norm_bound (T : (H × ℂ) ≃ₗ[ℂ] (H × ℂ))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w) :
    ∃ C : ℝ, ∀ v, ‖T v‖ ≤ C * ‖v‖ := by
  let u := T.symm (0, (1 : ℂ))
  let C : ℝ := ‖u.1‖ + ‖u.2‖
  have hC : 0 ≤ C := add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨1 + C, fun v => ?_⟩
  have hs : ‖(T v).2‖ ≤ C * ‖v‖ := by
    have he : pairing u v = -(T v).2 := by
      rw [← hT u v, LinearEquiv.apply_symm_apply]
      simp only [pairing, inner_zero_left, map_one, one_mul, zero_sub]
    simpa only [he, norm_neg] using norm_pairing_le u v
  have hq := congrArg Complex.re (hT v v)
  rw [pairing_self_re, pairing_self_re] at hq
  have hf : ‖(T v).1‖ ≤ ‖v‖ + ‖(T v).2‖ := by
    have hfst := norm_fst_le v
    have hfst2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hfst
    have hcross : 0 ≤ ‖v‖ * ‖(T v).2‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith only [hq, hfst2, sq_nonneg ‖v.2‖, hcross,
      norm_nonneg (T v).1, norm_nonneg v, norm_nonneg (T v).2]
  rw [Prod.norm_def]
  apply max_le
  · calc
      ‖(T v).1‖ ≤ ‖v‖ + ‖(T v).2‖ := hf
      _ ≤ ‖v‖ + C * ‖v‖ := add_le_add le_rfl hs
      _ = (1 + C) * ‖v‖ := by ring
  · exact hs.trans (by nlinarith only [norm_nonneg v])

/-- Completing the positive coordinate leaves the negative scalar unchanged. -/
def completionEmbedding : (H × ℂ) →ₗ[ℂ] (Completion H × ℂ) where
  toFun v := ((v.1 : Completion H), v.2)
  map_add' v w := by simp only [Prod.fst_add, Prod.snd_add, Completion.coe_add]; rfl
  map_smul' c v := by simp only [Prod.smul_fst, Prod.smul_snd, Completion.coe_smul]; rfl

theorem completionEmbedding_norm (v : H × ℂ) : ‖completionEmbedding v‖ = ‖v‖ := by
  simp only [Prod.norm_def, completionEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
    Completion.norm_coe]

theorem completionEmbedding_pairing (v w : H × ℂ) :
    pairing (completionEmbedding v) (completionEmbedding w) = pairing v w := by
  exact congrArg (fun a : ℂ => a - conj v.2 * w.2) (Completion.inner_coe v.1 w.1)

theorem completionEmbedding_dense : DenseRange (completionEmbedding (H := H)) := by
  exact Completion.denseRange_coe.prodMap (Function.surjective_id.denseRange)

/-- Extension of an algebraic form-isometry to the complete index-one space. -/
def completedIsometry (T : (H × ℂ) ≃ₗ[ℂ] (H × ℂ))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w) :
    (Completion H × ℂ) ≃L[ℂ] (Completion H × ℂ) :=
  T.extend completionEmbedding completionEmbedding completionEmbedding_dense
    (by simpa only [completionEmbedding_norm] using exists_norm_bound T hT)
    completionEmbedding_dense (by
      have hinv : ∀ v w, pairing (T.symm v) (T.symm w) = pairing v w := by
        intro v w
        simpa only [LinearEquiv.apply_symm_apply] using (hT (T.symm v) (T.symm w)).symm
      simpa only [completionEmbedding_norm] using exists_norm_bound T.symm hinv)

theorem completedIsometry_embedding (T : (H × ℂ) ≃ₗ[ℂ] (H × ℂ))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w) (v : H × ℂ) :
    completedIsometry T hT (completionEmbedding v) = completionEmbedding (T v) :=
  LinearEquiv.extend_eq _ _ _ _ _ _ _ v

theorem continuous_pairing : Continuous (fun p : (H × ℂ) × (H × ℂ) => pairing p.1 p.2) := by
  unfold pairing
  fun_prop

theorem completedIsometry_pairing (T : (H × ℂ) ≃ₗ[ℂ] (H × ℂ))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w)
    (v w : Completion H × ℂ) :
    pairing (completedIsometry T hT v) (completedIsometry T hT w) = pairing v w := by
  refine (completionEmbedding_dense (H := H)).induction_on₂ ?_ ?_ v w
  · exact isClosed_eq (continuous_pairing.comp
      ((completedIsometry T hT).continuous.prodMap (completedIsometry T hT).continuous))
      continuous_pairing
  · intro x y
    rw [completedIsometry_embedding, completedIsometry_embedding,
      completionEmbedding_pairing, completionEmbedding_pairing, hT]

end GaloisForLFunctions.HeckeKreinToeplitz.IndexOne
