import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteNegativeDirections
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Completing isometries with a finite negative factor

An algebraic isometry of a difference of Hilbert forms is bounded when the
negative factor is finite-dimensional. The inverse restricted to that factor
is automatically continuous; pairing against it controls the negative
coordinate. Preservation of the square controls the positive coordinate.
-/

noncomputable section
set_option autoImplicit false
open Complex UniformSpace
open scoped ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Every algebraic form-isometry with a finite negative factor is bounded. -/
theorem exists_norm_bound [FiniteDimensional ℂ E] (T : (H × E) ≃ₗ[ℂ] (H × E))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w) :
    ∃ C : ℝ, ∀ v, ‖T v‖ ≤ C * ‖v‖ := by
  let U : E →L[ℂ] (H × E) := LinearMap.toContinuousLinearMap
    (T.symm.toLinearMap.comp (LinearMap.inr ℂ H E))
  have hU (x : E) : T (U x) = (0, x) := T.apply_symm_apply _
  let C : ℝ := 2 * ‖U‖
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (norm_nonneg U)
  refine ⟨1 + C, fun v => ?_⟩
  have hs : ‖(T v).2‖ ≤ C * ‖v‖ := by
    have he : pairing (U (T v).2) v = -inner ℂ (T v).2 (T v).2 := by
      rw [← hT, hU]
      simp only [pairing, inner_zero_left, zero_sub]
    have hnorm : ‖(T v).2‖ ^ 2 = ‖pairing (U (T v).2) v‖ := by
      rw [he, norm_neg, GaloisForLFunctions.HTGeometry.norm_inner_self_eq]
    have hsum : ‖(U (T v).2).1‖ + ‖(U (T v).2).2‖ ≤ 2 * (‖U‖ * ‖(T v).2‖) := by
      calc
        _ ≤ 2 * ‖U (T v).2‖ := by
          linarith only [norm_fst_le (U (T v).2), norm_snd_le (U (T v).2)]
        _ ≤ _ := mul_le_mul_of_nonneg_left (U.le_opNorm _) (by norm_num)
    have hsq : ‖(T v).2‖ * ‖(T v).2‖ ≤ ‖(T v).2‖ * (C * ‖v‖) := by
      calc
        _ = ‖pairing (U (T v).2) v‖ := by rw [← hnorm, pow_two]
        _ ≤ (‖(U (T v).2).1‖ + ‖(U (T v).2).2‖) * ‖v‖ := norm_pairing_le _ _
        _ ≤ (2 * (‖U‖ * ‖(T v).2‖)) * ‖v‖ :=
          mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
        _ = _ := by dsimp only [C]; ring
    by_cases hz : (T v).2 = 0
    · rw [hz, norm_zero]
      exact mul_nonneg hC (norm_nonneg _)
    · exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hz)).mp hsq
  have hq := congrArg Complex.re (hT v v)
  rw [pairing_self_re, pairing_self_re] at hq
  have hf : ‖(T v).1‖ ≤ ‖v‖ + ‖(T v).2‖ := by
    have hfst2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_fst_le v)
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

/-- Complete only the positive Hilbert coordinate. -/
def completionEmbedding : (H × E) →ₗ[ℂ] (Completion H × E) where
  toFun v := ((v.1 : Completion H), v.2)
  map_add' v w := by simp only [Prod.fst_add, Prod.snd_add, Completion.coe_add]; rfl
  map_smul' c v := by simp only [Prod.smul_fst, Prod.smul_snd, Completion.coe_smul]; rfl

theorem completionEmbedding_norm (v : H × E) : ‖completionEmbedding v‖ = ‖v‖ := by
  simp only [Prod.norm_def, completionEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
    Completion.norm_coe]

theorem completionEmbedding_pairing (v w : H × E) :
    pairing (completionEmbedding v) (completionEmbedding w) = pairing v w :=
  congrArg (fun a : ℂ => a - inner ℂ v.2 w.2) (Completion.inner_coe v.1 w.1)

theorem completionEmbedding_dense : DenseRange (completionEmbedding (H := H) (E := E)) :=
  Completion.denseRange_coe.prodMap (Function.surjective_id.denseRange)

variable [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- The unique continuous extension of an algebraic form-isometry. -/
def completedIsometry (T : (H × E) ≃ₗ[ℂ] (H × E))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w) :
    (Completion H × E) ≃L[ℂ] (Completion H × E) :=
  T.extend completionEmbedding completionEmbedding completionEmbedding_dense
    (by simpa only [completionEmbedding_norm] using exists_norm_bound T hT)
    completionEmbedding_dense (by
      have hinv : ∀ v w, pairing (T.symm v) (T.symm w) = pairing v w := by
        intro v w
        simpa only [LinearEquiv.apply_symm_apply] using (hT (T.symm v) (T.symm w)).symm
      simpa only [completionEmbedding_norm] using exists_norm_bound T.symm hinv)

theorem completedIsometry_embedding (T : (H × E) ≃ₗ[ℂ] (H × E))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w) (v : H × E) :
    completedIsometry T hT (completionEmbedding v) = completionEmbedding (T v) :=
  LinearEquiv.extend_eq _ _ _ _ _ _ _ v

theorem completedIsometry_pairing (T : (H × E) ≃ₗ[ℂ] (H × E))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w)
    (v w : Completion H × E) :
    pairing (completedIsometry T hT v) (completedIsometry T hT w) = pairing v w := by
  refine (completionEmbedding_dense (H := H) (E := E)).induction_on₂ ?_ ?_ v w
  · exact isClosed_eq (continuous_pairing.comp
      ((completedIsometry T hT).continuous.prodMap (completedIsometry T hT).continuous))
      continuous_pairing
  · intro x y
    rw [completedIsometry_embedding, completedIsometry_embedding,
      completionEmbedding_pairing, completionEmbedding_pairing, hT]

#print axioms exists_norm_bound
#print axioms completedIsometry_pairing

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
