import GaloisForLFunctions.RepresentationLifting.Hecke.PermutationSpecialization
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The two-dimensional Hecke augmentation kernel

An explicit basis identifies the weighted-augmentation kernel at every parameter.
Its commutator detects the exact divisor admitting a common eigenline.
-/

noncomputable section
open Matrix
namespace GaloisForLFunctions.RepresentationLifting.Hecke

/-- First generator in the universal basis of the weighted-augmentation kernel. -/
def kernelLeft (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![t - 1, 1; t, 0]

/-- Second generator in the same basis, valid at every specialization. -/
def kernelRight (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![t, 0; -t ^ 2, -1]

/-- The commutator detects exactly the zero and cubic exceptional parameters. -/
theorem kernel_commutator_det (t : ℂ) :
    (kernelLeft t * kernelRight t - kernelRight t * kernelLeft t).det = t * (t ^ 2 + t + 1) := by
  simp [Matrix.det_fin_two, kernelLeft, kernelRight]
  ring

/-- Every kernel vector is uniquely represented by its first two coordinates. -/
def kernelEmbedding (t : ℂ) : (Fin 2 → ℂ) →ₗ[ℂ] Triple where
  toFun v := (v 0, v 1, -t ^ 2 * v 0 - t * v 1)
  map_add' _ _ := by ext <;> simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' _ _ := by ext <;> simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring

theorem kernelEmbedding_left (t : ℂ) (v : Fin 2 → ℂ) :
    permutationLeft t (kernelEmbedding t v) = kernelEmbedding t (kernelLeft t *ᵥ v) := by
  ext <;> simp [permutationLeft, kernelEmbedding, kernelLeft, dotProduct, Fin.sum_univ_two] <;> ring

theorem kernelEmbedding_right (t : ℂ) (v : Fin 2 → ℂ) :
    permutationRight t (kernelEmbedding t v) = kernelEmbedding t (kernelRight t *ᵥ v) := by
  ext <;> simp [permutationRight, kernelEmbedding, kernelRight, dotProduct, Fin.sum_univ_two] <;> ring

/-- The displayed two-dimensional action is the actual augmentation kernel, without a parameter restriction. -/
def permutationKernelEquiv (t : ℂ) :
    (Fin 2 → ℂ) ≃ₗ[ℂ] LinearMap.ker (permutationAugmentation t) where
  toFun v := ⟨kernelEmbedding t v, by
    change t ^ 2 * v 0 + t * v 1 + (-t ^ 2 * v 0 - t * v 1) = 0
    ring⟩
  invFun v := ![v.val.1, v.val.2.1]
  left_inv v := by
    funext i
    fin_cases i <;> rfl
  right_inv v := by
    apply Subtype.ext
    have hv := v.property
    change t ^ 2 * v.val.1 + t * v.val.2.1 + v.val.2.2 = 0 at hv
    ext
    · rfl
    · rfl
    · change -t ^ 2 * v.val.1 - t * v.val.2.1 = v.val.2.2
      linear_combination -hv
  map_add' v w := Subtype.ext ((kernelEmbedding t).map_add v w)
  map_smul' c v := Subtype.ext ((kernelEmbedding t).map_smul c v)

/-- A common eigenline exists exactly at the exceptional commutator divisor. -/
theorem kernel_common_eigenvector_iff (t : ℂ) :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ ∃ a b : ℂ,
      kernelLeft t *ᵥ v = a • v ∧ kernelRight t *ᵥ v = b • v) ↔
      t = 0 ∨ t ^ 2 + t + 1 = 0 := by
  constructor
  · rintro ⟨v, hv, a, b, ha, hb⟩
    have hc : (kernelLeft t * kernelRight t - kernelRight t * kernelLeft t) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hb, ha, Matrix.mulVec_smul, Matrix.mulVec_smul, ha, hb, smul_smul, smul_smul,
        mul_comm b a, sub_self]
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp [kernelLeft, kernelRight, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at h0 h1
    have hx : (t * (t ^ 2 + t + 1)) * v 0 = 0 := by
      linear_combination t ^ 2 * h0 + (t + 1) * h1
    have hy : (t * (t ^ 2 + t + 1)) * v 1 = 0 := by
      linear_combination -(t ^ 3 + t) * h0 - t ^ 2 * h1
    have hd : t * (t ^ 2 + t + 1) = 0 := by
      by_contra hd
      have hv0 := (mul_eq_zero.mp hx).resolve_left hd
      have hv1 := (mul_eq_zero.mp hy).resolve_left hd
      apply hv
      funext i
      fin_cases i
      · exact hv0
      · exact hv1
    exact mul_eq_zero.mp hd
  · rintro (rfl | ht)
    · refine ⟨![1, 0], ?_, -1, 0, ?_, ?_⟩
      · intro h
        have hh := congrFun h 0
        exact one_ne_zero hh
      · ext i
        fin_cases i <;> simp [kernelLeft, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · ext i
        fin_cases i <;> simp [kernelRight, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · refine ⟨![1, 1], ?_, t, t, ?_, ?_⟩
      · intro h
        have hh := congrFun h 0
        exact one_ne_zero hh
      · ext i
        fin_cases i <;> simp [kernelLeft, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · ext i
        fin_cases i
        · simp [kernelRight, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        · simp [kernelRight, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          linear_combination -ht

#print axioms kernel_commutator_det
#print axioms permutationKernelEquiv
#print axioms kernel_common_eigenvector_iff
end GaloisForLFunctions.RepresentationLifting.Hecke
