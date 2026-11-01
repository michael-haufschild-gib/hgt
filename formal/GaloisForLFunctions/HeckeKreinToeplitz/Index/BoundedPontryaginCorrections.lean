import GaloisForLFunctions.HeckeKreinToeplitz.FiniteIndexIsPositiveMinusFiniteRank

/-!
# Bounded correction functions for finite-index kernels

The correction functions in a Pontryagin decomposition are finite sums of
translates of the kernel. A bounded kernel therefore admits bounded
corrections, with a common bound independent of the tested finite family.
-/

noncomputable section

open Complex Finset
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G]

/-- A finite-index bounded Hermitian kernel has a bounded family of exactly
as many correction functions as its negative index. -/
theorem exists_bounded_pontryagin_corrections {k : G → ℂ}
    (hk : IsHermKernel k) {m : ℕ} (hm : negIndex k = m)
    (hbounded : ∃ M : ℝ, ∀ g, ‖k g‖ ≤ M) :
    ∃ (n₀ : ℕ) (x₀ : Fin n₀ → G) (w : Fin m → Fin n₀ → ℂ) (C : ℝ),
      0 ≤ C ∧ (∀ i g, ‖∑ b, w i b * k ((x₀ b)⁻¹ * g)‖ ≤ C) ∧
      ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
        0 ≤ hermQuad (gram k x) c +
          ∑ i, normSq (∑ a, c a * ∑ b, w i b * k ((x₀ b)⁻¹ * x a)) := by
  classical
  obtain ⟨M, hM⟩ := hbounded
  have hM0 : 0 ≤ M := (norm_nonneg (k 1)).trans (hM 1)
  obtain ⟨n₀, x₀, w, hw⟩ := exists_pontryagin_decomposition hk hm
  let φ : Fin m → G → ℂ := fun i g => ∑ b, w i b * k ((x₀ b)⁻¹ * g)
  let C : ℝ := ∑ i, ∑ b, ‖w i b‖ * M
  have hC : 0 ≤ C := sum_nonneg fun i _ => sum_nonneg fun b _ =>
    mul_nonneg (norm_nonneg _) hM0
  refine ⟨n₀, x₀, w, C, hC, ?_, hw⟩
  intro i g
  calc
    ‖φ i g‖ ≤ ∑ b, ‖w i b * k ((x₀ b)⁻¹ * g)‖ := norm_sum_le _ _
    _ ≤ ∑ b, ‖w i b‖ * M := sum_le_sum fun b _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
    _ ≤ C := single_le_sum
      (fun j _ => sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) hM0)
      (mem_univ i)

end GaloisForLFunctions.HeckeKreinToeplitz
