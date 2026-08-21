import GaloisForLFunctions.RHTower.Sieve.AlmostOrthogonality

namespace RHTower.Sieve

open Finset Complex
open scoped BigOperators ComplexConjugate

noncomputable section

private def jutilaKernel {ρ ν : Type*} [Fintype ρ] [Fintype ν]
    (x : ρ → ν → ℂ) (r s : ρ) (a : ν → ℂ) : ℂ :=
  ∑ n, a n * x r n * conj (x s n)

private def jutilaColumnGram {ρ ν : Type*} [Fintype ρ]
    (x : ρ → ν → ℂ) (n m : ν) : ℂ :=
  ∑ r, x r n * conj (x r m)

private theorem sum_four_rotate {α β γ δ M : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid M]
    (f : α → β → γ → δ → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ d, ∑ c, ∑ b, ∑ a, f a b c d := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
        ∑ a, ∑ b, ∑ d, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ c, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ a, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ b, ∑ a, f a b c d := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm

private theorem jutila_energy_expansion {ρ ν : Type*} [Fintype ρ] [Fintype ν]
    (x : ρ → ν → ℂ) (a : ν → ℂ) :
    ((∑ r, ∑ s, ‖jutilaKernel x r s a‖ ^ 2 : ℝ) : ℂ) =
      ∑ n, ∑ m, a n * conj (a m) *
        (jutilaColumnGram x n m * conj (jutilaColumnGram x n m)) := by
  simp only [jutilaKernel, jutilaColumnGram, Complex.ofReal_sum,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, map_sum, map_mul]
  simp only [conj_conj]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [sum_four_rotate]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem jutila_unweighted_energy_expansion {ρ ν : Type*} [Fintype ρ] [Fintype ν]
    (x : ρ → ν → ℂ) :
    (∑ r, ∑ s, ‖jutilaKernel x r s (fun _ => 1)‖ ^ 2 : ℝ) =
      ∑ n, ∑ m, ‖jutilaColumnGram x n m‖ ^ 2 := by
  have h := jutila_energy_expansion x (fun _ => 1)
  simp only [one_mul, map_one] at h
  have hre := congrArg Complex.re h
  simp_rw [Complex.re_sum] at hre
  simpa only [Complex.ofReal_re, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hre

theorem jutila_coefficient_removal {ρ ν : Type*} [Fintype ρ] [Fintype ν]
    (x : ρ → ν → ℂ) (a : ν → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, ‖a n‖ ≤ A) :
    ∑ r, ∑ s, ‖jutilaKernel x r s a‖ ^ 2 ≤
      A ^ 2 * ∑ r, ∑ s, ‖jutilaKernel x r s (fun _ => 1)‖ ^ 2 := by
  have hexp := jutila_energy_expansion x a
  have hre := congrArg Complex.re hexp
  have hre' :
      (∑ r, ∑ s, ‖jutilaKernel x r s a‖ ^ 2 : ℝ) =
        ∑ n, ∑ m, (a n * conj (a m)).re * ‖jutilaColumnGram x n m‖ ^ 2 := by
    simp_rw [Complex.re_sum] at hre
    simpa only [Complex.ofReal_re, Complex.mul_re,
      Complex.mul_conj, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.normSq_eq_norm_sq] using hre
  rw [hre', jutila_unweighted_energy_expansion]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  have hreBound : (a n * conj (a m)).re ≤ A ^ 2 := by
    calc
      (a n * conj (a m)).re ≤ ‖a n * conj (a m)‖ := Complex.re_le_norm _
      _ = ‖a n‖ * ‖a m‖ := by rw [norm_mul, norm_conj]
      _ ≤ A * A := mul_le_mul (ha n) (ha m) (norm_nonneg _) hA
      _ = A ^ 2 := by ring
  exact mul_le_mul_of_nonneg_right hreBound (sq_nonneg _)

end

end RHTower.Sieve
