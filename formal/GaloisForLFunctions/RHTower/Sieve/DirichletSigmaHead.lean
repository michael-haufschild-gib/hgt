import GaloisForLFunctions.RHTower.Sieve.DirichletSigmaTail
import GaloisForLFunctions.RHTower.Sieve.ZetaTruncated

/-!
# The head off the line

Below the split point the Dirichlet sum is controlled by the absolute values of its terms, which off
the line is `∑ n^(-σ)` rather than a harmonic sum.  The corpus already owns the integral-comparison
bound for that sum below the abscissa, so the head costs only the modulus computation.
-/

namespace RHTower.Sieve

open Finset

/-- The modulus of a Dirichlet term off the line. -/
theorem norm_dirichletSigmaTerm {n : ℕ} (hn : 1 ≤ n) (σ t : ℝ) :
    ‖(n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖ = ((n : ℝ)) ^ (-σ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n : ℕ) : ℂ) = (((n : ℝ) : ℝ) : ℂ) := by push_cast; ring
  have hre : (-(σ : ℂ) - Complex.I * (t : ℂ)).re = -σ := by simp
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn0, hre]

/-- **Head bound off the line.**  The corpus integral comparison controls `∑ n^(-σ)` below the
abscissa. -/
theorem norm_dirichlet_sigma_head_le {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {B : ℕ} (hB : 2 ≤ B) :
    ‖∑ n ∈ Finset.Icc 1 B, (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 1 + ((B : ℝ) ^ (1 - σ) - 1) / (1 - σ) + (B : ℝ) ^ (-σ) := by
  calc ‖∑ n ∈ Finset.Icc 1 B, (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ ∑ n ∈ Finset.Icc 1 B, ‖(n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 B, ((n : ℝ)) ^ (-σ) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        exact norm_dirichletSigmaTerm (Finset.mem_Icc.mp hn).1 σ t
    _ ≤ 1 + ((B : ℝ) ^ (1 - σ) - 1) / (1 - σ) + (B : ℝ) ^ (-σ) :=
        sum_rpow_neg_le_of_lt_one hσ0 hσ1 hB

/-- **Head and tail off the line.**  A single integral-comparison term for everything below the
split point, plus one supplied bound per dyadic block above it. -/
theorem norm_dirichlet_sigma_partial_of_blockBound {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {C R : ℕ} (hC : 3 ≤ C) (b : ℕ → ℝ)
    (hb : ∀ r < R,
      ‖∑ n ∈ Finset.Ico (C * 2 ^ r) (C * 2 ^ (r + 1)),
          (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖ ≤ b r) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (C * 2 ^ R), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ (1 + (((C - 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ) + ((C - 1 : ℕ) : ℝ) ^ (-σ))
        + ∑ r ∈ Finset.range R, b r := by
  have hC1 : 1 ≤ C := by omega
  have hCle : C ≤ C * 2 ^ R := by
    calc C = C * 1 := (Nat.mul_one C).symm
      _ ≤ C * 2 ^ R := Nat.mul_le_mul_left C Nat.one_le_two_pow
  have hsplit :
      (∑ n ∈ Finset.Ico 1 C, (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ)))
        + (∑ n ∈ Finset.Ico C (C * 2 ^ R), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ)))
      = ∑ n ∈ Finset.Ico 1 (C * 2 ^ R), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ)) :=
    Finset.sum_Ico_consecutive _ hC1 hCle
  have hIco : Finset.Ico 1 C = Finset.Icc 1 (C - 1) := by
    obtain ⟨B, rfl⟩ : ∃ B, C = B + 1 := ⟨C - 1, by omega⟩
    simpa using Finset.Ico_add_one_right_eq_Icc 1 B
  rw [← hsplit]
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add ?_ (norm_sum_Ico_dyadic_of_blockBound C R _ b hb)
  rw [hIco]
  exact norm_dirichlet_sigma_head_le hσ0 hσ1 (by omega)

end RHTower.Sieve
