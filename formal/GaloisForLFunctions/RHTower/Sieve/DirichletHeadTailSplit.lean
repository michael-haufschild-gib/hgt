import GaloisForLFunctions.RHTower.Sieve.DirichletDyadicTailAssembly
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Head and tail of the Dirichlet sum on the line `Re s = 1`

On the line `Re s = 1` each Dirichlet term has modulus `1/n`, so a head segment is bounded by a
harmonic sum and contributes `1 + log` of its length.  Beyond the head the dyadic block estimates
apply, and the two pieces combine into a bound for the whole partial sum.

The split point is free: the head bound grows like `log A` while each dyadic block above `A` saves,
so the assembly chooses `A` to balance the two.
-/

namespace RHTower.Sieve

open Finset

/-- On the line `Re s = 1` the Dirichlet term has modulus `1/n`. -/
theorem norm_dirichletTerm {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    ‖(n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖ = ((n : ℝ))⁻¹ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n : ℕ) : ℂ) = (((n : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  simp [Real.rpow_neg_one]

/-- **Head bound.**  The initial segment is controlled by the harmonic sum. -/
theorem norm_dirichlet_head_le {A : ℕ} (hA : 1 ≤ A) (t : ℝ) :
    ‖∑ n ∈ Finset.Ico 1 A, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + Real.log ((A - 1 : ℕ) : ℝ) := by
  obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
  have hIco : Finset.Ico 1 (B + 1) = Finset.Icc 1 B := Finset.Ico_add_one_right_eq_Icc 1 B
  calc ‖∑ n ∈ Finset.Ico 1 (B + 1), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ ∑ n ∈ Finset.Ico 1 (B + 1), ‖(n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖ :=
        norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 B, 1 / (n : ℝ) := by
        rw [hIco]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [norm_dirichletTerm (Finset.mem_Icc.mp hn).1 t, one_div]
    _ ≤ 1 + Real.log (B : ℝ) := sum_Icc_one_div_le_one_add_log B
    _ = 1 + Real.log ((B + 1 - 1 : ℕ) : ℝ) := by norm_num

/-- **Head and tail combined.**  With the dyadic schedule available above the split point, the whole
partial sum on the line `Re s = 1` splits into a harmonic head and the sum of the block savings. -/
theorem norm_dirichlet_partial_le {t : ℝ} (ht : 0 < t) {A R : ℕ} (hA : 1 ≤ A) (k : ℕ → ℕ)
    (hk : ∀ r < R, 2 ≤ k r)
    (hfac : ∀ r < R, Nat.factorial (k r - 1) ≤ A * 2 ^ r)
    (hlow : ∀ r < R, 8 * Real.pi * ((A * 2 ^ r : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : ∀ r < R, t ≤ 2 * Real.pi * 2 ^ (k r) * ((A * 2 ^ r : ℕ) : ℝ) ^ (k r - 1)
      * ((A * 2 ^ r : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖∑ n ∈ Finset.Ico 1 (A * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ (1 + Real.log ((A - 1 : ℕ) : ℝ))
        + ∑ r ∈ Finset.range R,
            2560 * ((A * 2 ^ r : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ (k r)))) := by
  have hAle : A ≤ A * 2 ^ R := by
    calc A = A * 1 := (Nat.mul_one A).symm
      _ ≤ A * 2 ^ R := Nat.mul_le_mul_left A Nat.one_le_two_pow
  have hsplit :
      (∑ n ∈ Finset.Ico 1 A, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)))
        + (∑ n ∈ Finset.Ico A (A * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)))
      = ∑ n ∈ Finset.Ico 1 (A * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)) :=
    Finset.sum_Ico_consecutive _ hA hAle
  rw [← hsplit]
  refine le_trans (norm_add_le _ _) ?_
  exact add_le_add (norm_dirichlet_head_le hA t)
    (dirichlet_tail_dyadic_le ht hA k hk hfac hlow hhigh)

end RHTower.Sieve
