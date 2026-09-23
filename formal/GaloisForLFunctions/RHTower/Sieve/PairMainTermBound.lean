import GaloisForLFunctions.RHTower.Sieve.TruncatedPairCount
import GaloisForLFunctions.RHTower.Sieve.SquarefreeHarmonic

/-!
# The pair main term is bounded

The main term of the truncated pair count is dominated by the square of the inverse-square sum:

`|∑_{d,e ≤ R, (d,e)=1} μ(d)μ(e)/(d²e²)| ≤ (∑_{d ≤ R} 1/d²)² ≤ 4`,

uniformly in `R`.  Combined with `abs_truncated_pair_sub_le` this makes the truncated pair sum
`O(L) + O(R²)` with explicit constants, without any Euler-product evaluation of the density.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **The pair main term is at most `4`.** -/
theorem abs_main_pair_le (R : ℕ) :
    |∑ p ∈ {p ∈ Finset.Icc 1 R ×ˢ Finset.Icc 1 R | Nat.Coprime p.1 p.2},
        ((moebius p.1 : ℤ) : ℝ) * ((moebius p.2 : ℤ) : ℝ)
          / ((p.1 : ℝ) ^ (2 : ℕ) * (p.2 : ℝ) ^ (2 : ℕ))| ≤ 4 := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ {p ∈ Finset.Icc 1 R ×ˢ Finset.Icc 1 R | Nat.Coprime p.1 p.2},
      |((moebius p.1 : ℤ) : ℝ) * ((moebius p.2 : ℤ) : ℝ)
        / ((p.1 : ℝ) ^ (2 : ℕ) * (p.2 : ℝ) ^ (2 : ℕ))|
        ≤ (1 / (p.1 : ℝ) ^ (2 : ℕ)) * (1 / (p.2 : ℝ) ^ (2 : ℕ)) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hd1, _⟩, ⟨he1, _⟩⟩, _⟩ := hp
    have hd : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hd1
    have he : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast he1
    have h1 : |((moebius p.1 : ℤ) : ℝ)| ≤ 1 := by
      rcases moebius_trichotomy p.1 with hm | hm | hm <;> rw [hm] <;> norm_num
    have h2 : |((moebius p.2 : ℤ) : ℝ)| ≤ 1 := by
      rcases moebius_trichotomy p.2 with hm | hm | hm <;> rw [hm] <;> norm_num
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (p.1:ℝ)^(2 : ℕ)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (p.2:ℝ)^(2 : ℕ))]
    have hnum : |((moebius p.1 : ℤ) : ℝ)| * |((moebius p.2 : ℤ) : ℝ)| ≤ 1 :=
      mul_le_one₀ h1 (abs_nonneg _) h2
    have hden : (0 : ℝ) < (p.1 : ℝ) ^ (2 : ℕ) * (p.2 : ℝ) ^ (2 : ℕ) := by positivity
    rw [div_le_iff₀ hden]
    calc |((moebius p.1 : ℤ) : ℝ)| * |((moebius p.2 : ℤ) : ℝ)| ≤ 1 := hnum
      _ = (1 / (p.1 : ℝ) ^ (2 : ℕ) * (1 / (p.2 : ℝ) ^ (2 : ℕ))) * ((p.1 : ℝ) ^ (2 : ℕ) * (p.2 : ℝ) ^ (2 : ℕ)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hsub : {p ∈ Finset.Icc 1 R ×ˢ Finset.Icc 1 R | Nat.Coprime p.1 p.2}
      ⊆ Finset.Icc 1 R ×ˢ Finset.Icc 1 R := Finset.filter_subset _ _
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity) ?_
  rw [Finset.sum_product]
  have hinner : ∀ d ∈ Finset.Icc 1 R,
      ∑ e ∈ Finset.Icc 1 R, (1 / (d : ℝ) ^ (2 : ℕ)) * (1 / (e : ℝ) ^ (2 : ℕ))
        = (1 / (d : ℝ) ^ (2 : ℕ)) * ∑ e ∈ Finset.Icc 1 R, 1 / (e : ℝ) ^ (2 : ℕ) := by
    intro d _
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
  have hsq := sum_inv_sq_le_two R
  have hnn : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 R, 1 / (d : ℝ) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun d _ => by positivity
  nlinarith [hsq, hnn]

end RHTower.Sieve
