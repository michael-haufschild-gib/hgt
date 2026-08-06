import GaloisForLFunctions.RHTower.Sieve.DirichletConstantOrder

/-!
# The shape with a power-of-two split

Specialising the base point to `A = 2` turns every block base into a power of two, so the two
logarithms appearing in the endpoint conditions and in the conclusion become explicit multiples of
`log 2`.  What remains is arithmetic in the exponents `S`, `R`, the order `K`, and the target `ε` —
no logarithm of a composite natural survives.
-/

namespace RHTower.Sieve

open Finset

/-- **Power-of-two form.**  With `A = 2` the harmonic term is `(S+1)·log 2` and the depth criterion
reads against the same quantity. -/
theorem norm_dirichlet_partial_littlewood_pow_two {t : ℝ} (ht : 0 < t) {S R K : ℕ} (hSR : S < R)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 2560) (hK : 2 ≤ K)
    (hfacS : Nat.factorial (K - 1) ≤ 2 ^ (S + 1))
    (hhighS : t ≤ 2 * Real.pi * 2 ^ K * ((2 ^ (S + 1) : ℕ) : ℝ) ^ (K - 1)
      * ((2 ^ (S + 1) : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hdeepS : 3 * (2 : ℝ) ^ K * Real.log (2560 / ε) ≤ ((S : ℝ) + 1) * Real.log 2)
    (hlowTop : 8 * Real.pi * ((2 ^ R : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (R + 1)), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + ((S : ℝ) + 1) * Real.log 2 + ((R - S : ℕ) : ℝ) * ε := by
  have hbaseS : 2 * 2 ^ S = 2 ^ (S + 1) := by ring
  have hbaseTop : 2 * 2 ^ (R - 1) = 2 ^ R := by
    obtain ⟨j, rfl⟩ : ∃ j, R = j + 1 := ⟨R - 1, by omega⟩
    simp [pow_succ]
    ring
  have hbaseR : 2 * 2 ^ R = 2 ^ (R + 1) := by ring
  have hlogS : Real.log ((2 ^ (S + 1) : ℕ) : ℝ) = ((S : ℝ) + 1) * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have hlogSm : Real.log ((2 ^ (S + 1) - 1 : ℕ) : ℝ) ≤ ((S : ℝ) + 1) * Real.log 2 := by
    rw [← hlogS]
    have hpos : (0 : ℝ) < ((2 ^ (S + 1) - 1 : ℕ) : ℝ) := by
      have h1 : 1 ≤ 2 ^ (S + 1) - 1 := by
        have : 2 ≤ 2 ^ (S + 1) := by
          calc 2 = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ (S + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact_mod_cast h1
    refine Real.log_le_log hpos ?_
    exact_mod_cast Nat.sub_le _ _
  have hmain := norm_dirichlet_partial_littlewood_const (t := t) (A := 2) (S := S) (R := R)
    (K := K) ht (by norm_num) hSR hε hε' hK
    (by rw [hbaseS]; exact hfacS)
    (by rw [hbaseTop]; exact hlowTop)
    (by rw [hbaseS]; exact hhighS)
    (by rw [hbaseS, hlogS]; exact hdeepS)
  rw [hbaseR, hbaseS] at hmain
  refine le_trans hmain ?_
  have : 1 + Real.log ((2 ^ (S + 1) - 1 : ℕ) : ℝ) ≤ 1 + ((S : ℝ) + 1) * Real.log 2 := by
    linarith
  linarith

end RHTower.Sieve
