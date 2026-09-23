import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.RHTower.Sieve.RamarePhaseError

/-!
# Counting squarefree integers

`μ(n)² = Σ_{d² ∣ n} μ(d)` turns the squarefree counting function into the exact divisor sum
`Σ_{n ≤ N} μ(n)² = Σ_{d ≤ N} μ(d) ⌊N/d²⌋`, in which only `d ≤ √N` contributes.
-/

namespace RHTower

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

/-- The squarefree indicator is the sum of `μ(d)` over `d` with `d² ∣ n`, indexed by the interval
`[1, n]`.  `GaloisForLFunctions.HTGeometry.sum_moebius_sq_dvd` is the same identity indexed by
`n.divisors`. -/
theorem sum_moebius_sq_dvd_Icc {n : ℕ} (hn : 1 ≤ n) :
    ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d * d ∣ n), (μ d : ℤ) = (μ n : ℤ) ^ (2 : ℕ) := by
  have hn0 : n ≠ 0 := by omega
  have hconv : (sqrtPart (μ : ArithmeticFunction ℤ) * (ζ : ArithmeticFunction ℤ)) n
      = (μ n : ℤ) ^ (2 : ℕ) := by
    rw [sqrtPart_moebius_mul_zeta, pmul_apply]
    ring
  rw [← hconv, coe_mul_zeta_apply]
  have hrestrict : ∑ e ∈ n.divisors, sqrtPart (μ : ArithmeticFunction ℤ) e
      = ∑ e ∈ n.divisors.filter (fun e => Nat.sqrt e * Nat.sqrt e = e),
          sqrtPart (μ : ArithmeticFunction ℤ) e := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro e he hne
    rw [Finset.mem_filter] at hne
    rw [not_and] at hne
    rw [sqrtPart_apply, if_neg (hne he)]
  rw [hrestrict]
  refine Finset.sum_nbij' (i := fun d => d * d) (j := fun e => Nat.sqrt e) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨hd.2, hn0⟩, ?_⟩
    rw [show d * d = d ^ (2 : ℕ) by ring, Nat.sqrt_eq']
    ring
  · intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hediv : e ∣ n := he.1.1
    have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      rw [h0] at hediv
      omega)
    have hen : e ≤ n := Nat.le_of_dvd (by omega) hediv
    have hs1 : 1 ≤ Nat.sqrt e := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      rw [h0] at he
      simp at he
      omega
    refine ⟨⟨hs1, ?_⟩, ?_⟩
    · calc Nat.sqrt e ≤ e := Nat.sqrt_le_self e
        _ ≤ n := hen
    · rw [he.2]
      exact hediv
  · intro d hd
    rw [show d * d = d ^ (2 : ℕ) by ring]
    exact Nat.sqrt_eq' d
  · intro e he
    simp only [Finset.mem_filter] at he
    exact he.2
  · intro d hd
    rw [show d * d = d ^ (2 : ℕ) by ring, sqrtPart_apply_sq]

/-- **The squarefree counting identity.**  `Σ_{n ≤ N} μ(n)² = Σ_{d ≤ N} μ(d) ⌊N/d²⌋`. -/
theorem sum_moebius_sq_Icc (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (μ n : ℤ) ^ (2 : ℕ)
      = ∑ d ∈ Finset.Icc 1 N, (μ d : ℤ) * ((N / (d * d) : ℕ) : ℤ) := by
  classical
  have hstep : ∀ n ∈ Finset.Icc 1 N, (μ n : ℤ) ^ (2 : ℕ)
      = ∑ d ∈ Finset.Icc 1 N, (if d * d ∣ n then (μ d : ℤ) else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [← sum_moebius_sq_dvd_Icc hn.1, Finset.sum_filter]
    refine Finset.sum_subset ?_ ?_
    · intro d hd
      rw [Finset.mem_Icc] at hd ⊢
      exact ⟨hd.1, le_trans hd.2 hn.2⟩
    · intro d hd hdn
      rw [Finset.mem_Icc] at hd hdn
      have hgt : n < d := by omega
      by_cases hdvd : d * d ∣ n
      · exfalso
        have hle : d * d ≤ n := Nat.le_of_dvd (by omega) hdvd
        nlinarith [hd.1]
      · rw [if_neg hdvd]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    RHTower.Sieve.card_Icc_filter_dvd N (d * d)]
  ring

end

end RHTower
