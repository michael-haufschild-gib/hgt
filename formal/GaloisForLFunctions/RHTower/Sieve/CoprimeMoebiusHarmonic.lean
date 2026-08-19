import GaloisForLFunctions.RHTower.Sieve.TotientDiagonalWeight
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap

/-!
# The coprime Möbius–harmonic inversion

The Möbius inversion of the polar unit survives restriction to a coprimality class: writing
`H_e(z) = ∑_{k ≤ z, (e,k)=1} 1/k`, one has

`∑_{d ≤ N, (e,d)=1} (μ(d)/d) H_e(⌊N/d⌋) = 1`.

The proof is the tree's divisor swap, using that coprimality to `e` is multiplicative,
`(e, d k) = 1 ↔ (e,d) = 1 ∧ (e,k) = 1`.  This is the coprime-class input that upgrades the bounded
logarithmic Möbius sum from the modulus `e = 1` to every modulus.
-/

open Finset ArithmeticFunction GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- The coprime harmonic sum. -/
noncomputable def coprimeHarmonic (e z : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 z).filter (fun k => Nat.Coprime e k), 1 / (k : ℝ)

/-- **The coprime Möbius–harmonic inversion.** -/
theorem sum_moebius_coprime_harmonic_eq_one {e N : ℕ} (hN : 1 ≤ N) :
    ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime e d),
        ((μ d : ℤ) : ℝ) / (d : ℝ) * coprimeHarmonic e (N / d) = 1 := by
  classical
  set G : ℕ → ℕ → ℝ := fun d k =>
    if Nat.Coprime e d ∧ Nat.Coprime e k then ((μ d : ℤ) : ℝ) / ((d : ℝ) * (k : ℝ)) else 0 with hG
  have hright : ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N / d), G d k
      = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime e d),
          ((μ d : ℤ) : ℝ) / (d : ℝ) * coprimeHarmonic e (N / d) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : Nat.Coprime e d
    · rw [if_pos hd, coprimeHarmonic, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : Nat.Coprime e k
      · have hpair : Nat.Coprime e d ∧ Nat.Coprime e k := ⟨hd, hk⟩
        rw [hG]
        simp only [if_pos hpair, if_pos hk]
        ring
      · have hnp : ¬ (Nat.Coprime e d ∧ Nat.Coprime e k) := fun h => hk h.2
        rw [hG]
        simp only [if_neg hnp, if_neg hk]
    · rw [if_neg hd]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hG]
      exact if_neg (fun h : Nat.Coprime e d ∧ Nat.Coprime e k => hd h.1)
  have hleft : ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ m.divisors, G d (m / d) = 1 := by
    have hinner : ∀ m ∈ Finset.Icc 1 N, ∑ d ∈ m.divisors, G d (m / d)
        = if Nat.Coprime e m then (1 / (m : ℝ)) * (if m = 1 then 1 else 0) else 0 := by
      intro m hm
      obtain ⟨hm1, -⟩ := Finset.mem_Icc.mp hm
      have hm0 : m ≠ 0 := by omega
      by_cases hcm : Nat.Coprime e m
      · rw [if_pos hcm, ← sum_divisors_moebius_real m, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hd
        have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
        have hqpos : 0 < m / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hdpos
        have hcd : Nat.Coprime e d := Nat.Coprime.coprime_dvd_right hdvd hcm
        have hcq : Nat.Coprime e (m / d) :=
          Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hdvd) hcm
        have hmul : (d : ℝ) * ((m / d : ℕ) : ℝ) = (m : ℝ) := by
          have : d * (m / d) = m := Nat.mul_div_cancel' hdvd
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) this
        have hpair : Nat.Coprime e d ∧ Nat.Coprime e (m / d) := ⟨hcd, hcq⟩
        rw [hG]
        simp only [if_pos hpair]
        rw [hmul]
        ring
      · rw [if_neg hcm]
        refine Finset.sum_eq_zero fun d hd => ?_
        have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hd
        rw [hG]
        refine if_neg ?_
        rintro ⟨hcd, hcq⟩
        exact hcm (by
          have hmul : d * (m / d) = m := Nat.mul_div_cancel' hdvd
          rw [← hmul]
          exact Nat.Coprime.mul_right hcd hcq)
    rw [Finset.sum_congr rfl hinner]
    rw [Finset.sum_eq_single 1]
    · norm_num
    · intro b hb hb1
      by_cases hcb : Nat.Coprime e b
      · rw [if_pos hcb, if_neg hb1]
        ring
      · rw [if_neg hcb]
    · intro h
      exact absurd (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩) h
  rw [← hright, ← sum_divisors_swap N G, hleft]

end RHTower.Sieve
