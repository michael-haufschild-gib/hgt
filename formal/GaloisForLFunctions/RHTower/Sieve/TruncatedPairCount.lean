import GaloisForLFunctions.RHTower.Sieve.JointCongruenceEmpty
import GaloisForLFunctions.RHTower.Sieve.MoebiusSignCount

/-!
# The truncated squarefree pair count for a squarefree shift

For squarefree `h` every contributing pair is coprime, so the weighted joint counts of
`sum_truncated_pair_eq` are all evaluated by `abs_card_joint_sub_lt`, each with error below one.
Summing over the at most `R²` pairs:

`|∑_{n ∈ (t,t+L]} Q_R(n) Q_R(n+h) - L ∑_{d,e ≤ R, (d,e)=1} μ(d)μ(e)/(d²e²)| ≤ R²`,

uniformly in the start `t` and the shift `h`.

This is the two-variable analogue of `abs_truncated_squarefree_sub_le`, and completes the elementary
sieve treatment of a shifted squarefree correlation.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **The truncated squarefree pair count.** -/
theorem abs_truncated_pair_sub_le {h : ℕ} (hh : Squarefree h) (t L R : ℕ) :
    |∑ n ∈ Finset.Ioc t (t + L),
        (∑ d ∈ {d ∈ Finset.Icc 1 R | d ^ (2 : ℕ) ∣ n}, ((moebius d : ℤ) : ℝ))
          * (∑ e ∈ {e ∈ Finset.Icc 1 R | e ^ (2 : ℕ) ∣ (n + h)}, ((moebius e : ℤ) : ℝ))
        - (L : ℝ) * ∑ p ∈ {p ∈ Finset.Icc 1 R ×ˢ Finset.Icc 1 R | Nat.Coprime p.1 p.2},
            ((moebius p.1 : ℤ) : ℝ) * ((moebius p.2 : ℤ) : ℝ)
              / ((p.1 : ℝ) ^ (2 : ℕ) * (p.2 : ℝ) ^ (2 : ℕ))|
      ≤ (R : ℝ) ^ (2 : ℕ) := by
  classical
  set S : Finset (ℕ × ℕ) := Finset.Icc 1 R ×ˢ Finset.Icc 1 R with hS
  set C : Finset (ℕ × ℕ) := {p ∈ S | Nat.Coprime p.1 p.2} with hC
  set N : ℕ × ℕ → ℝ := fun p =>
    ((#{n ∈ Finset.Ioc t (t + L) | p.1 ^ (2 : ℕ) ∣ n ∧ p.2 ^ (2 : ℕ) ∣ (n + h)} : ℕ) : ℝ) with hN
  set w : ℕ × ℕ → ℝ := fun p => ((moebius p.1 : ℤ) : ℝ) * ((moebius p.2 : ℤ) : ℝ) with hw
  have hswap : ∑ n ∈ Finset.Ioc t (t + L),
      (∑ d ∈ {d ∈ Finset.Icc 1 R | d ^ (2 : ℕ) ∣ n}, ((moebius d : ℤ) : ℝ))
        * (∑ e ∈ {e ∈ Finset.Icc 1 R | e ^ (2 : ℕ) ∣ (n + h)}, ((moebius e : ℤ) : ℝ))
      = ∑ p ∈ S, w p * N p := by
    rw [sum_truncated_pair_eq t L R h, hS, Finset.sum_product]
  have hzero : ∀ p ∈ S, p ∉ C → w p * N p = 0 := by
    intro p hp hpc
    have hnc : ¬ Nat.Coprime p.1 p.2 := by
      rw [hC, Finset.mem_filter] at hpc
      tauto
    have hgcd : ¬ ((Nat.gcd p.1 p.2) ^ (2 : ℕ) ∣ h) := by
      intro hdvd
      exact hnc (Nat.isUnit_iff.mp (hh (Nat.gcd p.1 p.2) (by simpa [pow_two] using hdvd)))
    rw [hN]
    simp only
    rw [card_joint_eq_zero hgcd t L]
    simp
  have hrestrict : ∑ p ∈ S, w p * N p = ∑ p ∈ C, w p * N p :=
    (Finset.sum_subset (by rw [hC]; exact Finset.filter_subset _ _) hzero).symm
  rw [hswap, hrestrict, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ C,
      |w p * N p - (L : ℝ) * (w p / ((p.1 : ℝ) ^ (2 : ℕ) * (p.2 : ℝ) ^ (2 : ℕ)))| ≤ 1 := by
    intro p hp
    rw [hC, Finset.mem_filter, hS, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hd1, _⟩, ⟨he1, _⟩⟩, hcop⟩ := hp
    have hd0 : 0 < p.1 := hd1
    have he0 : 0 < p.2 := he1
    have hcop2 : Nat.Coprime (p.1 ^ (2 : ℕ)) (p.2 ^ (2 : ℕ)) := Nat.Coprime.pow _ _ hcop
    have hpos : 0 < p.1 ^ (2 : ℕ) * p.2 ^ (2 : ℕ) := by positivity
    obtain ⟨n₀, h0a, h0b⟩ := exists_joint_solution (by positivity : 0 < p.2 ^ (2 : ℕ)) hcop2 h
    have hcount := abs_card_joint_sub_lt hcop2 hpos h0a h0b t L
    have hcast : ((p.1 ^ (2 : ℕ) : ℕ) : ℝ) * ((p.2 ^ (2 : ℕ) : ℕ) : ℝ) = (p.1 : ℝ) ^ (2 : ℕ) * (p.2 : ℝ) ^ (2 : ℕ) := by
      push_cast; ring
    rw [hcast] at hcount
    have hwabs : |w p| ≤ 1 := by
      rw [hw]
      simp only [abs_mul]
      have h1 : |((moebius p.1 : ℤ) : ℝ)| ≤ 1 := by
        rcases moebius_trichotomy p.1 with hm | hm | hm <;> rw [hm] <;> norm_num
      have h2 : |((moebius p.2 : ℤ) : ℝ)| ≤ 1 := by
        rcases moebius_trichotomy p.2 with hm | hm | hm <;> rw [hm] <;> norm_num
      exact mul_le_one₀ h1 (abs_nonneg _) h2
    have hrw : w p * N p - (L : ℝ) * (w p / ((p.1 : ℝ) ^ (2 : ℕ) * (p.2 : ℝ) ^ (2 : ℕ)))
        = w p * (N p - (L : ℝ) / ((p.1 : ℝ) ^ (2 : ℕ) * (p.2 : ℝ) ^ (2 : ℕ))) := by ring
    rw [hrw, abs_mul]
    exact mul_le_one₀ hwabs (abs_nonneg _) hcount.le
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (C.card : ℝ) ≤ (R : ℝ) ^ (2 : ℕ) := by
    have h1 : C.card ≤ S.card := Finset.card_le_card (by rw [hC]; exact Finset.filter_subset _ _)
    have h2 : S.card = R * R := by
      rw [hS, Finset.card_product, Nat.card_Icc]
      simp
    have : (C.card : ℝ) ≤ ((R * R : ℕ) : ℝ) := by exact_mod_cast h2 ▸ h1
    calc (C.card : ℝ) ≤ ((R * R : ℕ) : ℝ) := this
      _ = (R : ℝ) ^ (2 : ℕ) := by push_cast; ring
  exact hcard

end RHTower.Sieve
