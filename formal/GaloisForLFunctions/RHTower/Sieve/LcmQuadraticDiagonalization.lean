import GaloisForLFunctions.RHTower.Sieve.DivisorSumMeanSquareSmooth

/-!
# Diagonalising the lcm quadratic form

`1/[m₁,m₂] = gcd(m₁,m₂)/(m₁ m₂)` and `gcd = ∑_{e ∣ m₁, e ∣ m₂} φ(e)` turn the lcm quadratic form
into a sum of squares weighted by Euler's totient.  This is the Selberg-sieve diagonalisation, and
it is step three of Graham's theorem: it exhibits the form as positive semidefinite and reduces its
evaluation to the one-dimensional sums `∑_{m ≤ X, e ∣ m} μ(m) log(X/m)/m`.
-/

open Finset

namespace RHTower.Sieve

theorem div_lcm_eq_sum_totient (a : ℕ → ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    a m * a n / (Nat.lcm m n : ℝ)
      = ∑ e ∈ (Nat.gcd m n).divisors, (Nat.totient e : ℝ) * ((a m / m) * (a n / n)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hgcd : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left _ hm
  have hlcm : 0 < Nat.lcm m n := Nat.pos_of_ne_zero (by
    intro h
    rcases Nat.lcm_eq_zero_iff.mp h with h1 | h1 <;> omega)
  have hlcmR : (0 : ℝ) < (Nat.lcm m n : ℝ) := by exact_mod_cast hlcm
  have htot : (∑ e ∈ (Nat.gcd m n).divisors, (Nat.totient e : ℝ)) = (Nat.gcd m n : ℝ) := by
    have h := Nat.sum_totient (Nat.gcd m n)
    exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
  rw [← Finset.sum_mul, htot]
  have hprod : (Nat.gcd m n : ℝ) * (Nat.lcm m n : ℝ) = (m : ℝ) * (n : ℝ) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) (Nat.gcd_mul_lcm m n)
  have hgcdR : (0 : ℝ) < (Nat.gcd m n : ℝ) := by exact_mod_cast hgcd
  have h1 : (Nat.gcd m n : ℝ) ≠ 0 := ne_of_gt hgcdR
  have h2 : (Nat.lcm m n : ℝ) ≠ 0 := ne_of_gt hlcmR
  have hinv : (Nat.gcd m n : ℝ) / ((m : ℝ) * (n : ℝ)) = 1 / (Nat.lcm m n : ℝ) := by
    rw [← hprod]
    field_simp
  calc a m * a n / (Nat.lcm m n : ℝ)
      = a m * a n * (1 / (Nat.lcm m n : ℝ)) := by ring
    _ = a m * a n * ((Nat.gcd m n : ℝ) / ((m : ℝ) * (n : ℝ))) := by rw [hinv]
    _ = (Nat.gcd m n : ℝ) * ((a m / m) * (a n / n)) := by ring

/-- **The Selberg diagonalisation of the lcm quadratic form.** -/
theorem sum_div_lcm_eq_totient_diagonal (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (a : ℕ → ℝ) :
    ∑ p ∈ S ×ˢ S, a p.1 * a p.2 / (Nat.lcm p.1 p.2 : ℝ)
      = ∑ e ∈ S.biUnion Nat.divisors, (Nat.totient e : ℝ) *
          (∑ m ∈ S.filter (fun m => e ∣ m), a m / (m : ℝ)) ^ (2 : ℕ) := by
  classical
  have hexp : ∀ p ∈ S ×ˢ S, a p.1 * a p.2 / (Nat.lcm p.1 p.2 : ℝ)
      = ∑ e ∈ (Nat.gcd p.1 p.2).divisors,
          (Nat.totient e : ℝ) * ((a p.1 / p.1) * (a p.2 / p.2)) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact div_lcm_eq_sum_totient a (hS _ hp1) (hS _ hp2)
  rw [Finset.sum_congr rfl hexp]
  have hmem : ∀ (p : ℕ × ℕ) (e : ℕ),
      p ∈ S ×ˢ S ∧ e ∈ (Nat.gcd p.1 p.2).divisors
        ↔ p ∈ (S ×ˢ S).filter (fun q => e ∣ q.1 ∧ e ∣ q.2) ∧ e ∈ S.biUnion Nat.divisors := by
    intro p e
    constructor
    · rintro ⟨hp, he⟩
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have hgcd : e ∣ Nat.gcd p.1 p.2 := Nat.dvd_of_mem_divisors he
      have hd1 : e ∣ p.1 := dvd_trans hgcd (Nat.gcd_dvd_left _ _)
      have hd2 : e ∣ p.2 := dvd_trans hgcd (Nat.gcd_dvd_right _ _)
      refine ⟨Finset.mem_filter.mpr ⟨hp, hd1, hd2⟩, Finset.mem_biUnion.mpr ⟨p.1, hp1, ?_⟩⟩
      exact Nat.mem_divisors.mpr ⟨hd1, (hS _ hp1).ne'⟩
    · rintro ⟨hpf, -⟩
      obtain ⟨hp, hd1, hd2⟩ := Finset.mem_filter.mp hpf
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      refine ⟨hp, Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hd1 hd2, ?_⟩⟩
      exact (Nat.gcd_pos_of_pos_left _ (hS _ hp1)).ne'
  rw [Finset.sum_comm' hmem]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hfilter : (S ×ˢ S).filter (fun q => e ∣ q.1 ∧ e ∣ q.2)
      = (S.filter (fun m => e ∣ m)) ×ˢ (S.filter (fun m => e ∣ m)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hfilter, ← Finset.mul_sum, sq, Finset.sum_mul_sum, Finset.sum_product]

end RHTower.Sieve
