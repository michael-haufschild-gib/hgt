import GaloisForLFunctions.RHTower.Sieve.ImageLowerBound

/-!
# A gcd sum as a totient-weighted square

Using `∑_{g ∣ n} φ(g) = n` at `n = gcd(d₁,d₂)`, the gcd of a pair is the totient sum over the common
divisors, so exchanging the order of summation turns a pair sum of gcds into a single sum of squares:

`∑_{d₁,d₂ ∈ S} gcd(d₁,d₂) = ∑_{g ≤ M} φ(g) · (#{d ∈ S : g ∣ d})²`.

This is the identity behind the evaluation of `∑ 1/lcm` — since `1/lcm(d₁,d₂) = gcd(d₁,d₂)/(d₁d₂)`,
the second moment of the balanced divisor count is governed by exactly this sum.
-/

namespace RHTower.Sieve

open Finset

/-- The common divisors of a pair, as a filtered interval. -/
theorem divisors_gcd_eq_filter {M a b : ℕ} (ha : 0 < a) (haM : a ≤ M) :
    (Nat.gcd a b).divisors = (Finset.Icc 1 M).filter (fun g => g ∣ a ∧ g ∣ b) := by
  classical
  have hgpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  ext g
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨hga, hgb⟩, -⟩
    have hg1 : 1 ≤ g := Nat.pos_of_dvd_of_pos hga ha
    exact ⟨⟨hg1, le_trans (Nat.le_of_dvd ha hga) haM⟩, hga, hgb⟩
  · rintro ⟨-, hga, hgb⟩
    exact ⟨⟨hga, hgb⟩, hgpos.ne'⟩

/-- **The gcd pair sum is a totient-weighted sum of squares.** -/
theorem sum_gcd_eq_sum_totient_mul_sq {S : Finset ℕ} {M : ℕ}
    (hpos : ∀ d ∈ S, 0 < d) (hM : ∀ d ∈ S, d ≤ M) :
    ∑ p ∈ S ×ˢ S, ((Nat.gcd p.1 p.2 : ℕ) : ℝ)
      = ∑ g ∈ Finset.Icc 1 M,
          ((Nat.totient g : ℕ) : ℝ) * (((S.filter (fun d => g ∣ d)).card : ℕ) : ℝ) ^ (2 : ℕ) := by
  classical
  have hpair : ∀ p ∈ S ×ˢ S, ((Nat.gcd p.1 p.2 : ℕ) : ℝ)
      = ∑ g ∈ Finset.Icc 1 M,
          (if g ∣ p.1 ∧ g ∣ p.2 then ((Nat.totient g : ℕ) : ℝ) else 0) := by
    intro p hp
    rw [Finset.mem_product] at hp
    have hgcd : ∑ g ∈ (Nat.gcd p.1 p.2).divisors, Nat.totient g = Nat.gcd p.1 p.2 :=
      Nat.sum_totient _
    rw [← Finset.sum_filter, ← divisors_gcd_eq_filter (hpos p.1 hp.1) (hM p.1 hp.1)]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hgcd.symm
  rw [Finset.sum_congr rfl hpair, Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hcount : ∑ p ∈ S ×ˢ S, (if g ∣ p.1 ∧ g ∣ p.2 then ((Nat.totient g : ℕ) : ℝ) else 0)
      = ((Nat.totient g : ℕ) : ℝ) * (((S.filter (fun d => g ∣ d)).card : ℕ) : ℝ) ^ (2 : ℕ) := by
    rw [Finset.sum_product]
    have hinner : ∀ d₁ ∈ S,
        ∑ d₂ ∈ S, (if g ∣ d₁ ∧ g ∣ d₂ then ((Nat.totient g : ℕ) : ℝ) else 0)
          = (if g ∣ d₁ then ((Nat.totient g : ℕ) : ℝ) else 0)
            * (((S.filter (fun d => g ∣ d)).card : ℕ) : ℝ) := by
      intro d₁ _
      by_cases h1 : g ∣ d₁
      · rw [if_pos h1]
        have : ∀ d₂ ∈ S, (if g ∣ d₁ ∧ g ∣ d₂ then ((Nat.totient g : ℕ) : ℝ) else 0)
            = (if g ∣ d₂ then ((Nat.totient g : ℕ) : ℝ) else 0) := by
          intro d₂ _
          by_cases h2 : g ∣ d₂
          · rw [if_pos ⟨h1, h2⟩, if_pos h2]
          · rw [if_neg (fun hc => h2 hc.2), if_neg h2]
        rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          mul_comm]
      · rw [if_neg h1, zero_mul]
        refine Finset.sum_eq_zero fun d₂ _ => ?_
        rw [if_neg (fun hc => h1 hc.1)]
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul]
    ring
  exact hcount

/-- On a window the reciprocal lcm is dominated by the gcd over `y²`. -/
theorem inv_lcm_le_gcd_div {y a b : ℕ} (hy : 1 ≤ y) (ha : y ≤ a) (hb : y ≤ b) :
    1 / ((Nat.lcm a b : ℕ) : ℝ) ≤ ((Nat.gcd a b : ℕ) : ℝ) / (y : ℝ) ^ (2 : ℕ) := by
  have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have haR : (y : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (y : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hmul : ((Nat.gcd a b : ℕ) : ℝ) * ((Nat.lcm a b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Nat.gcd_mul_lcm a b)
  have hlcm0 : (0 : ℝ) < ((Nat.lcm a b : ℕ) : ℝ) := by
    have : 0 < Nat.lcm a b := Nat.pos_of_ne_zero (Nat.lcm_ne_zero ha0.ne' hb0.ne')
    exact_mod_cast this
  have hgcd0 : (0 : ℝ) < ((Nat.gcd a b : ℕ) : ℝ) := by
    have : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha0
    exact_mod_cast this
  have hab : (y : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) * (b : ℝ) := by nlinarith
  have h1 : 1 / ((Nat.lcm a b : ℕ) : ℝ) = ((Nat.gcd a b : ℕ) : ℝ) / ((a : ℝ) * (b : ℝ)) := by
    rw [← hmul]
    field_simp
  rw [h1]
  exact div_le_div_of_nonneg_left (le_of_lt hgcd0) (by positivity) hab

/-- **The reciprocal lcm sum is controlled by the gcd sum.** -/
theorem sum_inv_lcm_le_gcd_sum {y : ℕ} (hy : 1 ≤ y) :
    ∑ p ∈ (Finset.Icc y (2 * y)) ×ˢ (Finset.Icc y (2 * y)), 1 / ((Nat.lcm p.1 p.2 : ℕ) : ℝ)
      ≤ (1 / (y : ℝ) ^ (2 : ℕ))
        * ∑ p ∈ (Finset.Icc y (2 * y)) ×ˢ (Finset.Icc y (2 * y)),
            ((Nat.gcd p.1 p.2 : ℕ) : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
  have h := inv_lcm_le_gcd_div hy hp.1.1 hp.2.1
  calc 1 / ((Nat.lcm p.1 p.2 : ℕ) : ℝ)
      ≤ ((Nat.gcd p.1 p.2 : ℕ) : ℝ) / (y : ℝ) ^ (2 : ℕ) := h
    _ = 1 / (y : ℝ) ^ (2 : ℕ) * ((Nat.gcd p.1 p.2 : ℕ) : ℝ) := by ring

end RHTower.Sieve
