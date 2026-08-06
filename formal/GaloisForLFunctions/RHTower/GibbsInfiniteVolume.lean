import Mathlib
import GaloisForLFunctions.RHTower.GibbsMoebiusAnchor

/-!
# The finite gas approximates the Möbius–Laplace transform

The genuine Möbius–Laplace transform `Φ(x) = ∑_n μ(n) e^{-n x}` differs from the gas over
the primes up to `y` only by terms indexed by squarefree integers with a prime factor above
`y`, and every such integer exceeds `y`.  Hence the explicit bridge

  `|Φ(x) − P_{S_y}(-1, x)| ≤ e^{-(y+1)x} / (1 − e^{-x})`,

valid for every `x > 0` and every cutoff `y`.  The finite theory therefore transfers to the
infinite-volume object with a controlled, exponentially small error.
-/

namespace RHTower.GibbsGas

open ArithmeticFunction

/-- The Möbius–Laplace transform. -/
noncomputable def moebiusLaplace (x : ℝ) : ℝ :=
  ∑' n : ℕ, ((moebius n : ℤ) : ℝ) * Real.exp (-(x * (n : ℝ)))

/-- The primes up to a cutoff. -/
noncomputable def primesUpTo (y : ℕ) : Finset ℕ :=
  (Finset.range (y + 1)).filter Nat.Prime

theorem primesUpTo_prime {y : ℕ} : ∀ p ∈ primesUpTo y, p.Prime := by
  intro p hp
  rw [primesUpTo, Finset.mem_filter] at hp
  exact hp.2

theorem mem_primesUpTo {y p : ℕ} (hp : p.Prime) (hple : p ≤ y) : p ∈ primesUpTo y := by
  rw [primesUpTo, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hp⟩

/-- Boltzmann weights are powers of `e^{-x}`. -/
theorem exp_neg_mul_nat (x : ℝ) (n : ℕ) :
    Real.exp (-(x * (n : ℝ))) = Real.exp (-x) ^ n := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- A squarefree integer below the cutoff divides the primorial of the cutoff. -/
theorem dvd_prod_primesUpTo {y n : ℕ} (hn : n ≠ 0) (hsq : Squarefree n) (hle : n ≤ y) :
    n ∣ ∏ p ∈ primesUpTo y, p := by
  have hsub : n.primeFactors ⊆ primesUpTo y := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    exact mem_primesUpTo hpp (le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpd) hle)
  have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsq
  calc n = ∏ p ∈ n.primeFactors, p := hprod.symm
    _ ∣ ∏ p ∈ primesUpTo y, p := Finset.prod_dvd_prod_of_subset _ _ _ hsub

set_option maxHeartbeats 1200000 in
/-- **The infinite-volume bridge.**  The gas over the primes up to `y` differs from the
Möbius–Laplace transform by at most the geometric tail beyond `y`. -/
theorem abs_moebiusLaplace_sub_gibbs_le (x : ℝ) (hx : 0 < x) (y : ℕ) :
    |moebiusLaplace x - gibbsDiag (primesUpTo y) x (-1)|
      ≤ Real.exp (-x) ^ (y + 1) / (1 - Real.exp (-x)) := by
  classical
  set r : ℝ := Real.exp (-x) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith
  set D : Finset ℕ := (∏ p ∈ primesUpTo y, p).divisors with hD
  set f : ℕ → ℝ := fun n => ((moebius n : ℤ) : ℝ) * r ^ n with hf
  -- the gas is the divisor sum
  have hgas : gibbsDiag (primesUpTo y) x (-1) = ∑ d ∈ D, f d := by
    rw [gibbs_parity_eq_moebius_divisors _ primesUpTo_prime x, hD]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hf, exp_neg_mul_nat]
  -- summability
  have hbound : ∀ n : ℕ, |f n| ≤ r ^ n := by
    intro n
    simp only [hf]
    rw [abs_mul, abs_pow, abs_of_pos hr0]
    have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
      by_cases hsq : Squarefree n
      · rw [moebius_apply_of_squarefree hsq]
        push_cast
        rw [abs_pow, abs_neg, abs_one, one_pow]
      · rw [moebius_eq_zero_of_not_squarefree hsq]
        norm_num
    have hpow : (0 : ℝ) ≤ r ^ n := by positivity
    nlinarith [hmu, hpow]
  have hgeo : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0.le hr1
  have hfsum : Summable f := by
    refine Summable.of_abs ?_
    exact Summable.of_nonneg_of_le (fun n => abs_nonneg _) hbound hgeo
  -- the transform in the `r` variable
  have hΦ : moebiusLaplace x = ∑' n : ℕ, f n := by
    rw [moebiusLaplace]
    refine tsum_congr fun n => ?_
    rw [hf, exp_neg_mul_nat]
  -- split off the divisor part
  set g : ℕ → ℝ := fun n => if n ∈ D then 0 else f n with hg
  have hsplit : ∀ n : ℕ, f n = (if n ∈ D then f n else 0) + g n := by
    intro n
    simp only [hg]
    by_cases h : n ∈ D <;> simp [h]
  have hsumD : ∑ b ∈ D, (if b ∈ D then f b else 0) = ∑ d ∈ D, f d :=
    Finset.sum_congr rfl (fun d hd => by simp [hd])
  have hhasD : HasSum (fun n : ℕ => if n ∈ D then f n else 0) (∑ d ∈ D, f d) := by
    rw [← hsumD]
    exact hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
  have hDsum : Summable (fun n : ℕ => if n ∈ D then f n else 0) := hhasD.summable
  have hDtsum : ∑' n : ℕ, (if n ∈ D then f n else 0) = ∑ d ∈ D, f d := hhasD.tsum_eq
  have hgsum : Summable g := by
    have hsub := hfsum.sub hDsum
    refine hsub.congr fun n => ?_
    simp only [hg]
    by_cases hn : n ∈ D <;> simp [hn]
  have hadd : ∑' n : ℕ, f n
      = (∑' n : ℕ, (if n ∈ D then f n else 0)) + ∑' n : ℕ, g n := by
    rw [← hDsum.tsum_add hgsum]
    exact tsum_congr hsplit
  have hdiff : moebiusLaplace x - gibbsDiag (primesUpTo y) x (-1) = ∑' n : ℕ, g n := by
    rw [hΦ, hgas, hadd, hDtsum]
    ring
  -- the tail bound
  set h : ℕ → ℝ := fun n => if n ≤ y then 0 else r ^ n with hh
  have hgle : ∀ n : ℕ, |g n| ≤ h n := by
    intro n
    simp only [hg, hh]
    by_cases hnD : n ∈ D
    · rw [if_pos hnD, abs_zero]
      by_cases hny : n ≤ y
      · rw [if_pos hny]
      · rw [if_neg hny]
        positivity
    · rw [if_neg hnD]
      by_cases hny : n ≤ y
      · rw [if_pos hny]
        -- below the cutoff the Möbius weight must vanish
        have hmu0 : ((moebius n : ℤ) : ℝ) = 0 := by
          by_contra hne
          have hne' : (moebius n : ℤ) ≠ 0 := by
            intro hz
            apply hne
            rw [hz]
            norm_num
          have hsq : Squarefree n := by
            by_contra hsqf
            exact hne' (moebius_eq_zero_of_not_squarefree hsqf)
          have hn0 : n ≠ 0 := by
            rintro rfl
            exact hne' (by simp)
          exact hnD (Nat.mem_divisors.mpr
            ⟨dvd_prod_primesUpTo hn0 hsq hny,
              (squarefree_prod_primes primesUpTo_prime).ne_zero⟩)
        simp only [hf]
        rw [hmu0, zero_mul, abs_zero]
      · rw [if_neg hny]
        exact hbound n
  have hhsum : Summable h := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeo
    · simp only [hh]
      by_cases hny : n ≤ y
      · rw [if_pos hny]
      · rw [if_neg hny]; positivity
    · simp only [hh]
      by_cases hny : n ≤ y
      · rw [if_pos hny]; positivity
      · rw [if_neg hny]
  have hle1 : ∀ n : ℕ, g n ≤ h n := fun n => le_trans (le_abs_self (g n)) (hgle n)
  have hle2 : ∀ n : ℕ, -(h n) ≤ g n := by
    intro n
    have := (abs_le.mp (hgle n)).1
    linarith
  have habs : |∑' n : ℕ, g n| ≤ ∑' n : ℕ, h n := by
    have hA : ∑' n : ℕ, g n ≤ ∑' n : ℕ, h n :=
      Summable.tsum_le_tsum hle1 hgsum hhsum
    have hB : ∑' n : ℕ, (-(h n)) ≤ ∑' n : ℕ, g n :=
      Summable.tsum_le_tsum hle2 hhsum.neg hgsum
    rw [tsum_neg] at hB
    rw [abs_le]
    exact ⟨by linarith, hA⟩
  -- evaluate the tail
  have htail : ∑' n : ℕ, h n = r ^ (y + 1) / (1 - r) := by
    have hzero : ∑ i ∈ Finset.range (y + 1), h i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp only [hh]
      rw [if_pos (by omega)]
    have hshift : ∀ i : ℕ, h (i + (y + 1)) = r ^ (y + 1) * r ^ i := by
      intro i
      simp only [hh]
      rw [if_neg (by omega), pow_add]
      ring
    have hsplit2 := hhsum.sum_add_tsum_nat_add (y + 1)
    rw [hzero, zero_add] at hsplit2
    rw [← hsplit2, tsum_congr hshift, tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1]
    ring
  rw [hdiff, ← htail]
  exact habs

end RHTower.GibbsGas
