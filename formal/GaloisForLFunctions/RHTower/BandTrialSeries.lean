import GaloisForLFunctions.RHTower.BandTrialMoments
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The Kaiser–Bessel trial series collapses to an odd-factorial series

The double series of the band trial function, indexed by the weight exponent `k` and the frequency
exponent `j`, collapses along its antidiagonals: with `m = j + k`,

```text
sum_(j,k) 2 binom(j+k, j) (c²)^k (-omega²)^j/(2(j+k)+1)! = sum_m 2 (c² - omega²)^m/(2m+1)!,
```

which is `2 sinh(sqrt(c² - omega²))/sqrt(c² - omega²)` inside the band and
`2 sin(sqrt(omega² - c²))/sqrt(omega² - c²)` outside it.

The regrouping is the antidiagonal reindexing of a summable family on `ℕ × ℕ`, stated here for an
arbitrary summable family (mathlib has it only inside the Cauchy product formula).  Summability comes
from the same binomial collapse applied to the absolute values, where the alternating sign is replaced
by `+`: the antidiagonal sums are then `2 (c² + omega²)^m/(2m+1)!`, dominated by the exponential
series because `m! <= (2m+1)!`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Finset

/-- **The antidiagonal binomial collapse.** -/
theorem antidiagonal_binomial_sum (a b : ℝ) (m : ℕ) :
    ∑ p ∈ Finset.antidiagonal m,
        2 * (Nat.choose m p.1 : ℝ) * b ^ p.2 * a ^ p.1 / (Nat.factorial (2 * m + 1) : ℝ)
      = 2 * (a + b) ^ m / (Nat.factorial (2 * m + 1) : ℝ) := by
  have hbinom : (a + b) ^ m
      = ∑ i ∈ Finset.range (m + 1), a ^ i * b ^ (m - i) * (Nat.choose m i : ℝ) := add_pow a b m
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hbinom, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The odd-factorial series is absolutely summable. -/
theorem summable_oddFactorial_pow (z : ℝ) :
    Summable fun m : ℕ => 2 * z ^ m / (Nat.factorial (2 * m + 1) : ℝ) := by
  have hbase : Summable fun m : ℕ => 2 * (|z| ^ m / (Nat.factorial m : ℝ)) :=
    (Real.summable_pow_div_factorial |z|).mul_left 2
  refine Summable.of_norm_bounded hbase fun m => ?_
  have hmle : Nat.factorial m ≤ Nat.factorial (2 * m + 1) := Nat.factorial_le (by omega)
  have hmposR : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hoddposR : (0 : ℝ) < (Nat.factorial (2 * m + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hmleR : (Nat.factorial m : ℝ) ≤ (Nat.factorial (2 * m + 1) : ℝ) := by
    exact_mod_cast hmle
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hoddposR, abs_pow, h2, mul_div_assoc]
  gcongr

/-- **Antidiagonal reindexing of a summable family on `ℕ × ℕ`.** -/
theorem tsum_eq_tsum_sum_antidiagonal {T : ℕ × ℕ → ℝ} (hT : Summable T) :
    (∑' p : ℕ × ℕ, T p) = ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, T p := by
  have hsig : Summable fun x : Σ m : ℕ, Finset.antidiagonal m => T (x.2 : ℕ × ℕ) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hT
  have hfib : ∀ m : ℕ, Summable fun p : Finset.antidiagonal m => T (p : ℕ × ℕ) := fun m =>
    (hasSum_fintype _).summable
  have hsigma := hsig.tsum_sigma' hfib
  have hprod : (∑' p : ℕ × ℕ, T p)
      = ∑' x : Σ m : ℕ, Finset.antidiagonal m, T (x.2 : ℕ × ℕ) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq T).symm
  calc (∑' p : ℕ × ℕ, T p)
      = ∑' x : Σ m : ℕ, Finset.antidiagonal m, T (x.2 : ℕ × ℕ) := hprod
    _ = ∑' m : ℕ, ∑' p : Finset.antidiagonal m, T (p : ℕ × ℕ) := hsigma
    _ = ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, T p := by
        refine tsum_congr fun m => ?_
        rw [tsum_fintype, Finset.sum_coe_sort]

/-- The `(j, k)` term of the trial series. -/
def trialTerm (c ω : ℝ) (p : ℕ × ℕ) : ℝ :=
  2 * (Nat.choose (p.1 + p.2) p.1 : ℝ) * (c ^ (2 : ℕ)) ^ p.2 * (-(ω ^ (2 : ℕ))) ^ p.1
    / (Nat.factorial (2 * (p.1 + p.2) + 1) : ℝ)

/-- The absolute value of the trial term is the same expression with `+omega²`. -/
theorem abs_trialTerm (c ω : ℝ) (p : ℕ × ℕ) :
    |trialTerm c ω p|
      = 2 * (Nat.choose (p.1 + p.2) p.1 : ℝ) * (c ^ (2 : ℕ)) ^ p.2 * (ω ^ (2 : ℕ)) ^ p.1
        / (Nat.factorial (2 * (p.1 + p.2) + 1) : ℝ) := by
  have hoddposR : (0 : ℝ) < (Nat.factorial (2 * (p.1 + p.2) + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  rw [trialTerm, abs_div, abs_of_pos hoddposR]
  congr 1
  rw [abs_mul, abs_mul, abs_mul]
  have h1 : |(2 : ℝ)| = 2 := by norm_num
  have h2 : |(Nat.choose (p.1 + p.2) p.1 : ℝ)| = (Nat.choose (p.1 + p.2) p.1 : ℝ) := by
    rw [abs_of_nonneg]
    positivity
  have h3 : |((c ^ (2 : ℕ)) ^ p.2 : ℝ)| = (c ^ (2 : ℕ)) ^ p.2 := by
    rw [abs_of_nonneg]
    positivity
  have h4 : |((-(ω ^ (2 : ℕ))) ^ p.1 : ℝ)| = (ω ^ (2 : ℕ)) ^ p.1 := by
    rw [abs_pow, abs_neg, abs_of_nonneg (sq_nonneg ω)]
  rw [h1, h2, h3, h4]

/-- **The trial family is summable on `ℕ × ℕ`.** -/
theorem summable_trialTerm (c ω : ℝ) : Summable (trialTerm c ω) := by
  have hnonneg : ∀ x : Σ m : ℕ, Finset.antidiagonal m, 0 ≤ |trialTerm c ω (x.2 : ℕ × ℕ)| :=
    fun _ => abs_nonneg _
  have hfibsum : ∀ m : ℕ, Summable fun p : Finset.antidiagonal m => |trialTerm c ω (p : ℕ × ℕ)| :=
    fun m => (hasSum_fintype _).summable
  -- the antidiagonal sums of the absolute values
  have hantisum : ∀ m : ℕ, (∑' p : Finset.antidiagonal m, |trialTerm c ω (p : ℕ × ℕ)|)
      = 2 * (ω ^ (2 : ℕ) + c ^ (2 : ℕ)) ^ m / (Nat.factorial (2 * m + 1) : ℝ) := by
    intro m
    rw [tsum_fintype,
      Finset.sum_coe_sort (Finset.antidiagonal m) (fun p : ℕ × ℕ => |trialTerm c ω p|),
      ← antidiagonal_binomial_sum (ω ^ (2 : ℕ)) (c ^ (2 : ℕ)) m]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hmem : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
    rw [abs_trialTerm, hmem]
  have hsigsum : Summable fun x : Σ m : ℕ, Finset.antidiagonal m =>
      |trialTerm c ω (x.2 : ℕ × ℕ)| := by
    rw [summable_sigma_of_nonneg hnonneg]
    refine ⟨hfibsum, ?_⟩
    refine (summable_oddFactorial_pow (ω ^ (2 : ℕ) + c ^ (2 : ℕ))).congr fun m => ?_
    exact (hantisum m).symm
  have habs : Summable fun p : ℕ × ℕ => |trialTerm c ω p| :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mp hsigsum
  exact habs.of_abs

/-- **The trial series collapses to the odd-factorial series.** -/
theorem tsum_trialTerm_eq (c ω : ℝ) :
    (∑' p : ℕ × ℕ, trialTerm c ω p)
      = ∑' m : ℕ, 2 * (c ^ (2 : ℕ) - ω ^ (2 : ℕ)) ^ m / (Nat.factorial (2 * m + 1) : ℝ) := by
  rw [tsum_eq_tsum_sum_antidiagonal (summable_trialTerm c ω)]
  refine tsum_congr fun m => ?_
  have hsum : (∑ p ∈ Finset.antidiagonal m, trialTerm c ω p)
      = ∑ p ∈ Finset.antidiagonal m,
        2 * (Nat.choose m p.1 : ℝ) * (c ^ (2 : ℕ)) ^ p.2 * (-(ω ^ (2 : ℕ))) ^ p.1
          / (Nat.factorial (2 * m + 1) : ℝ) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hmem : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
    rw [trialTerm, hmem]
  rw [hsum, antidiagonal_binomial_sum (-(ω ^ (2 : ℕ))) (c ^ (2 : ℕ)) m]
  congr 2
  ring

end GaloisForLFunctions.RHTower

end
