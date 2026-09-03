import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareBlockSplit
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockAbel
import GaloisForLFunctions.RHTower.Sieve.GeomBlockPrimesRange

/-!
# Reciprocal Abel transfer for Menon's harmonic prime block

Prime cancellation estimates in the corpus control the ordinary prime polynomial.  Menon's
polynomial lies on `Re s = 1`, so its prime factor has one additional coefficient `1/p`.  Abel
summation transfers a uniform prefix bound with exactly the reciprocal left-endpoint loss.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- A set characterized as all primes in `(a,b]` is the corpus prime range. -/
theorem eq_primesRange_of_mem_iff {B : Finset ℕ} {a b : ℕ}
    (hB : ∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b)) :
    B = primesRange a b := by
  ext p
  rw [hB p, mem_primesRange]

/-- The prime-filtered integer prefix `[a+1,m)` is exactly `primesRange a (m-1)`. -/
theorem filter_prime_Ico_eq_primesRange {a m : ℕ} (ham : a + 1 ≤ m) :
    (Finset.Ico (a + 1) m).filter Nat.Prime = primesRange a (m - 1) := by
  ext p
  rw [Finset.mem_filter, Finset.mem_Ico, mem_primesRange]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp⟩
    exact ⟨hp, by omega, by omega⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨⟨by omega, by omega⟩, hp⟩

/-- The harmonic prime block is the ordinary prime phase weighted by `1/p`. -/
theorem harmonicPrimeBlockPoly_eq_weighted_sum {B : Finset ℕ} (w : ℝ) :
    harmonicPrimeBlockPoly B w =
      ∑ p ∈ B, (((1 / (p : ℝ) : ℝ) : ℂ)) * moebiusPhase w p := by
  rw [harmonicPrimeBlockPoly]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [harmonicMoebiusPhase]
  have hcast : ((((1 : ℝ) / (p : ℝ) : ℝ)) : ℂ) = 1 / (p : ℂ) := by
    apply Complex.ext <;> simp
  rw [hcast]
  ring

/-- Reciprocal Abel transfer for a full prime interval.  Uniform ordinary-prime prefix bound `E`
on `(a,m-1]` gives the harmonic bound `E/(a+1)` on `(a,b]`. -/
theorem norm_harmonicPrimeBlockPoly_le_of_prefix {B : Finset ℕ} {a b : ℕ}
    (hab : a ≤ b) (hB : ∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b))
    (w : ℝ) {E : ℝ}
    (hE : ∀ m : ℕ, a + 1 ≤ m → m ≤ b + 1 →
      ‖primeBlockPoly (primesRange a (m - 1)) w‖ ≤ E) :
    ‖harmonicPrimeBlockPoly B w‖ ≤ E / ((a + 1 : ℕ) : ℝ) := by
  let c : ℕ → ℂ := fun n => if n.Prime then moebiusPhase w n else 0
  have hprefix : ∀ m : ℕ, a + 1 ≤ m → m ≤ b + 1 →
      ‖∑ n ∈ Finset.Ico (a + 1) m, c n‖ ≤ E := by
    intro m ham hmb
    have hfilter : ∑ n ∈ Finset.Ico (a + 1) m, c n =
        ∑ n ∈ (Finset.Ico (a + 1) m).filter Nat.Prime, moebiusPhase w n := by
      rw [Finset.sum_filter]
    rw [hfilter, filter_prime_Ico_eq_primesRange ham]
    simpa [primeBlockPoly] using hE m ham hmb
  have hanti : ∀ m : ℕ, a + 1 ≤ m → m < b + 1 →
      (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 / (m : ℝ) := by
    intro m hm _
    have hm0 : (0 : ℝ) < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < a + 1) hm)
    exact one_div_le_one_div_of_le hm0 (by push_cast; linarith)
  have htop0 : (0 : ℝ) ≤ (1 : ℝ) / ((b + 1 : ℕ) : ℝ) := by positivity
  have hab' : a + 1 ≤ b + 1 := by omega
  have habel := abel_block_bound c (fun n => (1 : ℝ) / (n : ℝ))
    (a + 1) (b + 1) hab' htop0 hanti E hprefix
  have hset : B = primesRange a b := eq_primesRange_of_mem_iff hB
  have hrewrite :
      (∑ n ∈ Finset.Ico (a + 1) (b + 1),
        ((((1 : ℝ) / (n : ℝ) : ℝ)) : ℂ) * c n) =
      ∑ p ∈ B, ((((1 : ℝ) / (p : ℝ) : ℝ)) : ℂ) * moebiusPhase w p := by
    have hfilter :
        (∑ n ∈ Finset.Ico (a + 1) (b + 1),
          ((((1 : ℝ) / (n : ℝ) : ℝ)) : ℂ) * c n) =
        ∑ n ∈ (Finset.Ico (a + 1) (b + 1)).filter Nat.Prime,
          ((((1 : ℝ) / (n : ℝ) : ℝ)) : ℂ) * moebiusPhase w n := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun n _ => by simp [c]
    rw [hfilter, filter_prime_Ico_eq_primesRange hab', show b + 1 - 1 = b by omega, ← hset]
  rw [harmonicPrimeBlockPoly_eq_weighted_sum, ← hrewrite]
  simpa [div_eq_mul_inv] using habel

end

end RHTower.Sieve
