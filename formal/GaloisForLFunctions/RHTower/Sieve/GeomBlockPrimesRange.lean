import GaloisForLFunctions.RHTower.Sieve.TuranKubiliusRange
import GaloisForLFunctions.RHTower.Sieve.PrimeBlockTwistBound

/-!
# A ladder block of the designated range is the primes of an interval

The Route-T envelope bounds the twisted sum over *all* primes of an interval, so applying it to a
ladder step requires the step to be exactly that set.  It is, once the ladder starts at the bottom
of the designated range and the range's top is the ladder's top.
-/

namespace RHTower.Sieve

open Finset

theorem mem_primesRange {z₀ z p : ℕ} :
    p ∈ primesRange z₀ z ↔ (p.Prime ∧ z₀ < p ∧ p ≤ z) := by
  rw [primesRange, Finset.mem_sdiff, mem_primesLE, mem_primesLE]
  constructor
  · rintro ⟨⟨hpz, hp⟩, hnot⟩
    refine ⟨hp, ?_, hpz⟩
    by_contra hle
    exact hnot ⟨by omega, hp⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨⟨hhi, hp⟩, fun h => absurd h.1 (by omega)⟩

/-- **A ladder block of the designated range is the set of primes of an interval.** -/
theorem mem_geomBlock_primesRange {z₀ z : ℕ} {Q η : ℝ} (hη : 0 ≤ η) (hQ : Q = (z₀ : ℝ))
    {L j : ℕ} (hj : j + 1 ≤ L) (hz : z = ⌊Q * (1 + η) ^ L⌋₊) (p : ℕ) :
    p ∈ geomBlock (primesRange z₀ z) Q (1 + η) j
      ↔ (p.Prime ∧ ⌊Q * (1 + η) ^ j⌋₊ < p ∧ p ≤ ⌊Q * (1 + η) ^ (j + 1)⌋₊) := by
  classical
  have hQ0 : (0 : ℝ) ≤ Q := by rw [hQ]; exact Nat.cast_nonneg _
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hbase : ∀ m : ℕ, (0 : ℝ) ≤ Q * (1 + η) ^ m := fun m => by positivity
  have hmono : ∀ m n : ℕ, m ≤ n → Q * (1 + η) ^ m ≤ Q * (1 + η) ^ n := fun m n hmn =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 hmn) hQ0
  have hfloorlt : ∀ (m : ℕ) (q : ℕ), (⌊Q * (1 + η) ^ m⌋₊ < q ↔ Q * (1 + η) ^ m < (q : ℝ)) :=
    fun m q => Nat.floor_lt (hbase m)
  have hfloorle : ∀ (m : ℕ) (q : ℕ), (q ≤ ⌊Q * (1 + η) ^ m⌋₊ ↔ (q : ℝ) ≤ Q * (1 + η) ^ m) :=
    fun m q => Nat.le_floor_iff (hbase m)
  rw [geomBlock, Finset.mem_filter, mem_primesRange]
  constructor
  · rintro ⟨⟨hp, -, -⟩, hlo, hhi⟩
    exact ⟨hp, (hfloorlt j p).2 hlo, (hfloorle (j + 1) p).2 hhi⟩
  · rintro ⟨hp, hlo, hhi⟩
    have hloR : Q * (1 + η) ^ j < (p : ℝ) := (hfloorlt j p).1 hlo
    have hhiR : (p : ℝ) ≤ Q * (1 + η) ^ (j + 1) := (hfloorle (j + 1) p).1 hhi
    refine ⟨⟨hp, ?_, ?_⟩, hloR, hhiR⟩
    · have h0 : Q * (1 + η) ^ 0 ≤ Q * (1 + η) ^ j := hmono 0 j (Nat.zero_le j)
      have hz0 : ((z₀ : ℕ) : ℝ) < (p : ℝ) := by
        rw [← hQ]
        have : Q * (1 + η) ^ 0 = Q := by rw [pow_zero, mul_one]
        linarith [h0, hloR, this]
      exact_mod_cast hz0
    · rw [hz]
      exact (hfloorle L p).2 (le_trans hhiR (hmono (j + 1) L hj))

end RHTower.Sieve
