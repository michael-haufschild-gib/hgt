import GaloisForLFunctions.BezoutValuationIncidence.Sieve.PrimeProgressionFinite
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ProgressionTruncationScales

/-!
# A uniform upper bound for primes in a large prime modulus

Above the square of the modulus, a sixteenth-root Selberg truncation has
logarithmic mass and negligible polynomial error. The resulting constant
does not depend on the modulus, residue or horizon.
-/

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

open Finset Filter Topology

/-- Above the square of a sufficiently large prime modulus, every residue class
contains at most a fixed multiple of its prime-density share. -/
theorem exists_prime_progression_upper :
    ∃ p₀ : ℕ, 8 ≤ p₀ ∧ ∀ p X a : ℕ, p.Prime → p₀ ≤ p → p ^ 2 ≤ X →
      ((#{n ∈ Icc 1 X | n.Prime ∧ n ≡ a [MOD p]} : ℕ) : ℝ) ≤
        1026 * (X : ℝ) / ((p : ℝ) * Real.log X) := by
  obtain ⟨U, hU⟩ := eventually_atTop.mp eventually_progression_truncation
  refine ⟨8 + ⌈U⌉₊, by omega, ?_⟩
  intro p X a hp hp₀ hpX
  have hp8 : 8 ≤ p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hsq : (p : ℝ) ^ 2 ≤ X := by exact_mod_cast hpX
  have hX0 : (0 : ℝ) < X := (sq_pos_of_pos hp0).trans_le hsq
  let u : ℝ := (X : ℝ) / p
  have hpu : (p : ℝ) ≤ u := by
    apply (le_div_iff₀ hp0).mpr
    simpa only [pow_two] using hsq
  have hUp : U ≤ (p : ℝ) := (Nat.le_ceil U).trans (by exact_mod_cast (show ⌈U⌉₊ ≤ p by omega))
  obtain ⟨hu, hY, hYL, hlogY, herror⟩ := hU u (hUp.trans hpu)
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hLu : 0 < Real.log u := Real.log_pos hu
  have hLX : 0 < Real.log (X : ℝ) := by
    apply Real.log_pos
    have hpX' : (p : ℝ) ≤ X := (le_self_pow₀ hp2.le (by omega : (2 : ℕ) ≠ 0)).trans hsq
    exact hp2.trans_le hpX'
  have hlogX : Real.log (X : ℝ) ≤ 2 * Real.log u := by
    have hlogp := Real.log_le_log hp0 hpu
    have hlogu : Real.log u = Real.log (X : ℝ) - Real.log p :=
      Real.log_div hX0.ne' hp0.ne'
    linarith only [hlogp, hlogu]
  have hmain : 16 * u / Real.log (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) ≤
      512 * u / Real.log u := by
    refine (div_le_div_of_nonneg_left (by positivity)
      (div_pos hLu (by norm_num)) hlogY).trans_eq ?_
    ring
  have hcount := card_prime_progression_le_truncation
    (X := X) (a := a) hp hp8 hY hYL
  have hbound : ((#{n ∈ Icc 1 X | n.Prime ∧ n ≡ a [MOD p]} : ℕ) : ℝ) ≤
      513 * u / Real.log u := by
    change _ ≤ (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) +
      16 * u / Real.log (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) +
        (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) ^ 6 at hcount
    calc
      _ ≤ (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) +
          16 * u / Real.log (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) +
            (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) ^ 6 := hcount
      _ = ((⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) +
          (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) ^ 6) +
            16 * u / Real.log (⌊u ^ (1 / 16 : ℝ)⌋₊ : ℝ) := by ring
      _ ≤ u / Real.log u + 512 * u / Real.log u := add_le_add herror hmain
      _ = _ := by ring
  refine hbound.trans ?_
  have hratio : u / Real.log u ≤ 2 * u / Real.log (X : ℝ) := by
    rw [div_le_div_iff₀ hLu hLX]
    nlinarith only [mul_le_mul_of_nonneg_left hlogX hu0.le]
  have h := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 513)
  convert h using 1 <;> dsimp only [u] <;> ring

#print axioms exists_prime_progression_upper

end GaloisForLFunctions.BezoutValuationIncidence
