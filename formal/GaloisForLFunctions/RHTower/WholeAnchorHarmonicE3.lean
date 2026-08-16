import GaloisForLFunctions.RHTower.ReservoirElementarySymmetric
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The whole-anchor harmonic relation

Replacing a whole central squarefree anchor by one reservoir times one structured three-prime
token needs four exact facts beyond the reservoir elementary symmetric law.

The first is Stirling's upper bound `n! ≤ e√n (n/e)^n`, which turns the factorial normalization of
the harmonic weight into an exponentially large lower bound as soon as the pool mass is at least
half the reservoir breadth.

The second is exact reservoir decoding: the structured token's small factor lies below the pool
floor and its two balanced factors above the pool ceiling, so the reservoir is recovered from the
terminal as its prime factors inside the pool band — no allocation ambiguity survives.

The third is the first-difference Gibbs cost `|e^{-xq} - e^{-xn}| ≤ x(q-n)`.

The fourth, the column bound, is the single-class case of the stretched column bound of the
reciprocal allocation kernel.
-/

open Finset

namespace RHTower

/-! ## Stirling's upper bound -/

/-- **Stirling's upper bound.**  `n! ≤ e·√n·(n/e)^n` for `n ≥ 1`. -/
theorem factorial_le_stirling {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hanti : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 := by
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le k)
    simpa using this
  rw [Stirling.stirlingSeq_one] at hanti
  have hden : (0 : ℝ) < Real.sqrt (2 * ((k : ℝ) + 1)) * (((k : ℝ) + 1) / Real.exp 1) ^ (k + 1) := by
    have h1 : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
    have h2 : (0 : ℝ) < ((k : ℝ) + 1) / Real.exp 1 := by positivity
    exact mul_pos (Real.sqrt_pos.2 h1) (pow_pos h2 _)
  have hseq : Stirling.stirlingSeq (k + 1)
      = ((k + 1).factorial : ℝ)
        / (Real.sqrt (2 * ((k : ℝ) + 1)) * (((k : ℝ) + 1) / Real.exp 1) ^ (k + 1)) := by
    rw [Stirling.stirlingSeq]
    push_cast
    ring_nf
  rw [hseq, div_le_iff₀ hden] at hanti
  have hsqrt2 : Real.sqrt (2 * ((k : ℝ) + 1)) = Real.sqrt 2 * Real.sqrt ((k : ℝ) + 1) :=
    Real.sqrt_mul (by norm_num) _
  have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hfin : Real.exp 1 / Real.sqrt 2
      * (Real.sqrt (2 * ((k : ℝ) + 1)) * (((k : ℝ) + 1) / Real.exp 1) ^ (k + 1))
      = Real.exp 1 * Real.sqrt ((k : ℝ) + 1) * (((k : ℝ) + 1) / Real.exp 1) ^ (k + 1) := by
    rw [hsqrt2]
    field_simp
  rw [hfin] at hanti
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  exact hanti

/-- **(17)-(18) The factorial-normalized power is exponentially large.**  When the pool mass is at
least half the reservoir breadth, `S^b/b!` exceeds `(e/2)^b/(e√b)`. -/
theorem pow_div_factorial_ge {S : ℝ} {b : ℕ} (hb : 1 ≤ b) (hS : (b : ℝ) / 2 ≤ S) :
    (Real.exp 1 / 2) ^ b / (Real.exp 1 * Real.sqrt b) ≤ S ^ b / (b.factorial : ℝ) := by
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hSpos : 0 < S := by linarith
  have hstir := factorial_le_stirling hb
  have hfacpos : (0 : ℝ) < (b.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos b
  have hrhs : (0 : ℝ) < Real.exp 1 * Real.sqrt b := by positivity
  have hbe : (0 : ℝ) < ((b : ℝ) / Real.exp 1) ^ b := by positivity
  have hstep : S ^ b / (Real.exp 1 * Real.sqrt b * ((b : ℝ) / Real.exp 1) ^ b)
      ≤ S ^ b / (b.factorial : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hfacpos hstir
  refine le_trans ?_ hstep
  rw [div_le_div_iff₀ hrhs (by positivity)]
  have hbase : Real.exp 1 / 2 * ((b : ℝ) / Real.exp 1) ≤ S := by
    have hexp : Real.exp 1 / 2 * ((b : ℝ) / Real.exp 1) = (b : ℝ) / 2 := by
      have hne : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
      field_simp
    rw [hexp]
    exact hS
  have hpow : (Real.exp 1 / 2) ^ b * ((b : ℝ) / Real.exp 1) ^ b ≤ S ^ b := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase b
  calc (Real.exp 1 / 2) ^ b * (Real.exp 1 * Real.sqrt b * ((b : ℝ) / Real.exp 1) ^ b)
      = ((Real.exp 1 / 2) ^ b * ((b : ℝ) / Real.exp 1) ^ b) * (Real.exp 1 * Real.sqrt b) := by
        ring
    _ ≤ S ^ b * (Real.exp 1 * Real.sqrt b) :=
        mul_le_mul_of_nonneg_right hpow (le_of_lt hrhs)

/-! ## Exact reservoir decoding -/

open scoped Classical in
/-- **(13) The reservoir is decoded from the terminal.**  When the reservoir primes lie in the pool
band and the structured token's primes lie outside it, the pool-band prime factors of the terminal
are exactly the reservoir. -/
theorem reservoir_decode {W Z : ℝ} {t m : ℕ} (ht : t ≠ 0) (hm : m ≠ 0)
    (htR : ∀ p ∈ t.primeFactors, W < (p : ℝ) ∧ (p : ℝ) ≤ Z)
    (hmR : ∀ p ∈ m.primeFactors, ¬(W < (p : ℝ) ∧ (p : ℝ) ≤ Z)) :
    (t * m).primeFactors.filter (fun p : ℕ => W < (p : ℝ) ∧ (p : ℝ) ≤ Z) = t.primeFactors := by
  ext p
  simp only [Finset.mem_filter, Nat.primeFactors_mul ht hm, Finset.mem_union]
  constructor
  · rintro ⟨hp | hp, hband⟩
    · exact hp
    · exact absurd hband (hmR p hp)
  · intro hp
    exact ⟨Or.inl hp, htR p hp⟩

/-! ## The first-difference Gibbs cost -/

/-- **(22) The first-difference Gibbs cost.**  One replacement costs at most the gap times the
Gibbs parameter. -/
theorem exp_neg_sub_le {x n q : ℝ} (hx : 0 ≤ x) (hn : 0 ≤ n) (hnq : n ≤ q) :
    |Real.exp (-(x * q)) - Real.exp (-(x * n))| ≤ x * (q - n) := by
  have hxq : x * n ≤ x * q := mul_le_mul_of_nonneg_left hnq hx
  have hmono : Real.exp (-(x * q)) ≤ Real.exp (-(x * n)) := by
    exact Real.exp_le_exp.2 (by linarith)
  rw [abs_of_nonpos (by linarith), neg_sub]
  have hkey : Real.exp (-(x * n)) - Real.exp (-(x * q))
      = Real.exp (-(x * n)) * (1 - Real.exp (-(x * q - x * n))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    ring_nf
  rw [hkey]
  have hbound : 1 - Real.exp (-(x * q - x * n)) ≤ x * q - x * n := by
    have := Real.add_one_le_exp (-(x * q - x * n))
    linarith
  have hnn : 0 ≤ 1 - Real.exp (-(x * q - x * n)) := by
    have : Real.exp (-(x * q - x * n)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    linarith
  have hle1 : Real.exp (-(x * n)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  calc Real.exp (-(x * n)) * (1 - Real.exp (-(x * q - x * n)))
      ≤ 1 * (1 - Real.exp (-(x * q - x * n))) := mul_le_mul_of_nonneg_right hle1 hnn
    _ ≤ x * q - x * n := by linarith
    _ = x * (q - n) := by ring

/-! ## The whole-anchor column product -/

/-- **(19)-(21) The whole-anchor column product.**  Multiplying the inverse-interval count by the
edge weight cancels the reservoir product exactly: only the co-moving ratio, the two logarithmic
losses and the harmonic normalizer survive. -/
theorem wholeAnchor_column_product {q n t H Λ₁ Λ₂ C : ℝ} (hq : 0 ≤ q) (hn : 0 < n) (ht : 0 < t)
    (hH : 0 < H) :
    (C * Real.sqrt (q * t) * Λ₂) * (Λ₁ / (H * Real.sqrt (n * t)))
      = C * Λ₁ * Λ₂ * Real.sqrt (q / n) / H := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  rw [Real.sqrt_mul hq, Real.sqrt_mul hn.le, Real.sqrt_div' q hn.le]
  field_simp

end RHTower
