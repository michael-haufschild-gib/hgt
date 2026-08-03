import GaloisForLFunctions.RHTower.Sieve.CharacterSeparation

/-!
# Two close frequencies must nearly coincide

The character-separation bound `∑_{p ∈ P}(1 - cos(v log p))/p ≤ 4δ²` becomes a constraint on `v`
itself through Jordan's inequality: for `|x| ≤ π`,

`1 - cos x ≥ (2/π²) x²`,

so on the primes where `|v log p| ≤ π`,

`v² ∑_{p ∈ P} (log p)²/p ≤ 2π² δ²`.

The weight `∑_p (log p)²/p` grows, so the admissible window for `v` shrinks: a multiplicative
function cannot be close to two genuinely different characters.  This is the quantitative form of the
uniqueness statement.
-/

namespace RHTower.Sieve

open Finset

/-- Jordan's inequality in the form `1 - cos x ≥ (2/π²) x²` on `|x| ≤ π`. -/
theorem two_div_pi_sq_mul_sq_le_one_sub_cos {x : ℝ} (hx : |x| ≤ Real.pi) :
    2 / Real.pi ^ 2 * x ^ 2 ≤ 1 - Real.cos x := by
  have h := Real.cos_le_one_sub_mul_cos_sq hx
  linarith

/-- **Quantitative frequency separation.** -/
theorem sq_mul_sum_sq_log_le_of_close {f : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (hP : ∀ p ∈ P, 0 < p) {t u δ : ℝ}
    (ht : Real.sqrt (mulDistSqPair f (charFn t) P) ≤ δ)
    (hu : Real.sqrt (mulDistSqPair f (charFn u) P) ≤ δ)
    (hsmall : ∀ p ∈ P, |(t - u) * Real.log (p : ℝ)| ≤ Real.pi) :
    (t - u) ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) ^ 2 / (p : ℝ) ≤ 2 * Real.pi ^ 2 * δ ^ 2 := by
  have hπ : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hmain := sum_one_sub_cos_le_of_close hf hP ht hu
  have hterm : ∀ p ∈ P,
      2 / Real.pi ^ 2 * ((t - u) ^ 2 * (Real.log (p : ℝ) ^ 2 / (p : ℝ)))
        ≤ (1 - Real.cos ((t - u) * Real.log (p : ℝ))) / (p : ℝ) := by
    intro p hp
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
    have hstep : (2 / Real.pi ^ 2 * ((t - u) * Real.log (p : ℝ)) ^ 2) / (p : ℝ)
        ≤ (1 - Real.cos ((t - u) * Real.log (p : ℝ))) / (p : ℝ) := by
      gcongr
      exact two_div_pi_sq_mul_sq_le_one_sub_cos (hsmall p hp)
    calc 2 / Real.pi ^ 2 * ((t - u) ^ 2 * (Real.log (p : ℝ) ^ 2 / (p : ℝ)))
        = (2 / Real.pi ^ 2 * ((t - u) * Real.log (p : ℝ)) ^ 2) / (p : ℝ) := by ring
      _ ≤ _ := hstep
  have hsum := Finset.sum_le_sum hterm
  set X := (t - u) ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) ^ 2 / (p : ℝ) with hXdef
  have hleft : ∑ p ∈ P, 2 / Real.pi ^ 2 * ((t - u) ^ 2 * (Real.log (p : ℝ) ^ 2 / (p : ℝ)))
      = 2 / Real.pi ^ 2 * X := by
    rw [hXdef, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hleft] at hsum
  have hX : 2 / Real.pi ^ 2 * X ≤ 4 * δ ^ 2 := le_trans hsum hmain
  have hmul := mul_le_mul_of_nonneg_right hX (le_of_lt hπ)
  have heq : (2 / Real.pi ^ 2 * X) * Real.pi ^ 2 = 2 * X := by
    field_simp
  rw [heq] at hmul
  linarith

end RHTower.Sieve
