import GaloisForLFunctions.RHTower.Sieve.DampedPrimeTerm

/-!
# Damped against plain, term by term

The damped Möbius function differs from `μ` only at the designated primes, so the Euler exponents
differ only there, and at each such prime by at most `p^{-σ}`.  Summed over `P` that is at most the
harmonic mass `∑_{p ∈ P} 1/p`, the same quantity that
`RHTower/DampedPretentiousGap.dampedCosPlusSum_ge` pays.

This is the term-level statement; it is what turns the corpus's undamped reconciliation between the
`σ`-level prime sum and the truncated one into the damped reconciliation.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- The plain Möbius twisted summand, in cosine form. -/
theorem twistedSummand_moebius_prime_re {p : ℕ} (hp : p.Prime) (σ τ : ℝ) :
    (twistedSummand (fun n => ((moebius n : ℤ) : ℂ)) ((σ : ℂ) + (τ : ℂ) * Complex.I) p).re
      = -((p : ℝ) ^ (-σ) * Real.cos (τ * Real.log p)) := by
  have hp0 : 0 < p := hp.pos
  have hmu : ((moebius p : ℤ) : ℂ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring
  rw [twistedSummand, hmu, show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, re_natCast_cpow_neg hp0 σ τ]
  ring

/-- **The two Euler exponents differ only on the designated primes, and there by at most `1/p`.** -/
theorem abs_twistedSummand_damped_sub_plain_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1 ≤ σ) (τ : ℝ) :
    |(twistedSummand (dampedOmegaMoebius P t) ((σ : ℂ) + (τ : ℂ) * Complex.I) p).re
        - (twistedSummand (fun n => ((moebius n : ℤ) : ℂ))
            ((σ : ℂ) + (τ : ℂ) * Complex.I) p).re|
      ≤ if p ∈ P then (1 : ℝ) / p else 0 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  rw [twistedSummand_dampedOmegaMoebius_prime_re hPprime hp t σ τ,
    twistedSummand_moebius_prime_re hp σ τ]
  have hpow : (p : ℝ) ^ (-σ) ≤ 1 / (p : ℝ) := by
    have h1 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at h1
  have hpow0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg hp0.le _
  have hcos := Real.neg_one_le_cos (τ * Real.log p)
  have hcos' := Real.cos_le_one (τ * Real.log p)
  by_cases hmem : p ∈ P
  · rw [if_pos hmem, if_pos hmem]
    set A : ℝ := (p : ℝ) ^ (-σ) with hA
    set c : ℝ := Real.cos (τ * Real.log p) with hc
    have heq : -(t * (A * c)) - -(A * c) = (1 - t) * (A * c) := by ring
    rw [heq, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t), abs_mul,
      abs_of_nonneg hpow0]
    have hcabs : |c| ≤ 1 := abs_le.2 ⟨hcos, hcos'⟩
    calc (1 - t) * (A * |c|) ≤ 1 * (A * 1) :=
          mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hcabs hpow0)
            (mul_nonneg hpow0 (abs_nonneg c)) (by norm_num)
      _ = A := by ring
      _ ≤ 1 / (p : ℝ) := hpow
  · rw [if_neg hmem, if_neg hmem]
    simp

end

end RHTower.Sieve
