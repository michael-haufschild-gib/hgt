import GaloisForLFunctions.RHTower.Sieve.DampedPlainCompare

/-!
# Summing the damped–plain comparison over the primes

The Euler exponents of the damped and the plain Möbius series are both summable over the primes on
`Re s > 1`, so their difference may be summed term by term.  Combined with the term-level bound of
`Sieve/DampedPlainCompare`, whose right-hand side vanishes off the finite set `P`, this is the step
that turns the corpus's undamped reconciliation between the `σ`-level prime sum and the truncated one
into the damped reconciliation.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- The Euler exponent is summable over the primes. -/
theorem summable_re_twistedSummand_primes {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => (twistedSummand f s (p : ℕ)).re) := by
  have hnorm : Summable (fun p : Nat.Primes => ‖twistedSummand f s (p : ℕ)‖) :=
    (summable_norm_twistedSummand hbdd hs).comp_injective Nat.Primes.coe_nat_injective
  refine Summable.of_norm_bounded hnorm ?_
  intro p
  rw [Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

/-- The difference of the two Euler exponents is summable. -/
theorem summable_abs_re_damped_sub_plain {P : Finset ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes =>
      |(twistedSummand (dampedOmegaMoebius P t) s (p : ℕ)).re
        - (twistedSummand (fun n => ((moebius n : ℤ) : ℂ)) s (p : ℕ)).re|) := by
  have hD := summable_re_twistedSummand_primes
    (f := dampedOmegaMoebius P t) (fun n => norm_dampedOmegaMoebius_le_one ht0 ht1 n) hs
  have hP := summable_re_twistedSummand_primes
    (f := fun n => ((moebius n : ℤ) : ℂ)) (fun n => by
      rw [show ((moebius n : ℤ) : ℂ) = (((moebius n : ℤ) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact abs_moebius_real_le_one n) hs
  exact (hD.sub hP).abs

/-- **The summed comparison.**  The two Euler exponents differ by at most the total of their
term-level differences. -/
theorem abs_tsum_re_damped_sub_plain_le {P : Finset ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    |(∑' p : Nat.Primes, (twistedSummand (dampedOmegaMoebius P t) s (p : ℕ)).re)
        - ∑' p : Nat.Primes, (twistedSummand (fun n => ((moebius n : ℤ) : ℂ)) s (p : ℕ)).re|
      ≤ ∑' p : Nat.Primes,
          |(twistedSummand (dampedOmegaMoebius P t) s (p : ℕ)).re
            - (twistedSummand (fun n => ((moebius n : ℤ) : ℂ)) s (p : ℕ)).re| := by
  have hD := summable_re_twistedSummand_primes
    (f := dampedOmegaMoebius P t) (fun n => norm_dampedOmegaMoebius_le_one ht0 ht1 n) hs
  have hP := summable_re_twistedSummand_primes
    (f := fun n => ((moebius n : ℤ) : ℂ)) (fun n => by
      rw [show ((moebius n : ℤ) : ℂ) = (((moebius n : ℤ) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact abs_moebius_real_le_one n) hs
  rw [← Summable.tsum_sub hD hP]
  have habs := summable_abs_re_damped_sub_plain (P := P) ht0 ht1 hs
  have h := norm_tsum_le_tsum_norm (f := fun p : Nat.Primes =>
    (twistedSummand (dampedOmegaMoebius P t) s (p : ℕ)).re
      - (twistedSummand (fun n => ((moebius n : ℤ) : ℂ)) s (p : ℕ)).re) (by simpa using habs)
  simpa using h

end

end RHTower.Sieve
