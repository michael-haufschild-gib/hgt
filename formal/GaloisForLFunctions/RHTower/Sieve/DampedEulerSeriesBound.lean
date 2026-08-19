import GaloisForLFunctions.RHTower.Sieve.DampedMultiplicative
import GaloisForLFunctions.RHTower.Sieve.MultiplicativeEulerBound

/-!
# The damped Möbius series is bounded by its prime sum

The damped Möbius function is multiplicative, unit-bounded and equal to `1` at `1`, so the corpus's
Euler bound applies to it verbatim: on `Re s > 1` the whole series, prime powers included, is damped
by the real part of its prime sum.

Since that prime sum is `−∑_p (if p ∈ P then t else 1)·Re(p^{-s})`, and
`RHTower/DampedPretentiousGap` bounds the corresponding positive sum from below uniformly in the
damping and in the frequency, this is the step that turns the pretentious distance into a bound on
the Dirichlet series — the object Halász's argument integrates.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- **The Euler bound for the damped Möbius series.** -/
theorem norm_tsum_dampedOmegaMoebius_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖∑' n : ℕ, twistedSummand (dampedOmegaMoebius P t) s n‖
      ≤ Real.exp
          ((∑' p : Nat.Primes, (twistedSummand (dampedOmegaMoebius P t) s (p : ℕ)).re) + 5 / 2) :=
  norm_tsum_twistedSummand_le_exp (f := dampedOmegaMoebius P t)
    (dampedOmegaMoebius_one hPprime t)
    (fun {_ _} h => dampedOmegaMoebius_mul_of_coprime hPprime t h)
    (fun n => norm_dampedOmegaMoebius_le_one ht0 ht1 n) hs

end

end RHTower.Sieve
