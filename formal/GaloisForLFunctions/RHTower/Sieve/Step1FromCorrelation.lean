import GaloisForLFunctions.RHTower.Sieve.MoebiusUnweighted
import GaloisForLFunctions.RHTower.Sieve.SquarefreeExceptional

/-!
# Step 1 from a correlation bound

Composing the two halves: the shifted Möbius correlations bound the mean square, and the mean square
bounds the exceptional starts.  So

`X ≤ #{good starts} + (L·Q + 2L(Lε + (2L+1)L))/(DL/8)² + W/θ`

with `θ = ½DL - (R + L/R)`, from a bound `ε` on the `L-1` shifted correlations and the elementary
truncation-tail bound `W`.

No mean-square theorem is cited anywhere in the chain; the only non-elementary hypothesis is the
correlation bound itself.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **Step 1 of the Hall-law argument from a correlation bound.** -/
theorem card_le_good_add_correlation {X L R M : ℕ} {ε W : ℝ} (hR : 1 ≤ R)
    (hM : ∀ t ∈ Finset.range X, t + L ≤ M)
    (hδ : 0 < (1 / 8) * squarefreeDensity * (L : ℝ))
    (hθ : 0 < (1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ)))
    (hε : 0 ≤ ε)
    (hcorr : ∀ h ∈ Finset.Ico 1 L,
      |∑ n ∈ (Finset.range (X + L + 1 - h)).filter (fun n => L ≤ n ∧ n + h ≤ X),
        ((moebius n : ℤ) : ℝ) * ((moebius (n + h) : ℤ) : ℝ)| ≤ ε)
    (hdef : ∑ t ∈ Finset.range X, ∑ d ∈ Finset.Icc (R + 1) M,
        ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ) ≤ W) :
    ((Finset.range X).card : ℝ)
      ≤ (((Finset.range X).filter (fun t =>
          (3 / 16) * squarefreeDensity * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * squarefreeDensity * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
        + ((L : ℝ) * (((Finset.range (X + L + 1)).filter (fun n => Squarefree n)).card : ℝ)
            + 2 * (L : ℝ) * ((L : ℝ) * ε + ((2 * L + 1 : ℕ) : ℝ) * (L : ℝ)))
          / ((1 / 8) * squarefreeDensity * (L : ℝ)) ^ (2 : ℕ)
        + W / ((1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ))) :=
  card_le_good_add_explicit hR hM hδ hθ (sum_sq_moebius_le_of_correlation hε hcorr) hdef

end RHTower.Sieve
