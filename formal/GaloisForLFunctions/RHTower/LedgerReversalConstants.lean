/-
# LedgerReversalConstants — the analytic guards of Theorem B⁗ (doc 41; task #147)

Two self-contained, verifiable constants from the (B⁗-a) sup lemma and (B⁗-b) remainder
(doc 41), the pieces doc 41 §5(3) flags as the natural RHTower bricks:

* `four_thirds_sub_log_three_lt_quarter` — the c = 2 closed-form value of the reversal
  ledger `R(1/2, 2, 0) = 4/3 − log 3` is strictly below the `1/4` budget. This is the
  base point of the Sup Lemma `sup_{c≥2} R(1/2,c,0) < 1/4` (the full grid + Lipschitz +
  tail bound remain certified-numerics / interval-arithmetic grade, doc 41 §4).
* `posTwo_algebraic_criterion` — the algebraic heart of Lemma P at `c = 2`: the paper's
  positivity criterion `(POS₂)` reduces, after the `(m,r)`-frame substitution
  `cosh m = e^r`, to `cosh m · (1 + cosh m) ≥ cosh² m + 1`, i.e. exactly `cosh m ≥ 1`
  (`Real.one_le_cosh`). This makes the `⁺`-clip of the reversal integrand vacuous at the
  working base point, so the abstract reversal shells (`weighted_pair_reversal_nonpos`,
  `LedgerConvex`) apply with the loss weight bounded by the gain weight.

The lift of `(POS₂)` to all `c ≥ 2` (the `y/sinh(cy)`-monotonicity, needing
`sinh x < x cosh x`) is the one analytic step left for the parallel formalization of the
(SPUR-R)/(AMP) stack (task #143); it is not reproved here.
-/
import Mathlib

namespace RHTower

/-- **(B⁗-a) base point.** The exact `c = 2` reversal value `R(1/2,2,0) = 4/3 − log 3`
is strictly below the `1/4` budget. Proof by the integer comparison `2^11 < 3^7`
(`2048 < 2187`) fed through `log` monotonicity and the mathlib bound
`0.6931471803 < log 2`: `7·log 3 > 11·log 2 > 7.624…`, so `log 3 > 1.089… > 13/12`. -/
theorem four_thirds_sub_log_three_lt_quarter :
    (4 : ℝ) / 3 - Real.log 3 < 1 / 4 := by
  have h1 : Real.log ((2 : ℝ) ^ 11) < Real.log ((3 : ℝ) ^ 7) := by
    apply Real.log_lt_log (by positivity)
    norm_num
  rw [Real.log_pow, Real.log_pow] at h1
  have h2 := Real.log_two_gt_d9
  push_cast at h1
  nlinarith [h1, h2]

/-- **Lemma P at `c = 2` (algebraic criterion `(POS₂)`).** After the `(m,r)`-frame
substitution the `c = 2` positivity of the continuum pair integrand `Ψ₂` is equivalent
to `cosh m · (1 + cosh m) ≥ cosh² m + 1`, which holds for every `m` because
`cosh m ≥ 1`. Hence the reversal integrand needs no positive-part clipping at the base
point — the input the abstract reversal shells consume. -/
theorem posTwo_algebraic_criterion (m : ℝ) :
    Real.cosh m ^ 2 + 1 ≤ Real.cosh m * (1 + Real.cosh m) := by
  nlinarith [Real.one_le_cosh m]

end RHTower
