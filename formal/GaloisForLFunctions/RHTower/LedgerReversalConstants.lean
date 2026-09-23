/-
# LedgerReversalConstants — the analytic guards of Theorem B⁗ (doc 41; task #147)

The `c = 2` base-point budget `R(1/2, 2, 0) = 4/3 − log 3 < 1/4` of the Sup Lemma
`sup_{c≥2} R(1/2,c,0) < 1/4` is `reversal_edge_lt_quarter` in `ReversalClosedForm`
(the full grid + Lipschitz + tail bound remain certified-numerics /
interval-arithmetic grade).  Here:

* `posTwo_algebraic_criterion` — the algebraic heart of Lemma P at `c = 2`: the paper's
  positivity criterion `(POS₂)` reduces, after the `(m,r)`-frame substitution
  `cosh m = e^r`, to `cosh m · (1 + cosh m) ≥ cosh² m + 1`, i.e. exactly `cosh m ≥ 1`
  (`Real.one_le_cosh`). This makes the `⁺`-clip of the reversal integrand vacuous at the
  working base point, so the abstract reversal shells (`weighted_pair_reversal_nonpos`,
  `LedgerConvex`) apply with the loss weight bounded by the gain weight.

The lift of `(POS₂)` to all `c ≥ 2` (the `y/sinh(cy)`-monotonicity via
`sinh x < x cosh x`) is closed in `ReversalPositivity` (`posC_of_posTwo`).
-/
import Mathlib

namespace RHTower

/-- **Lemma P at `c = 2` (algebraic criterion `(POS₂)`).** After the `(m,r)`-frame
substitution the `c = 2` positivity of the continuum pair integrand `Ψ₂` is equivalent
to `cosh m · (1 + cosh m) ≥ cosh² m + 1`, which holds for every `m` because
`cosh m ≥ 1`. Hence the reversal integrand needs no positive-part clipping at the base
point — the input the abstract reversal shells consume. -/
theorem posTwo_algebraic_criterion (m : ℝ) :
    Real.cosh m ^ (2 : ℕ) + 1 ≤ Real.cosh m * (1 + Real.cosh m) := by
  nlinarith [Real.one_le_cosh m]

end RHTower
