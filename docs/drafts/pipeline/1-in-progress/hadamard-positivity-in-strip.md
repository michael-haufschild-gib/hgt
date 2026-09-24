# Hadamard positivity inside the critical strip

**Classification:** `[BRIDGE]`. RH remains unproved. This widens an exact RH receiver from
`Re s ≥ 1` to the zero-free region, with the same constant.

## The receiver

RH ⟺ `Re (ξ'/ξ)(s) ≥ 0` for every `Re s > ½`. The corpus proves the `⟸` direction
(`re_le_half_add_of_lagPoleSeries_re_nonneg` in the lag coordinates,
`riemannHypothesis_iff_lagPoleSeries_re_nonneg`), and proves positivity unconditionally on
`Re s ≥ 1` (`re_logDeriv_xi_pos_of_one_le_re`).

## The new theorem

`RHTower.re_logDeriv_xi_nonneg_of_zeroFree`
(`formal/GaloisForLFunctions/RHTower/XiLogDerivZeroFreePositive.lean`):

```text
1 − 1/58 / log(4(|Im s| + 1)) ≤ Re s   →   0 ≤ Re (ξ'/ξ)(s).
```

Axiom-clean. The width is exactly that of the corpus's zero-free region
`re_le_one_sub_of_zeta_zero : β ≤ 1 − 1/(58 log|γ|)`.

## Mechanism

`xiPairedResolventTerm s q = (Re s − β)/|s−ρ|² + (Re s − (1−β))/|s−(1−ρ)|²`, and
`2 Re (ξ'/ξ)(s) = ∑_q xiPairedResolventTerm s q`. Clearing denominators, the numerator is

```text
u·|s−(1−ρ)|² + v·|s−ρ|² = 2( x(x² − a²) + x(t² + γ²) − 2 a t γ ),
x = Re s − ½,  a = β − ½,  t = Im s,  u = x − a,  v = x + a.
```

* **Near regime** `log|γ| ≤ log(4(|t|+1))`. The zero-free region, in displacement form
  `|β − ½| ≤ ½ − 1/(58 log|γ|)` (`abs_re_sub_half_le_of_xiZeroCopy`, from
  `re_le_one_sub_of_zeta_zero` and `one_div_le_re_of_zeta_zero`), gives `|a| ≤ x`. Then
  `2·numerator = 4x(x²−a²) + 2(x−a)(t+γ)² + 2(x+a)(t−γ)²` is a sum of nonnegative terms.
* **Far regime** `log|γ| > log(4(|t|+1))`, i.e. `|γ| > 4(|t|+1)`. The region is too weak to bound
  `|a|` by `x` there, but the distance dominates: `2atγ ≤ |t||γ|` (since `|a| ≤ ½`),
  `x ≥ ¼` gives `x(t²+γ²) ≥ (t²+γ²)/4`, and `|γ| − 4|t| ≥ 4` with `|γ| ≥ 4` gives
  `(t²+γ²)/4 − |t||γ| ≥ 4`, while `x(x²−a²) ≥ −⅛`.

No zero counting, no density estimate and no analytic bound are used.

## What remains

The far regime is robust — it has slack `4` against `⅛`. The binding constraint is the near
regime, where the admissible width is exactly the zero-free-region width. Consequently:

* any improvement of the zero-free region transfers verbatim to this receiver;
* conversely, reaching `Re s > ½` through this route requires a zero-free region of *fixed* width,
  i.e. quasi-RH. The termwise analysis is exact (CANNOT-323): a copy with `|a| > x` genuinely makes
  its own pair term negative once `s` approaches its pole, so no sharpening of the pair algebra can
  extend the region.
