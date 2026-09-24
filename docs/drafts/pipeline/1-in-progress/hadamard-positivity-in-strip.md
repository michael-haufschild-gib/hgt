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

## The tail carries no obstruction

`RHTower.xiPairedResolventTerm_nonneg_tail` (`RHTower/XiHadamardTailNonneg.lean`) removes the
zero-free region from the far regime entirely. With `x = Re s − ½ > 0` and `ξ(s) ≠ 0`, every copy
with

```text
|γ| ≥ hadamardTailHeight s = (|Im s| + 1)/x + 1
```

has nonnegative paired term, **unconditionally** — no hypothesis on `β` at all. Hence

```text
∑_{|γ| < hadamardTailHeight s} (paired term) ≤ 2 Re (ξ'/ξ)(s)
```

(`tsum_low_le_two_mul_re_logDeriv_xi`), and `re_logDeriv_xi_nonneg_of_low_nonneg` says the low part
alone decides the receiver.

So the Hadamard criterion for RH is **local in the height**: at each test point only finitely many
copies can obstruct it, and the infinite tail is always on the right side. This removes a whole
class of would-be difficulties (tail convergence, cancellation at infinity) from the criterion and
concentrates everything on the local obstruction of CANNOT-323.

## Correction and sharpening

The tail localization above uses the reflection pairing `ρ ↦ 1 − ρ`, whose far regime only reaches
ordinate `(|Im s| + 1)/(Re s − ½) + 1`. The corpus already had a strictly sharper statement in the
**line-conjugate** pairing `ρ ↦ 1 − conj ρ`, which preserves the ordinate:
`re_inv_add_re_inv_lineConj_pos_of_far` (`RHTower/XiHadamardPairSignLaw.lean`) gives positivity of
a pair as soon as `(Re s − ½)² + (Im s − Im ρ)² ≥ ¼`. The obstruction window is therefore
`|Im s − Im ρ| < ½`: **bounded, independent of the height.**

`RHTower/XiHadamardSharpRegion.lean` builds on that:

* `re_logDeriv_xi_nonneg_of_window` — only copies inside the window can obstruct;
* `re_logDeriv_xi_nonneg_of_abs_im_le_four` — every copy has `|Im ρ| > 4.5`
  (`four_half_lt_abs_im_of_xiZeroCopy`), so for `|Im s| ≤ 4` the window is empty and the receiver
  holds on the **entire rectangle** `Re s > ½`, `|Im s| ≤ 4`;
* `re_logDeriv_xi_nonneg_of_zeroFree_sharp` — for `|Im s| > 4`, inside the window
  `|Im ρ| < |Im s| + ½`, so the zero-free region gives positivity on
  `Re s ≥ 1 − 1/58 / log(|Im s| + ½)`, strictly wider than the region above.

The earlier statements remain true and built, but are superseded by these.

## Consumer form: horizontal monotonicity of `|ξ|`

`RHTower/XiHorizontalMonotone.lean` (MUST-381). `∂_σ ‖ξ(σ+it)‖² = 2‖ξ‖² Re(ξ'/ξ)(σ+it)`
(`hasDerivAt_normSq_xi_horizontal`, unconditional), so positivity of `Re(ξ'/ξ)` on a convex set of
abscissas is exactly horizontal monotonicity of `|ξ|` there
(`monotoneOn_normSq_xi_horizontal`). Instantiating the two regions:

* `monotoneOn_norm_xi_low`: for `|t| ≤ 4`, `|ξ(σ+it)|` is nondecreasing on all of `σ > ½`;
* `monotoneOn_norm_xi_high`: for `|t| > 4`, on `σ ≥ 1 − 1/(58 log(|t| + ½))`.

The corpus's Sondow–Dumitrescu monotonicity
(`strictMonoOn_norm_XiC_horizontal_of_halfPlaneBound`) is parametrized by a *uniform* half-plane
zero bound and unconditionally reaches only `Re s ≥ 1`. `monotoneOn_normSq_xi_horizontal` is stated
for an arbitrary convex abscissa set, so any future improvement of the positivity region upgrades
the monotonicity statement for free.
