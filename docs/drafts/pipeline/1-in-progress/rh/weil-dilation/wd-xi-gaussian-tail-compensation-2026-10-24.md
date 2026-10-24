# Xi finite head and compensated Gaussian tail

- **Stage:** 1-in-progress.
- **Type:** THEOREM (paper), Lean in progress; stronger source-scale conjecture open.
- **Route:** WD: directed source current → negative-cross control or collision charge < 2 → RH.
- **Open core:** global cap vanishing, full signed prime–Gamma contraction, uniform zero-block absorption.

## Programme connection

Arithmetic Compensation Theory says to subtract the coherent component before
taking norms. Applied to the Gaussian-background model, the coherent component
is the exponential of the exact quadratic reciprocal-zero sum. A magnitude
envelope for the whole Xi product does not estimate this difference.

Signed Arithmetic Energy Incidence supplies exact companion-sampling prices,
including off-diagonal configuration Grams. Arithmetic Orientation Theory
retains a rank-one square per prime tower. These suggest retaining an entire
finite zero block and its mixed terms, rather than paying each zero separately.
Neither programme supplies the actual Xi companion geometry or the complete
signed prime–Gamma bound.

## Conjecture loop

### C1. Exact source tail admits a fourth-moment Gaussian remainder — Lean proof checked

For a real ordinate `gamma` with `XiC gamma != 0`, put
`b_q = (xiSpectralPoint q - gamma)^(-2)`. For any finite set of zero copies `H`,
let `P_H(z) = product_{q in H}(1+z^2*b_q)` and set

```
C_H = sum_{q notin H} b_q,
A_H = sum_{q notin H} |b_q|,
B_H = sum_{q notin H} |b_q|^2.
```

Then all sums converge and, at every complex `z`,

```
|S_gamma(z)/S_gamma(0) - P_H(z)*exp(z^2*C_H)|
 <= |P_H(z)| * exp(2*|z|^2*A_H) * |z|^4*B_H.
```

**Proof.** Translated reciprocal-square summability is already unconditional
in the corpus. It gives summability of `b_q`, `|b_q|`, and `|b_q|^2`; for the
last, bound each `|b_q|` by the total sum. The finite Banach-algebra theorem
`FormationDust.norm_prod_one_add_sub_exp_le` bounds the product/exponential
difference by `exp(2 sum |x_q|) sum |x_q|^2`. Apply it to the complementary
copies with `x_q=z^2*b_q` and pass to the absolutely convergent sums and
convergent product. Multiply by `P_H`. The existing exact Xi product limit
identifies the product with `S_gamma(z)/S_gamma(0)`. This proves the assertion
without assuming a Gaussian approximation, a zero-spacing condition, or RH.

The bound retains the complex quadratic sum `C_H`; replacing it by the
nonnegative size `A_H` would discard the orientation being estimated.

**Lean.** `RHTower/XiSliceGaussianTailComparison.lean` contains
`norm_xiSliceGaussianTail_sub_exp_le`,
`xiSliceProduct_div_eq_gaussianHead_mul_tail`, and
`norm_xiSliceProduct_sub_gaussianHead_exp_le`. The complete source passed a
scratch-file kernel check and its named production olean build. All three
capstones passed `#print axioms`: only `propext`, `Classical.choice`,
`Quot.sound`. A final named check without output files remains before
advancing the card.

### C2. A rescaled far tail is an actual Gaussian limit — paper argument

Take `H` to contain the zeros within distance `R` of the ordinate. Seek
`B_H/A_H^2 -> 0` and `C_H/A_H -> 1`, using actual zero counting and the
unconditional spectral strip. C1 then gives a locally uniform Gaussian
limit on the natural scale `z=y/sqrt(A_H)`. This is a statement about the
actual Xi divisor, not an assumed model background.

**Paper proof.** Fix the ordinate. The unconditional Riemann–von Mangoldt
law gives at least `R` zero copies with positive ordinates in `(2R,4R]`
for every sufficiently large `R`. They lie outside the distance-`R` head
and within distance `5R` of the fixed ordinate. Therefore
`A_H >= 1/(25R) > 0`. Outside the head, `|b_q| <= R^(-2)`, hence
`B_H <= A_H/R^2` and `B_H/A_H^2 <= 25/R -> 0`.

For `z_q=x+iy=xiSpectralPoint q-gamma`, the strip gives `|y|<1/2`.
Writing `b_q=conj(z_q)^2/|z_q|^4` shows
`|b_q-|b_q|| <= 2|y|/|z_q| * |b_q| <= |b_q|/R`.
Consequently `|C_H-A_H| <= A_H/R`; in particular `C_H/A_H -> 1`.
At `z=y/sqrt(A_H)`, C1 bounds the tail difference from
`exp(y^2*C_H/A_H)` by
`exp(2|y|^2)|y|^4 B_H/A_H^2`. Both this error and the difference of
the exponentials tend uniformly to zero on every fixed complex ball.
Thus the actual complementary Xi product converges to `exp(y^2)` under
the stated moving rescaling. The finite head is retained exactly.

**Remaining distinction.** A far-tail Gaussian limit does not yet control a
dense nearby block at the coefficient order selected by the heat model.
Uniform passage at those moving orders, and a source sign, remain to prove.

The corpus theorem `eventually_card_xiCopiesBand_mul_two_lower` supplies the
dyadic multiplicity count directly. The Lean construction uses the exact
distance head and the symmetric band `(2R,4R]`, keeping the fourth-moment
bound `25/R` after normalization.

### C3. Multiplicative compensation removes the total-mass exponential — paper proof

C1 still pays `exp(2|z|^2 A_H)`. This can overwhelm a small fourth moment in
a dense background. Instead compensate each factor before estimating it.
For the distance-`R` head, `R>0`, write `x_q=z^2 b_q`,
`eta=|z|^2/R^2`, and `u_q=(1+x_q)exp(-x_q)`. Then

```
|exp(-z^2 C_H) T_H(z) - 1|
 <= exp(exp(2*eta) * |z|^4 B_H) - 1.
```

**Proof.** The existing exponential Taylor bound gives
`|u_q-1| <= |x_q|^2 exp(2|x_q|) <= exp(2eta)|x_q|^2`.
The right side is summable. For any finite set,
`|product u_q-1| <= product (1+|u_q-1|)-1
 <= exp(sum |u_q-1|)-1`; the first inequality follows by induction from
`ab-1=(a-1)b+(b-1)`. Passing to limits proves the same bound for the
infinite product. Absolute summability of `x_q` identifies that product
with `exp(-sum x_q) product(1+x_q)`. Summing the termwise bound gives
the displayed estimate.

This is stronger than C1 in a dense background: the error no longer pays an
exponential in `A_H`. It still does not control the retained block or give
an RH sign. The next source estimate to attack is a fourth-moment bound
uniform in a moving height and cutoff.

**Corpus connection and stronger survivor.** These compensated factors are
exactly genus-one Weierstrass factors, `u_q=E1(-x_q)`. The corpus already
proves `|E1(w)-1| <= |w|^2` for `|w|<=1` and the infinite-product bound
`|product(1+v_q)-1| <= exp(sum|v_q|)-1`. Consequently, on `|z|<=R`,

```
|exp(-z^2 C_H) T_H(z) - 1| <= exp(|z|^4 B_H)-1.
```

The parent estimate is existing canonical-product mathematics. The new
source work is its exact centered Xi tail identification and the subsequent
unconditional estimates on the actual moments; no external novelty claim.

### C4. A dense Gaussian tail at growing height — paper route

For `t>=4`, `R>=3`, the existing source partial-fraction bound yields
`A_R(t) <= D log t`, hence `B_R(t) <= D log t/R^2`, with an absolute
constant `D=4(3650+5 smallHeightCount)`.

To see the first bound, put `d=|xiSpectralPoint(q)-t|>R` and compare with
`s=2+it`, `s0=3+it` in `sum_norm_partialFractionDiff_le`. Both distances
from these anchors to the corresponding xi zero are at most `2d`, while
`|s0-s|=1`. Therefore
`d^-2 <= 4 |(s-rho)^-1-(s0-rho)^-1|`. The anchor `s` is unconditionally
at distance at least one from every zero by the open critical strip.
Sum over arbitrary finite tail subsets and pass to the summable limit.
Multiplying the termwise `|b_q|<=R^-2` gives the fourth-moment bound.

The logarithmic Riemann--von Mangoldt remainder
`exists_xiZeroCount_routeKSmoothRVMCount_log_remainder` also gives, for
large `t`, all sufficiently large `R<=t/4`, at least
`R log t/(4 pi)` positive-ordinate copies in `(t+2R,t+4R]`.
Indeed the smooth-count difference is at least `R log t/(2 pi)` once
`log t>=2 log routeKRVMBase`; the two remainder terms together cost at
most `4 C log t`, absorbed when `R>=16 pi C`. Distances of these copies
lie in `(R,5R]`, so `A_R(t)>=log t/(100 pi R)`.

Thus at `t=exp(u^4)`, `R=u^3`, one has `A_R(t)>=u/(100 pi)->infinity`
and `B_R(t)<=D/u^2->0`. C3 gives relative Gaussian approximation on every
fixed physical disc, even though the quadratic mass diverges. This is the
scale missing from C2's fixed-center normalization.

**Exact real orientation to formalize.** The reflection `lagPartner`
preserves the radius head and conjugates the spectral point. Its tail
reciprocal sum is therefore real. Moreover, writing `d_q` for the centered
spectral point gives

```
A_R - C_R = 2 sum_{tail} (Im d_q)^2 / |d_q|^4,
0 <= A_R-C_R <= B_R/2.
```

This follows termwise from `Re(d^-2)=(Re(d)^2-Im(d)^2)/|d|^4`, with
imaginary parts canceling under the involution. It also permits replacing
the exact real quadratic coefficient by `A_R` with an absolute error
vanishing with `B_R`. No nearby zero factors are discarded: their growing
finite block remains the unresolved part of the heat-sign transfer.

### Further conjecture tested: positivity of the remote factors

Conjugate reciprocal-square factors have polynomial
`1+2 Re(b) z^2+|b|^2 z^4`; outside the local strip cone, `Re(b)>=0`.
This is already the mechanism of `XiHorizontalSliceConeCriterion`, so it
does not provide a new source sign. Retaining the finite bad-cone block
remains essential. Continue with the multiplicatively compensated error
and moving-height fourth moments, rather than repackage that cone criterion.

## Verification obligations

Direct leaf checks only; no umbrella build. Audit transitive axioms, wire the
completed modules, remove owned scratch files. No web, novelty audit, numerical
experiment, unproved analytic premise, or raised Lean limit.

## Implementation checkpoint

- Gaussian model completed separately in
  `docs/drafts/pipeline/3-formalized/wd-gaussian-background-heat-law.md`.
- C1 production module and umbrella import exist; olean built for the next module.
- C2 full proof draft: `/tmp/wd_gaussian_tail_limit.lean`; first check found
  elaboration/coercion issues, now corrected for the next check. Intended
  production name: `RHTower/XiSliceGaussianTailLimit.lean`.
- C3 genus-one compensation proof draft:
  `/tmp/wd_gaussian_multiplicative_compensation.lean`; explicit finite-product
  and finite-sum `Tendsto` types replace ambiguous `HasProd`/`HasSum` methods.
- C4 actual logarithmic moment-bound draft: `/tmp/wd_gaussian_tail_height.lean`.
  Not checked yet. Exact real orientation and growing-height lower mass are
  paper-proved above and still require Lean implementation.
