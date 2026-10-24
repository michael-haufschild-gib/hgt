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
scratch-file kernel check. Named-file final check and transitive axiom audit
remain before advancing the card.

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

## Verification obligations

Direct leaf checks only; no umbrella build. Audit transitive axioms, wire the
completed modules, remove owned scratch files. No web, novelty audit, numerical
experiment, unproved analytic premise, or raised Lean limit.
