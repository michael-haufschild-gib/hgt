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
scratch-file kernel check, production olean build, and final named check.
All three capstones passed `#print axioms`: only `propext`,
`Classical.choice`, `Quot.sound`.

### C2. A rescaled far tail is an actual Gaussian limit — Lean verified

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

**Lean.** `RHTower/XiSliceGaussianTailLimit.lean` builds successfully. Its
capstone `tendstoUniformlyOn_xiSliceGaussianNormalizedTail t M` has no
analytic or zero-location premises: it applies to every real center and
every fixed complex closed ball. Axiom audits passed; the final named no-output check remains in the
verification batch.

### C3. Multiplicative compensation removes the total-mass exponential

For the distance-`R` head, `R>0`, and `|z|<=R`, the exact theorem is

```
|exp(-z^2 C_H) T_H(z) - 1| <= exp(|z|^4 B_H)-1.
```

**Proof.** Set `x_q=z^2 b_q` and
`u_q=(1+x_q)exp(-x_q)=E1(-x_q)`. The cutoff gives `|x_q|<=1`.
The existing genus-one estimate gives `|u_q-1|<=|x_q|^2`, so these
errors are summable and their sum is at most `|z|^4 B_H`. The existing
infinite-product inequality gives
`|product u_q-1|<=exp(sum |u_q-1|)-1`. Absolute summability of `x_q`
identifies the product with `exp(-z^2 C_H)T_H(z)` and proves the result.

This avoids C1's exponential in total mass `A_H`. The parent inequalities
are existing canonical-product results; the connection identifies their
literal centered Xi tail and retains the finite head. Multiplication by
that head gives the corresponding normalized full-slice comparison.
The finite head's contribution to the signed heat coefficients remains open.

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

**Exact real orientation.** The reflection `lagPartner`
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

### C5. Source mass at the scale needed for moving coefficient orders — paper proof

The crude upper bound in C4 gives `A <= D log t`; this does not control the
coefficient order `k` proportional to the Gaussian mass. Refine the source
bound by summing actual zero-window counts from the cutoff onward.

For an integer `N>=2`, the corpus window bound is
`# {q : k<=|t-Im rho_q|<k+1} <= 80 log(180(t+k+1))+K0`.
The logarithm is at most `6 log t+log(k+2)`. Telescoping gives

```
sum_{k>=N} k^-2 <= 1/(N-1),
sum_{k>=N} (k sqrt k)^-1 <= 2/sqrt(N-1),
log(k+2) <= 2 sqrt k+3.
```

Thus the actual reciprocal-square mass over those windows is at most
`(480 log t+240+K0)/(N-1)+320/sqrt(N-1)`. If the spectral distance exceeds
`R>=2N`, its ordinate distance exceeds `N`: otherwise the strip bound
would give squared spectral distance at most `N^2+1/4 < 4N^2`. Consequently
this bounds the full distance tail. Taking `N=floor(R/2)` yields
`A_R(t)=O(log(t)/R+R^(-1/2))` for `R>=8`.

At `t=exp(u^4)`, `R=u^3`, C4 and this upper bound give `A` bounded above
and below by positive multiples of `u`; also `B<=A/R^2=O(u^-5)`.
In particular `B*A^(3/2)->0`. That rate is relevant to coefficient sign:
at the Gaussian saddle a Cauchy error pays `sqrt(A)`, while the negative
quartic model coefficient has relative size `1/A`. The source rate can
pay their product. A complete heat-integral and finite-block transfer is
still open; this observation is not yet such a transfer theorem.

**Status:** dependency-closed paper proof of the moment estimate above;
Lean implementation and olean build passed; the named final audit remains.
The coefficient-transfer discussion identifies
the next conjecture, not an established sign.

### C6. Expanding-disc Gaussian approximation — paper proof

With the same moving height and cutoff, write `a_u=Re C_R(t)` and
`T_u(z)=product_tail(1+z^2 b_q)`. C3 and C5 prove, for each fixed `M`,

```
sup_{|z|<=M} |exp(-a_u (u z)^2) T_u(u z)-1|
 <= exp(M^4 D/u)-1 -> 0,
a_u -> infinity.
```

Indeed `|uz|<=u^3` eventually, `B<=D/u^5`, and the quadratic coefficient
is exactly real by reflection. Its positive growth follows from
`a_u=A_u-transverse_u`, `A_u>=u/(100 pi)`, and
`0<=transverse_u<=B_u/2`. This upgrades fixed-disc convergence to physical
discs with unbounded radius; no sign of the finite complementary block is
asserted. Also `a_u<=A_u<=Du`, hence `B_u*a_u^2<=D^3/u^3 -> 0` once
`a_u>=0`. This pays a square loss in coefficient size, stronger than the
provisional saddle-loss rate in C5. The complete production module is
`RHTower/XiSliceDenseGaussianTail.lean`; its olean build passed.

### C7. Global real-axis Gaussian bracketing — next exact statement

The fixed-disc error is insufficient by itself for a Gaussian heat integral
over the whole real axis. A stronger, one-sided factor estimate survives:
for a distance cutoff `R>=4`, real `x`, and `a=Re C_R(t)`,

```
exp(a*x^2-B_R*x^4) <= |T_R(x)| <= exp(a*x^2).
```

**Paper proof.** The strip and distance cutoff put each reciprocal `b` in
the cone `Re b >= 3|b|/4`. For `v=x^2 b`, write `r=Re v>=0`.
Then `|v|^2 <= 2r^2`, so
`|1+v|^2=1+2r+|v|^2 <= 1+2r+2r^2 <= exp(2r)`.
For the reverse bound,
`log|1+v| >= log(1+r) >= r-r^2 >= r-|v|^2`.
Exponentiate, multiply over finite tail sets, and pass to the absolutely
convergent product and sums. This proves both bounds, even without invoking
the reflection reality of the product. The required scalar exponential and
logarithm inequalities already exist in the corpus.

Reflection pairs also make `T_R(x)` positive real: every pair contributes
`|1+x^2 b|^2>0`, and a fixed factor is positive real. Pass along finite
sets closed under reflection. Therefore the stronger signed statement is

```
0 <= 1-exp(-a*x^2)*T_R(x) <= B_R*x^4.
```

The upper bound follows from the lower exponential bracket and
`1-exp(-y)<=y`. This gives a global real-axis relative error polynomial in
`x`, dominated by the exact Gaussian. It pays real heat-integral error
terms without a cutoff loss. Complex coefficient-sign transfer and the
finite complementary block remain separate open work. The complete
production module is `RHTower/XiSliceGaussianTailRealBounds.lean`; its
scratch proof and all four capstone axiom audits passed.

Multiplying by the retained head gives, for the actual normalized Xi slice,
`|exp(-a*x^2) S_t(x)/S_t(0)-P_H(x)| <= |P_H(x)| B_R*x^4` on the whole real
axis. This exact source estimate retains all nearby zeros.

### C8. Actual-tail Gaussian heat comparison — paper proof

Let `R>=4`, `a=Re C_R(t)`, `lambda>0`, and `mu=1-2a*lambda>0`.
Define the literal variance-`lambda` heat integral
`F(x)=integral g_lambda(u) T_R(x+u) du`. C7 gives absolute integrability
and the exact one-sided estimate

```
0 <= mu^(-1/2)*exp(a*x^2/mu)-F(x)
 <= B_R*mu^(-1/2)*exp(a*x^2/mu)
      * [(x/mu)^4 + 6*(x/mu)^2*(lambda/mu) + 3*(lambda/mu)^2].
```

**Proof.** The tail is a measurable pointwise infinite product of continuous
factors and is positive real on the real axis. Its upper Gaussian majorant
is integrable by the completed-square identity from the model module.
Multiply `0<=exp(a*y^2)-T_R(y)<=B_R*y^4*exp(a*y^2)` by the positive heat
kernel and integrate. The upper integral is exactly the already proved
Gaussian model with offset zero. Completing the square identifies its
fourth moment with the displayed polynomial. No unproved cofactor-deviation
or dominated-convergence premise remains in this statement.

For the dense family and `lambda=kappa/a_u`, `0<kappa<1/2`, the normalized
heat integral tends to one, locally uniformly for real `x`: `mu=1-2kappa`
is fixed, `a_u->infinity`, and `B_u->0`. C6 even gives `B_u*a_u^2->0`.
This transfers the actual background through heat; it still does not
transfer the model's negative coefficient through the retained finite head.

**Status:** paper proof complete. Full Lean draft, including absolute
integrability, the explicit heat bound, and locally uniform normalized heat
convergence, is in `/tmp/wd_gaussian_tail_heat.lean`; not checked yet. Intended
production name: `RHTower/XiSliceGaussianTailHeat.lean`. This draft imports C6
and C7, authorizing their oleans when the dependencies are ready.

Direct leaf checks only; no umbrella build. Audit transitive axioms, wire the
completed modules, remove owned scratch files. No web, novelty audit, numerical
experiment, unproved analytic premise, or raised Lean limit.

### C9. Retain the central zero instead of dividing by it — paper proof

The normalized slice formula excludes `XiC(t)=0`. The corpus already has
the required stronger factorization mechanism in
`XiSliceClusterDetectionOrder`: splitting the canonical product outside a
finite set, the uniform genus-one pair identity, and the tail product limit
after removing every copy at the center. Reuse those results rather than
assuming nonvanishing of the whole slice.

For `H=H(t,R)`, `R>=0`, let `P` be the canonical product outside `H` and set

```
K = XiC(0)^2 P(t)^2 product_(q in H) exp(2t/z_q)/z_q^2,
Q(x) = K product_(q in H) [x^2+(z_q-t)^2].
```

All copies at `t` belong to `H`; therefore `P(t)!=0` and `K!=0`. The
uniform genus-one pair identity gives the finite polynomial factor, while
the existing complementary-product limit gives
`P(t-ix)P(t+ix)=P(t)^2 T_H(x)`. Thus `S_t(x)=Q(x)T_H(x)` for every complex
`x`, including centers where `XiC(t)=0`. Copies at the center contribute
their exact factors `x^2`; no divisor is discarded.

For `R>=4`, C7 now gives the unconditional full-source estimate

```
|exp(-C_H*x^2) S_t(x)-Q(x)| <= |Q(x)| B_H*x^4,   x real.
```

For complex `x` with `|x|<=R`, C3 gives the corresponding bound with
`|Q(x)|[exp(|x|^4 B_H)-1]`. Both follow by factoring the difference as
`Q(x)[exp(-C_H*x^2)T_H(x)-1]`.

**Audit:** BRIDGE. The finite factorization is already present inside a
corpus proof; the new connection removes the central nonvanishing premise
from the Gaussian comparison. It does not establish coefficient-sign transfer through the finite head
or claim new knowledge relative to external literature. Paper proof
complete; complete Lean draft saved in `/tmp/wd_gaussian_finite_head.lean`.
Frontier ledger must not be edited.

## Declaration map

All source paths below are under `formal/GaloisForLFunctions/RHTower/`.
C8 and C9 remain drafts until their pending kernel checks pass.

| Part | Module | Main declarations |
|---|---|---|
| C1 | `XiSliceGaussianTailComparison.lean` | `norm_xiSliceGaussianTail_sub_exp_le`, `xiSliceProduct_div_eq_gaussianHead_mul_tail`, `norm_xiSliceProduct_sub_gaussianHead_exp_le` |
| C2 | `XiSliceGaussianTailLimit.lean` | `tendstoUniformlyOn_xiSliceGaussianNormalizedTail`, `eventually_xiSliceGaussianTailFourth_normalized_le` |
| C3 | `XiSliceGaussianTailCompensation.lean` | `xiSliceGaussianTailQuadratic_eq_mass_sub_transverse`, `norm_xiSliceGaussianTail_compensated_sub_one_le` |
| C4 | `XiSliceGaussianTailHeightBounds.lean` | `xiSliceGaussianTailMass_le_log`, `xiSliceGaussianTailFourth_le_log`, `exists_xiSliceGaussianTailMass_height_lower` |
| C5 | `XiSliceGaussianTailWindowBounds.lean` | `xiSliceGaussianTailMass_le_window_bound`, `xiSliceGaussianTailMass_le_cutoff_bound` |
| C6 | `XiSliceDenseGaussianTail.lean` | `tendsto_xiSliceDenseGaussianCoefficient_atTop`, `tendsto_xiSliceDenseGaussianFourth_mul_coefficient_sq`, `tendstoUniformlyOn_xiSliceDenseGaussianTail_compensated`, `tendstoUniformlyOn_xiSliceDenseGaussianTail_dilated` |
| C7 | `XiSliceGaussianTailRealBounds.lean` | `xiSliceGaussianTail_real_eq_norm`, `norm_xiSliceGaussianTail_real_bounds`, `norm_xiSliceGaussianTail_real_compensated_sub_one_le`, `norm_xiSliceProduct_real_compensated_sub_head_le` |
| C8 | `XiSliceGaussianTailHeat.lean` | `DeBruijn.integrable_xiSliceGaussianTailHeat`, `DeBruijn.xiSliceGaussianTailHeat_bounds`, `DeBruijn.abs_xiSliceGaussianTailHeat_relative_error_le`, `DeBruijn.tendstoUniformlyOn_xiSliceDenseGaussianHeatNormalized` |
| C9 | `XiSliceGaussianFiniteHead.lean` | `xiSliceGaussianFiniteHeadScalar_ne_zero`, `xiSliceProduct_eq_gaussianFiniteHead_mul_tail`, `norm_xiSliceProduct_compensated_sub_finiteHead_le`, `norm_xiSliceProduct_real_compensated_sub_finiteHead_le` |

## Implementation checkpoint

Finishing the saved Lean work at the user's request. Do not edit the frontier
ledger. No broader RH result is claimed.

- C1: named final check and transitive axiom audits passed.
- C2: scratch proof, olean, and axiom audits passed; the interrupted named
  final check remains pending. Do not rebuild its existing olean.
- C3 and C4: named final checks, oleans, and capstone axiom audits passed.
- C5: complete scratch check, production olean, and axiom audits passed;
  named final check pending.
- C6 and C7: complete scratch checks and capstone axiom audits passed;
  production modules and umbrella imports exist. Their named final checks
  remain pending. C6, C7, and the Gaussian model olean builds passed;
  the C8 scratch proof is now undergoing its kernel and axiom checks.
- C8: complete paper proof and full draft in `/tmp/wd_gaussian_tail_heat.lean`.
  Integrability, the one-sided heat bound, and the explicit relative-error
  theorem passed their kernel and standard-three-axiom audits. The uniform
  convergence proof had one redundant terminal `rfl`; it was removed and
  the complete draft is being checked again.
- C9: complete paper proof and full draft in `/tmp/wd_gaussian_finite_head.lean`;
  kernel verification pending.
- The C1–C6 combined audit reported only `propext`, `Classical.choice`, and
  `Quot.sound` for all fifteen capstones; C7's four capstones have the same
  axiom set. No placeholders or raised proof limits occur in these modules
  or the C8/C9 drafts.
- All finished leaves are wired into `RHTower.lean`; no umbrella build.
  The Gaussian model itself is complete in the separate stage-3 card
  `wd-gaussian-background-heat-law.md`.
- Remove owned scratch files after production integration and final audits.
