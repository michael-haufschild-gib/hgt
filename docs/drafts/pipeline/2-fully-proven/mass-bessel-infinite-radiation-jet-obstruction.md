# Mass-Bessel infinite radiation-jet obstruction

**Stage:** 2 — fully proven on paper  
**Date frozen:** 2026-08-04  
**Label:** `[LOCAL-RESEARCH] [PAPER-PROVED] [NOVELTY UNVERIFIED]`

## 1. Exact theorem

Fix `a>0`, `\sigma>0`, and a nonnegative integer `m`.  Let `Q_{j,a}` be the
unique Poincare coefficient polynomials in

\[
 \frac{2atK_1(a\sqrt{t^2+x^2})}{\sqrt{t^2+x^2}}
 \sim \sqrt{2\pi a}\,e^{-at}t^{-1/2}
 \sum_{j\ge0}Q_{j,a}(x^2)t^{-j}
\]

as `|t|\to\infty` in a fixed closed subsector containing the positive
imaginary direction.

For the dyadic shell `X<n\le2X`, define its order-`m` radiation remainder

\[
 \begin{aligned}
 R_{m,X}(t):={}&
 \sum_{X<n\le2X}\frac{\Lambda(n)}{\sqrt n}B_a(t,\log n)\\
 &-\sqrt{2\pi a}\,e^{-at}t^{-1/2}
 \sum_{j=0}^{m-1}t^{-j}
 \sum_{X<n\le2X}\frac{\Lambda(n)}{\sqrt n}
 Q_{j,a}((\log n)^2),
 \end{aligned}
\]

where the second line is empty for `m=0`.  Put
`t_X=\sigma+i(\log X)^4`.  Then

\[
 R_{m,X}(t_X)
 =C_{a,\sigma,m}(X)\,
   \frac{\sqrt X}{(\log X)^{2m+2}},
\]

where `|C_{a,\sigma,m}(X)|` converges to a strictly positive constant.
Consequently

\[
 \lim_{X\to\infty}|R_{m,X}(t_X)|=+\infty
\]

for every finite `m`.

## 2. Coefficient classification

For every `j\ge0`,

\[
 \deg Q_{j,a}=j,
 \qquad [s^j]Q_{j,a}(s)=\frac{(-a/2)^j}{j!}.
\]

Indeed, put `s=x^2` and expand

\[
 \sqrt{t^2+s}
 =t+\frac{s}{2t}-\frac{s^2}{8t^3}+\cdots.
\]

At inverse order `t^{-j}`, the only contribution of `s`-degree `j` is the
`j`th power of `-as/(2t)` in
`\exp(-a(\sqrt{t^2+s}-t))`.  Every correction from `t/z`, `z^{-1/2}`, the
higher square-root terms, or the standard `K_1` coefficient series has smaller
`s`-degree at that order.  This proves the formula and nonvanishing.

## 3. Uniform shell asymptotic

Let `L=\log X`, `t=t_X`, and `x=\log n` for `X<n\le2X`.  Then `x=L+O(1)` and
`x^2/t=O(L^{-2})`.  The sectorial `K_1` expansion through order `m` and its
remainder are therefore uniform over the shell:

\[
 B_a(t,x)=\sqrt{2\pi a}\,e^{-at}t^{-1/2}
 \left(\sum_{j=0}^{m}Q_{j,a}(x^2)t^{-j}
 +O_m(L^{2m+2}|t|^{-m-1})\right).
\]

After subtracting the first `m` terms, the `j=m` contribution dominates the
uniform remainder by a factor tending to infinity.

The prime number theorem with partial summation gives

\[
 \sum_{X<n\le2X}\frac{\Lambda(n)}{\sqrt n}
 Q_{m,a}((\log n)^2)
 =\frac{(-a/2)^m}{m!}
 2(\sqrt2-1)\sqrt X L^{2m}(1+o(1)).
\]

Since `|t|^{-m-1/2}=L^{-4m-2}(1+o(1))`, the asserted scale is
`\sqrt X L^{-2m-2}` with a nonzero limiting coefficient.

## 4. Dependency ledger

- all-orders sectorial Poincare expansion and fixed-order remainder for `K_1`;
- analytic binomial expansion of the principal square root;
- coefficient-degree bookkeeping;
- PNT partial summation for a fixed logarithmic polynomial weight;
- positivity of the von Mangoldt coefficients on a dyadic shell.

No zero-free region beyond the classical prime number theorem and no RH input
enters.

## 5. Scientific content

Finite prime apertures do not fail because one leading divergence was left
unsubtracted.  Their failure has infinite asymptotic rank.  Each removed
radiation coefficient exposes a new nonzero logarithmic moment whose prime
mass defeats the next power of vertical-time decay.

Thus any completion built from finitely many moments, jets, Rees layers, or
local counterterms is excluded.  The exact open core, if solvable through this
representation, requires an infinite-jet singular quotient and a canonical
source-only summation on that quotient.

## 6. Hostile significance audit

Wrong interpretation: this theorem does not supply the summation functional
and does not improve a zero-free region.  It is a no-go classification.

Positive content: it gives a parameterized sharp lower law for every finite
renormalization order and unifies route-specific Bessel behavior with the
corpus's independent finite-Rees and regular-completion obstructions.

Exact-priority search found the parent `K_1` asymptotics but no collision with
the prime-shell theorem.  Scientific priority remains
`[NOVELTY UNVERIFIED]` pending specialist review.

## 7. Lean target

Formal proof must construct, not assume:

1. mass-carrier Fourier integral and its all-fixed-orders deep-time expansion;
2. coefficient polynomials with exact leading coefficient;
3. PNT partial summation for logarithmic polynomial weights;
4. dyadic lower bound for every `m`.

Status: `[PAPER-PROVED]`; Lean proof absent.

## Lean progress -- item 3, the arithmetic input at every order

`formal/GaloisForLFunctions/RHTower/DyadicVonMangoldtLogWeighted.lean` (new, umbrella-wired,
axiom-clean) proves the PNT partial summation with logarithmic polynomial weights that section 3
uses, for every order `m`.

| Card item | Declaration |
|---|---|
| the dyadic prime mass weighted by `n^{-1/2}` and `(log n)^{2m}` | `dyadicSqrtVonMangoldtLogMass` |
| on a dyadic shell the logarithm lies between `log X` and `log X + log 2` | `log_mem_dyadic` |
| hence the weighted mass is squeezed between the two shell endpoints times the unweighted mass | `dyadicSqrtVonMangoldtLogMass_bounds` |
| the shell distortion factor `((log X + log 2)/log X)^{2m}` tends to one | `tendsto_logShellRatio` |
| **`∑_{X<n<=2X} Λ(n) n^{-1/2} (log n)^{2m} ~ 2(√2 − 1) √X (log X)^{2m}`** | `tendsto_dyadicSqrtVonMangoldtLogMass` |

The `m = 0` case is the sibling card's `tendsto_dyadicSqrtVonMangoldtMass_div_sqrt`
(`dyadicSqrtVonMangoldtLogMass_zero` records the identification), so no partial summation is
redone: on a dyadic shell the logarithm is *constant to within `log 2`*, and a two-sided squeeze
transports the whole asymptotic to every logarithmic weight at once.  This is exactly the
statement that after subtracting `m` Poincaré terms the surviving prime mass still grows like
`√X (log X)^{2m}`, so no finite jet can absorb it.

### What remains

Items 1 and 2: the all-orders sectorial Poincaré expansion of `K_1` with a fixed-order remainder,
and the coefficient polynomials `Q_{j,a}` with `deg Q_{j,a} = j` and
`[s^j]Q_{j,a} = (-a/2)^j/j!`.  The corpus already owns the order-zero sectorial bound
`RHTower.norm_besselK1C_sub_leading_le_norm` (error in `|w|`, not `Re w`) and the integration-by-
parts engine `HTGeometry.BesselOrderAbsoluteAsymptotic` that produced it; the all-orders statement
is the same integration by parts iterated, with the coefficient bookkeeping of section 2.

## Lean progress -- the Watson layer of item 1

Two new modules (umbrella-wired, axiom-clean) supply the exact evaluation and the exact remainder
that the all-orders Schläfli expansion of `K_1` consumes.  The corpus already writes
`K_1(w) = 2e^{-w} ∫_0^∞ e^{-wv²} P(v) dv` with `P(v) = (1+v²)/√(2+v²)`
(`BesselOrderLaplaceAsymptotic.besselK1C_sub_leading`), so the all-orders expansion is Watson's
lemma applied to that profile.

`formal/GaloisForLFunctions/HTGeometry/GaussianHalfLineMoment.lean`:

| Card item | Declaration |
|---|---|
| the even half-line Gaussian moment with a *complex* parameter | `gaussianHalfMoment` |
| its integrability on the half line at every order | `integrableOn_pow_mul_cexp_neg_mul_sq` |
| a power times a Gaussian tends to zero | `tendsto_pow_mul_exp_neg_mul_sq`, `tendsto_pow_mul_cexp_neg_mul_sq` |
| the base case, from the complex Gaussian integral | `gaussianHalfMoment_zero` |
| **the recursion `M_{k+1} = ((2k+1)/2w) M_k`**, by one integration by parts | `gaussianHalfMoment_succ` |
| **the closed form**: every even moment is an explicit rational multiple of `(π/w)^{1/2}` | `gaussianHalfMoment_eq` |

Mathlib has the complex Gaussian integral (`integral_gaussian_complex_Ioi`) but not its moments, and
the corpus's `RHTower.integral_cpow_mul_exp_neg_mul_sq_Ioi` is restricted to a *real* parameter,
which the card's `t_X = σ + i(log X)^4` rules out.  The recursion avoids analytic continuation
entirely: `∫_0^∞ d/dv[v^{2k+1}e^{-wv²}] dv = 0` because both endpoint values vanish, and expanding
the derivative is the recursion.

`formal/GaloisForLFunctions/HTGeometry/WatsonGaussianRemainder.lean`:

| Card item | Declaration |
|---|---|
| the real Gaussian majorant at the real part of the parameter | `realGaussianHalfMoment`, `realGaussianHalfMoment_nonneg` |
| the polynomial part of a Watson expansion and its Gaussian transform | `watsonPoly`, `integral_watsonPoly_gauss` |
| **Watson's lemma with an explicit remainder**: a profile agreeing with `∑_{k<m} c_k v^{2k}` to within `C v^{2m}` has Gaussian transform agreeing with `∑_{k<m} c_k M_k(w)` to within `C · (m-th real moment at `Re w`)` | `norm_integral_sub_watson_le` |

The bound depends on the parameter only through its real part, so it is uniform along every ray in
the open right half plane -- which is what the card's fixed-order remainder needs at
`t_X = σ + i(log X)^4`.

## Lean progress -- the all-orders `K_1` asymptotic is closed

`formal/GaloisForLFunctions/HTGeometry/HalfShiftedBinomialRemainder.lean`:

| Card item | Declaration |
|---|---|
| the generalized binomial coefficient of `(1+s/2)^α`, and its absolute majorant | `binomCoeff`, `binomAbsCoeff`, `binomCoeff_succ`, `binomAbsCoeff_succ` |
| the Taylor remainder, its vanishing at the origin, and its derivative recursion | `binomRem`, `binomRem_zero_arg`, `hasDerivAt_binomRem` |
| **the remainder bound on the whole half line**, for every nonpositive exponent | `abs_binomRem_le` |
| at exponent `-1/2` the falling factorial is at most `m!`, so the bound is `(s/2)^m` | `binomAbsCoeff_neg_half_le`, `abs_binomRem_neg_half_le` |
| **the Schläfli profile in the squared variable**, and its Taylor coefficients | `besselLaplaceProfile_eq_shifted`, `schlafliCoeff`, `watsonPoly_schlafliCoeff` |
| **item 1's profile input**: `\|P(v) - ∑_{k<m+1} p_k v^{2k}\| ≤ 3·2^{-1/2}·2^{-(m+1)}·v^{2(m+1)}` | `abs_besselLaplaceProfile_sub_watsonPoly_le` |

There is no radius-of-convergence restriction anywhere.  The `m`-th derivative of `(1+u/2)^α` is
`(∏_{j<m}(α-j)/2^m)(1+u/2)^{α-m}`, and for nonpositive exponents that last factor is at most one on
the whole half line, so one induction -- differentiate, integrate back, lower the exponent by one --
gives the remainder bound globally.  At `α = -1/2` the falling factorial `∏_{j<m}(1/2+j)` is at most
`m!`, which is exactly the constant that cancels the `1/m!`.

`formal/GaloisForLFunctions/HTGeometry/BesselK1AllOrderAsymptotic.lean` and
`formal/GaloisForLFunctions/HTGeometry/BesselK1PoincareForm.lean`:

| Card item | Declaration |
|---|---|
| the Schläfli integral as an exact Gaussian transform of the profile | `besselK1C_eq_gauss` |
| **the all-orders sectorial expansion with a fixed-order remainder** | `norm_besselK1C_sub_watson_le` |
| every even Gaussian moment is a rational multiple of `w^{-k}` times `(π/w)^{1/2}` | `gaussianMomentFactor`, `gaussianHalfMoment_eq_pow` |
| **the classical Poincaré form**: `K_1(w) = e^{-w}(π/w)^{1/2}∑_{k<m+1} q_k w^{-k} + O(...)` | `besselK1Coeff`, `norm_besselK1C_sub_poincare_le` |

The remainder is `2e^{-Re w}·(3·2^{-1/2}/2^{m+1})·(the (m+1)-st real Gaussian moment at `Re w`)`, so
it depends on the argument only through its real part and is uniform along every ray in the open
right half plane -- which is the card's "fixed closed subsector" clause.

## Lean progress -- the complex binomial layer of the composition

`formal/GaloisForLFunctions/HTGeometry/ComplexBinomialRemainder.lean` (new, umbrella-wired,
axiom-clean) repeats the half-line remainder bound for a *complex* argument, which is what the
composition `z = t(1+x²/t²)^{1/2}` needs, since `x²/t²` is complex.

| Card item | Declaration |
|---|---|
| the generalized binomial coefficient at a real exponent, and its absolute majorant | `cbinomCoeff`, `cbinomAbsCoeff`, `cbinomCoeff_succ`, `cbinomAbsCoeff_succ` |
| the remainder, its vanishing at the origin, its derivative recursion, and its continuity | `cbinomRem`, `cbinomRem_zero_arg`, `hasDerivAt_cbinomRem`, `continuousAt_cbinomRem` |
| the disc of radius one half lies in the slit plane | `one_add_mem_slitPlane_of_norm_le_half` |
| the inductive step, isolated | `norm_cbinomRem_succ_le_of_pred` |
| **the remainder bound on `\|u\| <= 1/2` for every nonpositive exponent** | `norm_cbinomRem_le` |
| **the same at every positive order for every exponent at most one** -- which covers the square root `α = 1/2` | `norm_cbinomRem_succ_le` |

The bound is `(∏_{j<m}\|α-j\|/m!)·2^{m-α}·\|u\|^m`.  The proof is the half-line proof with the segment
`[0,u]` in place of `[0,s]`: the modulus of a complex power is the power of the modulus
(`Complex.norm_cpow_real`), on `\|u\| ≤ 1/2` the base stays in the slit plane with modulus at least
one half, and integrating the derivative along the segment lowers the exponent by one.  Isolating the
inductive step is what makes the exponent `1/2` free: its predecessor `-1/2` is already covered, so
one application of the step covers every positive order.

## Lean progress -- the expansion calculus and the shell factors

Four more modules (all umbrella-wired, axiom-clean) build the algebra the composition runs in.

`formal/GaloisForLFunctions/HTGeometry/DiscExpansionCalculus.lean` and
`DiscExpansionExponential.lean`:

| Card item | Declaration |
|---|---|
| `f` agrees with a polynomial to order `n` on a disc | `HasPolyExpansion` |
| sums and scalar multiples | `HasPolyExpansion.add`, `HasPolyExpansion.const_mul` |
| **the product rule, with no truncation** | `HasPolyExpansion.mul` |
| a function with an expansion is bounded on the disc | `HasPolyExpansion.norm_le` |
| truncation below degree `n`, on a disc of radius at most one | `truncBelow`, `polyAbsSum`, `norm_eval_sub_truncBelow_le`, `HasPolyExpansion.trunc` |
| **powers**, with a constant linear in the exponent | `HasPolyExpansion.pow` |
| **exponentials of expansions that vanish to first order** | `HasPolyExpansion.cexp` |

The product rule needs no truncation and no antidiagonal bookkeeping at all: the product of the two
polynomials is again a polynomial, and the decomposition `fg - PQ = (f-P)g + P(g-Q)` multiplies each
error by the other factor's bound.  Truncation is a separate step, taken once at the end, and costs
one further term of the same order because the discarded coefficients all carry at least `n` powers
of an argument of modulus at most one.

`formal/GaloisForLFunctions/HTGeometry/ShellBinomialExpansion.lean` and
`ShellRootDefectExpansion.lean`:

| Card item | Declaration |
|---|---|
| the truncated shell polynomial and its evaluation | `shellBinomPoly`, `eval_shellBinomPoly` |
| **`(1+x²w²)^α` as an expansion of order `2m` in `w`**, at every nonpositive exponent | `hasPolyExpansion_shellBinom` |
| the same at every positive order for exponents at most one -- in particular `α = 1/2` | `hasPolyExpansion_shellBinom_succ` |
| the shell polynomial has only even coefficients | `coeff_odd_shellBinomPoly` |
| **the root defect `(√(t²+x²) - t)` in the reciprocal parameter**, and its expansion | `shellDefect`, `shellDefectPoly`, `hasPolyExpansion_shellDefect` |

`α = 1/2` is exactly the exponent of the mass shell, and it is reached because the isolated inductive
step of the complex remainder only needs its *predecessor* `-1/2` to be nonpositive.  Dividing the
root defect by `w` is exact on the polynomial side (`Polynomial.divX`, legitimate because the shell
polynomial has no odd coefficients and constant term one), so the defect expansion has order one less
and vanishes at the origin -- which is precisely the hypothesis `HasPolyExpansion.cexp` consumes.

## Lean progress -- the branch identities and the exact carrier identity at every order

Three more modules (umbrella-wired, axiom-clean).

`formal/GaloisForLFunctions/HTGeometry/MassShellRootFactorization.lean`:

| Card item | Declaration |
|---|---|
| off the negative real axis the principal root is the unique square root with positive real part | `csqrt_eq_of_sq_of_re_pos_of_im_ne_zero` |
| **the shell root factors through the spectral parameter**: `√(t²+x²) = t·√(1+x²/t²)` | `massBesselRoot_eq_mul_csqrt` |

The card's spectral parameter `t_X = σ + i(log X)^4` makes `(t²+x²).re` very *negative*, so the
corpus's `csqrt_eq_of_sq_of_re_pos` does not apply; the uniqueness has to be run off the imaginary
part instead.  The side condition is `x² < t.re·‖t‖`, which is exactly what makes the second factor
close enough to one for the product to stay in the right half plane -- the principal root is
one-Lipschitz at the unit, so no argument bookkeeping is needed.

`formal/GaloisForLFunctions/HTGeometry/PrincipalRootMultiplicative.lean`:

| Card item | Declaration |
|---|---|
| on the right half plane the principal root's modulus is at most `√2` times its real part | `norm_csqrt_le_sqrt_two_mul_re` |
| **multiplicativity of the principal root at a factor near one** | `csqrt_mul_of_near_one` |

`norm_csqrt_le_sqrt_two_mul_re` is what replaces an argument estimate: squaring turns the difference
of the squared coordinates into the real part of the argument, so the imaginary part of the root is
strictly below its real part, and the whole quadrant condition becomes the single inequality
`√2·‖s-1‖ < 1`.

`formal/GaloisForLFunctions/HTGeometry/MassCarrierRatioIdentity.lean`:

| Card item | Declaration |
|---|---|
| the Poincaré polynomial and remainder of `K_1` at the shell argument | `shellPoincareSum`, `shellPoincareRemainder` |
| the distortion of the carrier against its deep-time profile, at order `n` | `carrierDistortion` |
| **the carrier at every order**, exactly | `massBesselCarrier_eq_distortion` |

This is the all-orders replacement for the corpus's order-zero `massBesselCarrier_eq`: the carrier is
its deep-time profile times `√2·(t/z)·(√t/√z)·e^{-a(z-t)}` times the Poincaré polynomial, plus the
carrier weight of the Poincaré remainder.  The identity is exact; only the last term is an error.

## Lean progress -- the distortion is now a product of expandable factors

Three more modules (umbrella-wired, axiom-clean).

`formal/GaloisForLFunctions/HTGeometry/MassCarrierDistortionFactors.lean`:

| Card item | Declaration |
|---|---|
| the shell quantity `1 + x²/t²`, its distance to one, and the positivity of its real part | `shellQuantity`, `norm_shellQuantity_sub_one`, `re_shellQuantity_pos` |
| **the distortion in shell factors**: `√2 · (√Q)⁻¹ · (√√Q)⁻¹ · e^{-a t(√Q - 1)} · Poincaré` | `carrierDistortion_eq_shellFactors` |

`formal/GaloisForLFunctions/HTGeometry/ShellPrincipalPowers.lean`:

| Card item | Declaration |
|---|---|
| a principal power with real exponent in `(0,1]` keeps the right half plane | `cpow_ofReal_re_pos` |
| the inverse root, the root of the root, and its inverse, as principal powers | `inv_csqrt_eq_cpow`, `csqrt_csqrt_eq_cpow`, `inv_csqrt_csqrt_eq_cpow` |
| every power of the root, and of its inverse, as a principal power | `csqrt_pow_eq_cpow`, `inv_csqrt_pow_eq_cpow` |

The quarter power is the only place a branch condition has to be checked, and it is checked once:
the argument of the shell quantity is below `π/2` in modulus, so a quarter of it is below `π/8` and
`Complex.cpow_mul` applies.  Every other identity is `Complex.cpow_add` or `Complex.cpow_neg`, which
need only nonvanishing.

`formal/GaloisForLFunctions/HTGeometry/MassCarrierShellPowers.lean`:

| Card item | Declaration |
|---|---|
| the shell quantity at the reciprocal parameter | `shellQuantity_eq_inv` |
| **the distortion as `√2 · Q^{-1/2} · Q^{-1/4} · e^{-a·shellDefect} · ∑_k q_k a^{-k} w^k Q^{-k/2}`** | `carrierDistortion_eq_shellPowers` |

with `Q = 1 + x²w²` and `w = 1/t`.  Every factor on the right now has its own expansion lemma:
`hasPolyExpansion_shellBinom` at the exponents `-1/2`, `-1/4` and `-k/2`,
`hasPolyExpansion_shellDefect` for the exponent of the exponential, and `HasPolyExpansion.cexp`,
`.mul`, `.add` for the assembly.

### What remains

Running the expansion calculus on that product -- supplying the disc bounds for each of the factors
-- to obtain a single `HasPolyExpansion` for `carrierDistortion`; item 2's coefficient bookkeeping
for `Q_{j,a}` (degree `j` in `x²` with leading coefficient `(-a/2)^j/j!`); and the dyadic assembly of
item 4.  The composition is where the remaining work sits: writing
`z = t(1+x²/t²)^{1/2}`, the carrier is `√(2πa)e^{-at}t^{-1/2}` times
`(t/z)^{3/2} e^{-a(z-t)} ∑_k q_k (az)^{-k}`, and every factor is a function of the *complex* variable
`u = x²/t²`, so the half-line binomial remainder above has to be repeated for complex argument along
the segment `[0,u]`.  The corpus already owns the order-zero case of exactly this composition
(`HTGeometry.massBesselCarrier`, `massBesselCarrier_eq`, `norm_massBesselCarrier_sub_leading_le`,
`norm_massBesselRoot_sub_le`), so the all-orders version is that estimate repeated at every order.

## Lean progress -- items 1 and 2 are closed

Five more modules (all umbrella-wired, axiom-clean) close the all-orders expansion of the carrier and
the classification of its coefficients.

`formal/GaloisForLFunctions/HTGeometry/BoundedDiscExpansion.lean`:

| Card item | Declaration |
|---|---|
| an expansion together with a bound for the function on the disc | `BddPolyExpansionAt` |
| sums, products, scalar multiples, finite sums, and lowering the order | `BddPolyExpansionAt.add`, `.mul`, `.const_mul`, `.finsetSum`, `.mono` |
| the truncating polynomial inherits the function's bound | `HasPolyExpansion.norm_poly_le` |
| truncation, and what it does to coefficients | `BddPolyExpansionAt.trunc`, `coeff_truncBelow_of_le`, `coeff_truncBelow_of_lt`, `eval_truncBelow` |
| exponentials, as a bounded expansion | `bddPolyExpansionAt_cexp` |

Carrying the bound alongside the approximant is what makes the assembly mechanical: the product rule
needs a bound for the second factor and for the first factor's polynomial, and the second follows
from the first.  The approximant itself stays explicit, which is what the coefficient classification
consumes.

`formal/GaloisForLFunctions/HTGeometry/ShellExpansionBounds.lean` and `ShellCarrierExpansion.lean`:

| Card item | Declaration |
|---|---|
| on the binomial disc the shell base stays above one half | `half_le_norm_one_add_shell` |
| hence a shell power with a nonpositive exponent is bounded by `2^{-α}` | `norm_shellPow_le` |
| the order-zero defect expansion has vanishing polynomial, so the defect is linear | `shellBinomPoly_one`, `shellDefectPoly_zero`, `shellDefectRate`, `norm_shellDefect_le` |
| the carrier distortion as a function of the reciprocal parameter | `shellCarrierProfile`, `carrierDistortion_eq_shellCarrierProfile` |
| each factor as a bounded expansion | `bddPolyExpansionAt_shellPow`, `bddPolyExpansionAt_monomial`, `bddPolyExpansionAt_defectExp` |
| the assembled approximant | `defectExpPoly`, `shellPoincarePoly`, `carrierProductPoly` |
| **item 1: the carrier distortion has an explicit approximant at every order** | `bddPolyExpansionAt_shellCarrierProfile`, `exists_poly_approx_carrierDistortion` |

The only genuine smallness condition in the whole assembly is on the exponential factor: the defect
must stay below one half so that its exponential series converges at the prescribed rate.  That is
the single hypothesis `a · shellDefectRate x · r <= 1/2`, and it is exactly the card's "fixed closed
subsector, `|t|` large" clause.

`formal/GaloisForLFunctions/HTGeometry/BivariateDiagonalSymbol.lean`:

| Card item | Declaration |
|---|---|
| the `j`-th outer coefficient has inner degree at most `j/c` | `SubDiag` |
| the extremal inner coefficient at each outer order | `diagSym` |
| stability under sums, products, powers, and lowering the weight | `SubDiag.add`, `.mul`, `.pow`, `.sum`, `.mono` |
| **on the weight-one class the extremal coefficients convolve** | `diagSym_mul` |
| **a weight-two factor contributes only at order zero** | `diagSym_eq_zero_of_subDiag_two`, `diagSym_mul_subDiag_two` |
| a factor concentrated in order one, raised to a power | `diagSym_pow_of_linear` |

This is the exact mechanism of section 2, made into an algebraic statement.  Everything except the
exponential loses at least one unit of shell degree per unit of inverse order -- weight two -- so it
can only act on the extremal coefficients through its value at order zero; the root defect keeps pace
exactly -- weight one -- and its first-order coefficient is `1/2`.

`formal/GaloisForLFunctions/HTGeometry/ShellCarrierSeries.lean`:

| Card item | Declaration |
|---|---|
| substituting `s = x²` into a bivariate polynomial | `shellEval`, `coeff_shellEval` |
| dividing off the outer variable commutes with a coefficient map | `map_divX` |
| the bivariate forms of every factor | `shellBinomSeries`, `shellDefectSeries`, `defectExpSeries`, `shellPoincareSeries`, `carrierProductSeries` |
| **the assembled approximant is the value of the bivariate series at `s = x²`** | `shellEval_carrierProductSeries` |

`formal/GaloisForLFunctions/HTGeometry/CarrierPoincareCoefficients.lean`:

| Card item | Declaration |
|---|---|
| the exact bicoefficient of the shell binomial series | `coeff_coeff_shellBinomSeries` |
| the shell powers and the Poincaré factor have weight two | `subDiag_two_shellBinomSeries`, `subDiag_two_shellPoincareSeries` |
| the root defect has weight one, and extremal symbol `1/2` in order one | `subDiag_one_shellDefectSeries`, `diagSym_shellDefectSeries` |
| **the exponential factor's extremal symbol is `(-a/2)^j / j!`** | `diagSym_defectExpSeries` |
| the leading Poincaré coefficient of `K_1` is `1/√2` | `besselK1Coeff_zero` |
| **the extremal shell coefficient of the whole carrier series** | `diagSym_carrierProductSeries` |
| the coefficient polynomials `Q_{j,a}` | `poincareCoeffPoly`, `coeff_carrierProductPoly` |
| **item 2: `deg Q_{j,a} = j` and `[s^j] Q_{j,a} = (-a/2)^j / j!`** | `natDegree_poincareCoeffPoly_le`, `coeff_poincareCoeffPoly_self`, `natDegree_poincareCoeffPoly` |
| **items 1 and 2 together** | `carrier_poincare_expansion` |

The normalization comes out on the nose: `√2 · q_0 = √2 · (√2)^{-1} = 1`, so `Q_{0,a} = 1` and the
extremal coefficient is exactly the card's `(-a/2)^j / j!`, nonzero for every `a ≠ 0`.

### What remains

Item 4's dyadic assembly.  Item 3 is already closed
(`RHTower.tendsto_dyadicSqrtVonMangoldtLogMass`), and items 1 and 2 are closed above.  The assembly
needs the order-`m` remainder uniformly over the shell `X < n <= 2X`, that is with the constant
tracked explicitly as a function of `x = log n` rather than left existential -- the shell constants
grow like `|x|^{2m}` and the radius is `|t_X|^{-1} ~ (log X)^{-4}`, so the product is the card's
`O_m(L^{2m+2}|t|^{-m-1})`.

## Lean progress -- the shell-uniform expansion, and what item 4 still needs

Three more modules (umbrella-wired, axiom-clean) make the order-`m` expansion uniform over a shell of
frequencies, which is the form section 3 consumes.

`formal/GaloisForLFunctions/HTGeometry/UniformDiscExpansion.lean`:

| Card item | Declaration |
|---|---|
| an expansion whose error constant and disc bound are both at most one scalar | `BddExpS` |
| raising the constant of an expansion | `HasPolyExpansion.weaken`, `BddExpS.weaken` |
| sums, products, scalars, finite sums, order lowering | `BddExpS.add`, `.mul`, `.const_mul`, `.finsetSum`, `.mono` |
| **the exponential, with the linear rate separated from the rest** | `bddExpS_cexp` |

Bounding the error constant and the disc bound by the same scalar turns each closure rule into an
explicit arithmetic operation -- a product costs a factor three -- so the constant of the whole
assembly is an explicit expression in the constants of the factors.  The exponential is the only rule
that keeps a second parameter, the linear rate `K`, and its constant is `2K^n` plus a term free of
`K`.  That is exactly the separation the shell needs.

`formal/GaloisForLFunctions/HTGeometry/ShellCarrierUniformExpansion.lean`:

| Card item | Declaration |
|---|---|
| the shell-power, monomial and root-defect factors with shell-free constants | `shellPowConst`, `bddExpS_shellPow`, `bddExpS_monomial`, `defectFactorConst`, `bddExpS_scaledDefect` |
| the exponential factor: `2(a·rate x)^m` plus a shell-free constant | `defectExpConst`, `bddExpS_defectExp` |
| the Poincaré factor | `poincareFactorConst`, `bddExpS_shellPoincare` |
| **the carrier profile with a shell-free constant times `1 + (a·rate x)^m`** | `carrierShellConst`, `bddExpS_shellCarrierProfile` |

Every constant is bounded independently of the frequency once `x²r` is bounded -- and `x²r` *is*
bounded, because `a·rate(x)·r <= 1/2` is precisely a bound on `a·cbinomAbsCoeff(1/2,1)·x²·r`.  The
one exception is the linear rate itself, whose `m`-th power is the card's `L^{2m}`.

`formal/GaloisForLFunctions/HTGeometry/ShellCarrierTruncationBound.lean`:

| Card item | Declaration |
|---|---|
| a polynomial of degree at most `j` against its coefficient mass | `norm_eval_le_of_natDegree_le` |
| truncation below degree `n`, with the tail weighted by the radius | `norm_eval_sub_truncBelow_le_upTo` |
| a shell-free degree bound and coefficient mass for the approximant | `carrierDegBound`, `poincareMassSum`, `natDegree_carrierProductPoly_lt` |
| the coefficients of the approximant, weighted, against the shell | `norm_coeff_carrierProductPoly_le` |
| **the profile against its genuine order-`m` partial sum, uniformly over the shell** | `carrierTruncConst`, `norm_shellCarrierProfile_sub_trunc_le` |

Passing from the assembled approximant to the card's partial sum `\sum_{j<m}` discards a tail, and
the tail is controlled by item 2: every discarded coefficient is a polynomial of degree at most its
own order in the squared frequency, so the tail carries the same `max(1,x²)^m` growth as the
expansion error, with a shell-free constant.

### What item 4 still needs

The distortion side is complete and uniform.  The open piece is the **sectorial** Poincaré remainder
for `K_1`.  The corpus's all-orders remainder
(`HTGeometry.norm_besselK1C_sub_poincare_le`) is bounded by the real Gaussian moment at `Re w`, so it
is uniform along every ray but does *not* decay along the imaginary direction.  At the card's
`t_X = σ + i(log X)^4` the shell root satisfies `Re(a z) ≈ aσ`, bounded, while `|a z| ≈ a(log X)^4`;
so that bound is a constant, and a constant times the dyadic prime mass `√X` dominates the card's
main term `√X (log X)^{-2m-2}`.  Item 4 therefore needs

  ‖K_1(w) − e^{-w}(π/w)^{1/2} Σ_{k<m} q_k w^{-k}‖ ≤ C_m e^{-Re w} |w|^{-1/2-m},

with the modulus, not the real part, in the decaying factor.  The corpus owns this at order zero
(`HTGeometry.norm_besselK1C_sub_leading_le_norm`, one integration by parts).

The route that avoids both an iterated integration by parts and a contour rotation:

1. the ray representation `K_1(z) = √2 e^{-z} z^{-1/2} ∫_0^∞ e^{-u} u^{1/2}(1 + u/(2z))^{1/2} du`,
   proved for *real* `z > 0` by the ordinary substitution `u = z v²` in the corpus's Gaussian form,
   and extended to the right half plane by the identity theorem, both sides being holomorphic there;
2. the binomial remainder for `(1+ζ)^{1/2}` on the *closed right half plane* rather than the disc of
   radius one half: on the segment `[0,ζ]` one has `Re(1+sζ) ≥ 1`, hence `|1+sζ| ≥ 1` and
   `|(1+sζ)^{1/2-m}| ≤ 1`, so the remainder is at most `|cbinomCoeff(1/2,m)|·|ζ|^m` with no radius
   restriction -- the corpus's `norm_cbinomRem_succ_le_of_pred` is the same induction with the
   sharper base;
3. `ζ = u/(2z)` has nonnegative real part exactly when `Re z ≥ 0`, and `|ζ|^m = u^m/(2|z|)^m`, so the
   remainder integrates against `e^{-u}u^{1/2+m}` and the modulus of `z` appears to the power `-m`.
