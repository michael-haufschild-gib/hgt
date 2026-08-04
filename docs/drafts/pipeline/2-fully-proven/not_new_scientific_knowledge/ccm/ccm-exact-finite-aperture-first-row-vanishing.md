# The exact CCM low radial first row vanishes at the leakage scale

- **ID:** `ccm-exact-finite-aperture-first-row-vanishing`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** Dunster's pole-uniform radial PSWF expansion, Bessel symbol asymptotics,
  one-dimensional stationary phase, and the exact logarithmic-aperture cutoff
- **Statement:** For the actual constrained degree-four radial mode, uniformly in the low radial
  range `2<=k<=lambda^2`,

  ```text
  |G_lambda(1,k)|/d_1(lambda)
    <= C*c^(-1/2)*k^(-2)+C*c^(-1)*k^(-1),
  c=2*pi*lambda^2.
  ```

  Consequently its logarithmically weighted first row is `o(d_1(lambda))`.

## Low radial range before asymptotics

The Lean theorem `logApertureDilationCorrelation_eq_zero` proves that a vector supported in
`[-log lambda,log lambda]` has zero correlation with the **prime shift** `log q` whenever
`q>lambda^2`. In the radial decomposition `k=q*n`, the multiplier `n` remains unbounded. The
present theorem controls the useful low radial subrange

```text
2<=k<=lambda^2=c/(2*pi).                                        (1)
```

This subrange is separated by a fixed factor from the endpoint-coalescing scale `k` of order `c`.
In particular, at the unique stationary point the first Bessel argument is at least a fixed
positive multiple of `c/k>=2*pi`; no uniform passage through `k/c=1` is required by the finite
operator.

## Actual fixed-degree Bessel phase

Put `s=sigma_4(c)^2`. Dunster's fixed-degree separation law gives

```text
s=9/c+O(c^(-2)).                                                 (2)
```

Thus `s->0`, but `c*s->9`: replacing the actual phase by the literal `s=0` phase loses a bounded
degree-four phase marking. Retain instead

```text
xi_s(x)=integral_1^x sqrt((t^2-s)/(t^2-1))dt,
A_s(x)=xi_s(x)^(1/2)/[(x^2-1)(x^2-s)]^(1/4).                    (3)
```

For `0<=s<=1/2` and `x>=1`, direct comparison of the integrands gives

```text
sqrt(1-s)*sqrt(x^2-1)<=xi_s(x)<=sqrt(x^2-1),
|A_s(x)|<=C*x^(-1/2).                                           (4)
```

After endpoint normalization, the leading part of the exact first-row Gram entry is a fixed
constant times

```text
L_(c,s)(k)=c*integral_1^infinity A_s(x)A_s(k*x)
  J_0(c*xi_s(x))J_0(c*xi_s(k*x))dx.                              (5)
```

## Exact stationary point

For the difference phase `phi_(s,k)(x)=xi_s(x)-xi_s(k*x)`, the stationary equation is

```text
sqrt((x^2-s)/(x^2-1))
 =k*sqrt((k^2*x^2-s)/(k^2*x^2-1)).                              (6)
```

Writing `y=x^2`, equation `(6)` reduces exactly to

```text
k^2*y^2-(k^2+1)*y+s=0.                                         (7)
```

The unique root with `y>1` is

```text
y_(s,k)=((k^2+1)+sqrt((k^2+1)^2-4*k^2*s))/(2*k^2),              (8)

y_(s,k)-1
 =2*(1-s)/(sqrt((k^2+1)^2-4*k^2*s)+k^2-1)
 asymptotic to k^(-2),                                         (9)
```

uniformly for `k>=2` and `0<=s<=1/2`. Differentiating `(3)` gives

```text
d/dx xi_s(r*x)
 =r*sqrt((r^2*x^2-s)/(r^2*x^2-1)),                              (10)
```

and a second differentiation at `(8)` yields

```text
|phi_(s,k)''(sqrt(y_(s,k)))| asymptotic to k^3.                 (11)
```

The implicit constants in `(9)` and `(11)` are absolute in the stated range.

## Uniform leading bound in the finite range

Split off the Bessel endpoint layer `x-1<=C*c^(-2)`. Its absolute contribution to `(5)` is

```text
O(c^(-3/2)*k^(-1))=O(c^(-1/2)*k^(-2)),                          (12)
```

because `k<=c/(2*pi)<c`.

On the complement, use the two Bessel symbol branches. At `(8)` their arguments have sizes
comparable to `c/k` and `c*k`. The product of the two Bessel symbols is `O(c^(-1))`,
`A_s(k*x)=O(k^(-1/2))`, and stationary phase with `(11)` supplies
`(c*k^3)^(-1/2)`. Including the prefactor `c` in `(5)` gives

```text
|L_(c,s)(k)|<=C*c^(-1/2)*k^(-2),
2<=k<=c/(2*pi).                                                  (13)
```

Outside a fixed relative neighbourhood of `(8)`, the difference-phase derivative is monotone
and bounded below by its distance from the critical point times a constant comparable to `k^3`.
One integration by parts on dyadic pieces gives `(13)`. The sum phase has no stationary point and
is smaller. The estimates in `(4)` and `s=O(c^(-1))` make all amplitude seminorms uniform.

## Dunster remainder is summable on the exact aperture

Dunster's pole-uniform formula is

```text
A_s(x)[J_0(c*xi_s(x))+O(c^(-1))*env J_0(c*xi_s(x))],             (14)
```

uniformly for `1<x<infinity`. The endpoint normalization changes `(14)` only by another uniform
factor `1+O(c^(-1))`.

Use `env J_0(u)<=C*(1+u)^(-1/2)`, `(4)`, and
`xi_s(k*x)>=sqrt(1-s)*sqrt(k^2*x^2-1)`. Then

```text
integral_1^infinity A_s(x)A_s(k*x)
  env J_0(c*xi_s(x))*env J_0(c*xi_s(k*x))dx
 <=C/(c*k).                                                      (15)
```

Indeed the second envelope and the two amplitudes contribute
`C*c^(-1/2)*k^(-1)*x^(-3/2)`, while splitting at `x=2` and using
`r=sqrt(x^2-1)` near the endpoint gives

```text
integral_1^infinity x^(-3/2)*(1+c*sqrt(x^2-1))^(-1/2)dx
 <=C*c^(-1/2).                                                   (16)
```

In the Gram product the prefactor `c` cancels the single `c^(-1)` from a cross remainder.
Equations `(15)`--`(16)` therefore give the exact-solution error

```text
|G_lambda(1,k)/d_1(lambda)-L_(c,s)(k)|<=C/(c*k).                 (17)
```

The product of two remainders is smaller. Combining `(13)` and `(17)` proves the stated bound.

## Arithmetic conclusion

The exact aperture and the elementary harmonic estimate give

```text
sum_(2<=k<=lambda^2) log(k)*|G_lambda(1,k)|/d_1(lambda)
 <=C*c^(-1/2)*sum_(k>=2)log(k)/k^2
   +C*c^(-1)*sum_(k<=lambda^2)log(k)/k
 =O(c^(-1/2))+O(log(c)^2/c)
 =o(1).                                                         (18)
```

Hence the complete exceptional first row vanishes cofinally at the leakage scale.

## Consequence and remaining gates

Together with the already proved exact nonstationary `j,k>=2` sector and the diagonal radial
leakage spectrum, `(18)` closes the low radial part of the exceptional first row. It does not close
the truncated-divisor weighted tail `k>lambda^2`; see
`ccm-prime-shift-radial-index-separation-law.md`. The Poisson center, archimedean form, and true
Weil even-gap lower bound remain later gates.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, especially the radial
  approximation `(3.6)` / summary formula `(6.5)` in the published numbering.
- NIST Digital Library of Mathematical Functions, Bessel envelopes and large-argument symbols.

## Lean status

**Partially formalized, 2026-08-04**, in
`formal/GaloisForLFunctions/RHTower/CCMFirstRowStationaryPhase.lean`.  Two of the card's proved gates
need no asymptotic input at all and are now unconditional.

**The exact stationary point, equations `(6)`–`(9)`:**

- **`stationary_equation_reduce`** — the reduction of `(6)` to `(7)`, as a *ring identity*:

  ```text
  (y-s)(k²y-1) - k²(k²y-s)(y-1) = (k²-1)(-(k²y²) + (k²+1)y - s).
  ```

  Displaying the factor `k² - 1` is the point: it shows that `k = 1` is the **only** excluded case, and
  that the reduction is exact rather than asymptotic.
- `stationaryDisc`, `stationaryRoot`, `stationaryDisc_nonneg`, `sq_le_sqrt_stationaryDisc`,
  `sqrt_stationaryDisc_le` — the discriminant, the root of `(8)`, and the two-sided discriminant
  bracket `k² <= sqrt(disc) <= k² + 1`.  Note that the lower bracket uses only `s <= 1/2` and the upper
  only `s >= 0`.
- **`stationaryRoot_isRoot`** — `(8)` is a root of `(7)`.
- **`stationaryRoot_sub_one`** — equation `(9)`, the exact rationalised form
  `y - 1 = 2(1-s)/(sqrt(disc) + k² - 1)`.
- **`stationaryRoot_sub_one_bounds`** — the card's `y - 1 ≍ k^{-2}`, with explicit absolute constants:
  `1/(2k²) <= y - 1 <= 2/k²` for `k >= 1`, `0 <= s <= 1/2`.

**The arithmetic conclusion, equation `(18)`:**

- `logLinTailSum`, `sum_logLin_div_sq_le`, **`weighted_firstRow_sum_le`** — given the pointwise
  two-term bound, the logarithmically weighted sum over the exact aperture satisfies

  ```text
  sum_(2<=k<=N) log k |G k| <= A * sum_k log k / k² + B * (log²N/2 + 1).
  ```

  Both arithmetic inputs were **already in the tree** and are reused rather than reproved:
  `HTGeometry.summable_logLin_div_sq` for the convergent weight and `RHTower.sum_log_div_le` for the
  harmonic weight.
- **`tendsto_firstRowBound_atTop`** — the `o(1)`: with `A = C c^{-1/2}` and `B = C/c` both terms vanish
  as the aperture grows, from `Real.tendsto_pow_log_div_mul_add_atTop` at exponent two.

Not formalized, because it genuinely imports external asymptotics rather than being derivable here:
Dunster's pole-uniform expansion `(14)`, the Bessel symbol branches and envelope bound, the
one-dimensional stationary-phase estimate behind `(13)`, the endpoint-layer split `(12)`, the envelope
integral `(15)`–`(16)`, and hence `(17)`.  Those supply exactly the *hypothesis* of
`weighted_firstRow_sum_le`; everything downstream of it is now unconditional.

The endpoint bracket `(4)` is now proved:

- `xiSpeed`, `xiCompSpeed`, `xiEndpointPhase` — the Liouville speed, the `s = 0` comparison speed and
  the endpoint-normalised phase.
- `sqrt_two_mul_sqrt_sub_one_le`, `xiCompSpeed_le`, `intervalIntegrable_rpow_sub_one`,
  `intervalIntegrable_xiCompSpeed`, `intervalIntegrable_xiSpeed` — the integrand is singular at the
  endpoint, so integrability is obtained by domination: `sqrt(t²-1) >= sqrt 2 sqrt(t-1)` gives
  `t/sqrt(t²-1) <= (x/sqrt 2)(t-1)^(-1/2)`, and `(t-1)^(-1/2)` is interval integrable because
  `-1/2 > -1`.
- **`integral_xiCompSpeed`** — the exact improper endpoint integral
  `int_1^x t/sqrt(t²-1) dt = sqrt(x²-1)`, from the one-sided fundamental theorem with antiderivative
  `sqrt(t²-1)`, continuous up to the endpoint and differentiable on the interior.
- `xiSpeed_le_xiCompSpeed`, `sqrt_one_sub_mul_xiCompSpeed_le` — the pointwise two-sided integrand
  comparison; the lower half is `(1-s)t² <= t²-s` for `t > 1`, which is where `s <= 1` enters.
- **`xiEndpointPhase_bounds`** — equation `(4)`:
  `sqrt(1-s) sqrt(x²-1) <= xi_s(x) <= sqrt(x²-1)` for `0 <= s <= 1` and `x >= 1`.  The Lean junk value
  of both integrands at the endpoint is `0`, so the closed-interval comparison needed by
  `integral_mono_on` holds there as well.

The amplitude half of `(4)`, the differentiation law `(10)` and the `k³` law `(11)` are now proved as
well:

- `xiAmplitude`, **`xiAmplitude_le`** — `A_s(x) <= 2^{1/4} x^{-1/2}` on `0 <= s <= 1/2`, `x > 1`.  Both
  inputs are exact: the phase bound `xi_s(x) <= sqrt(x²-1)` cancels the first factor of the fourth
  root, and `x² - s >= x²/2` converts the second.
- `continuousAt_xiSpeed`, `continuousOn_xiSpeed`, **`hasDerivAt_xiEndpointPhase`**,
  **`hasDerivAt_xiEndpointPhase_dilate`** — equation `(10)`.  The integrand is singular at the
  endpoint, so the interior derivative comes from the one-sided fundamental theorem at an interior
  point with the integrability of the bracket as input; the dilation is the chain rule.
- **`hasDerivAt_xiSpeed`** — the closed-form speed derivative
  `x(s-1) / [(x²-1)² xi_s'(x)]`, whose negative sign is what makes the difference phase concave.
- `xiDiffPhase`, `xiDiffSpeed`, `hasDerivAt_xiDiffPhase`, `hasDerivAt_xiDiffSpeed` — the difference
  phase and its first two derivatives.
- `stationaryPoint`, `one_lt_stationaryRoot`, `stationaryPoint_sq`, `one_lt_stationaryPoint`,
  **`stationaryRoot_mul_identity`**, `zero_lt_stationaryRoot_far` — the root equation in the form
  `(k² y - 1)(y - 1) = 1 - s`, which is what makes the far Bessel argument explicit.
- **`xiSpeed_stationaryPoint`**, **`xiSpeed_far_stationaryPoint`** — at the stationary point the two
  Liouville speeds collapse to the exact algebraic values `k x` and `x`.  This is an identity, not an
  estimate, and it is what reduces `(11)` to rational arithmetic.
- **`xiDiffSecond_stationaryPoint_eq`** — the resulting closed form
  `phi''(x) = (s-1)[1/(k (y-1)²) - k³ (y-1)²/(1-s)²]`.
- `stationaryRoot_sub_one_le_sharp` — the sharpened bound `y - 1 <= (8/7) k^{-2}` for `k >= 2`, from
  the discriminant bound `k² <= sqrt(disc)`.  The crude `2 k^{-2}` does not separate the two blocks of
  `phi''` at `k = 2`; this one does.
- **`abs_xiDiffSecond_stationaryPoint_bounds`** — equation `(11)` with absolute constants:
  `k³/20 <= |phi_(s,k)''(x_(s,k))| <= 4 k³` for `k >= 2`, `0 <= s <= 1/2`.

The Bessel envelope of `(14)`–`(15)` is also now a proved object of the tree, in
`formal/GaloisForLFunctions/RHTower/BesselJZeroEnvelope.lean`:

- `besselJ0` — Bessel's integral representation `J_0(u) = (1/pi) int_0^pi cos(u sin θ) dθ`.
- `abs_besselJ0_le_one`, `besselJ0_eq_two_div_pi_mul` — the trivial bound and the reflection
  `θ ↦ pi - θ` folding the representation onto a quarter period.
- `besselPhase` and its two derivatives, `integral_cos_eq_re_phase` — the phase objects and the
  passage to the complex oscillatory integral.
- `norm_integral_besselPhase_first`, `norm_integral_besselPhase_second` — the two van der Corput
  blocks: on `[0, pi/4]` the phase derivative `u cos θ` is bounded below and the first-derivative test
  gives `O(1/u)`; on `[pi/4, pi/2]` the second derivative `u sin θ` is bounded below and the
  second-derivative test gives `O(u^{-1/2})`.
- **`abs_besselJ0_le_envelope`**, `abs_besselJ0_le_min` — the envelope
  `|J_0(u)| <= 72 sqrt 2 / sqrt u` for `u >= 1`, so `|J_0| <= min(1, C u^{-1/2})`.  The exponent is the
  square-root loss of the single nondegenerate stationary point at `θ = pi/2`.  The corpus van der
  Corput layer (`RHTower.firstDerivTest`, `RHTower.secondDerivTest`) supplies both blocks; mathlib has
  no Bessel functions.

The envelope tail integral `(16)` is proved in
`formal/GaloisForLFunctions/RHTower/CCMFirstRowEnvelopeTail.lean`:

- `invPow32`, `hasDerivAt_negTwoDivSqrt`, `integrableOn_invPow32`, **`integral_Ioi_invPow32`** — the
  exact tail mass `int_a^infinity x^(-3/2) dx = 2 a^(-1/2)`, from the antiderivative `-2 x^(-1/2)`;
  integrability comes with the improper fundamental theorem rather than being assumed.
- `intervalIntegrable_rpow_sub_one_gen`, `rpow_neg_quarter`, **`integral_Ioc_rpow_sub_one`** — the
  exact endpoint mass `int_1^2 (x-1)^(-1/4) dx = 4/3`.
- `envelopeTail`, `envelopeTail_le_invPow32`, `integrableOn_envelopeTail` — the integrand and its
  domination by the pure power, which is what makes it integrable on the whole ray.
- `integral_Ioi_two_envelopeTail_le`, `integral_Ioc_envelopeTail_le` — the two blocks: `sqrt 2 c^(-1/2)`
  on `x >= 2` and `(4/3) c^(-1/2)` on `1 < x <= 2`, the latter through
  `sqrt(x²-1) >= sqrt(x-1)`.
- **`integral_Ioi_envelopeTail_le`** — equation `(16)` with an explicit constant:
  `int_1^infinity x^(-3/2)(1 + c sqrt(x²-1))^(-1/2) dx <= 3 c^(-1/2)` for `c >= 1`.

Equation `(15)` is now proved as well, in the same module:

- `envelopeProduct` — the majorant of the whole remainder layer: the two Liouville–Green amplitudes
  against the two Bessel envelopes `(1 + c xi)^{-1/2}`.
- `xiEndpointPhase_nonneg`, `continuousOn_xiEndpointPhase`, `continuousOn_xiAmplitude`,
  `continuousOn_envelopeProduct` — interior regularity, which is what makes the majorant measurable on
  the open ray; the phase is continuous because it is differentiable there.
- `sqrt_div_sqrt_two_le_xiEndpointPhase`, `half_mul_le_xiEndpointPhase_far` — the two phase lower
  bounds `xi_s(x) >= sqrt(x²-1)/sqrt 2` and `xi_s(u) >= u/2` for `u > 2`.  Both come from the bracket
  `(4)` after absorbing `sqrt(1-s)` into the radical.
- **`envelopeProduct_le`** — the pointwise majorant
  `envelopeProduct <= 2 (k sqrt c)^{-1} envelopeTail(c/sqrt 2)`: the two amplitudes and the far
  envelope contribute `2 c^{-1/2} k^{-1} x^{-3/2}`, and the near envelope is exactly the integrand of
  `(16)` at the rescaled aperture.
- `integrableOn_envelopeProduct`, **`integral_Ioi_envelopeProduct_le`** — equation `(15)` with an
  explicit constant: `int_1^infinity envelopeProduct <= 8/(c k)` for `k >= 2`, `c >= 2`,
  `0 <= s <= 1/2`.

The Bessel symbol input of `(13)`–`(14)` is now a proved object of the tree as well, in
`formal/GaloisForLFunctions/RHTower/BesselJZeroODE.lean` and
`formal/GaloisForLFunctions/RHTower/BesselJZeroPhase.lean`.  Neither the equation nor the asymptotic
exists in mathlib.

- `besselJ0Deriv`, `besselJ0SecondDeriv`, `hasDerivAt_besselJ0`, `hasDerivAt_besselJ0Deriv` —
  differentiation under the integral sign, with the constant `1` as dominating function.
- `integral_sin_mul_sin_eq` — the integration by parts `cos θ cos(u sin θ) = (1/u) d/dθ sin(u sin θ)`,
  whose boundary terms vanish.
- **`besselJ0_ode`** — Bessel's equation `J_0'' + J_0'/u + J_0 = 0`.  The integral representation is a
  genuine solution, so the whole Liouville–Green theory applies to it.
- `sinAmp`, `sinAmp_budget_le`, `besselJ0Deriv_eq_two_div_pi_mul`, `integral_sin_mul_sin_eq_neg_im`,
  `norm_integral_sinAmp_besselPhase_first`, `norm_integral_sinAmp_besselPhase_second`,
  **`abs_besselJ0Deriv_le_envelope`** — the derivative envelope `|J_0'(u)| <= 144 sqrt 2 / sqrt u`, by
  the same two-block van der Corput split with amplitude `sin θ`.
- `besselV`, `besselVDeriv`, **`hasDerivAt_besselVDeriv`** — the Liouville–Green normalisation
  `v = sqrt x J_0`, which satisfies the harmonic equation with the integrable perturbation
  `v'' = -(1 + 1/(4x²)) v`.
- `abs_besselV_le`, `abs_besselVDeriv_le` — `v` and `v'` are bounded, from the two envelopes.  This is
  what replaces a Grönwall argument.
- `invSq`, `integrableOn_invSq`, `integral_Ioi_invSq` — the exact tail `int_a^infinity t^(-2) = 1/a`.
- `besselW`, `besselWDeriv`, **`hasDerivAt_besselW`** — the rotating frame `w = (v + i v') e^{ix}`.
  The harmonic part cancels exactly and `w' = -i q v e^{ix}` with `q = 1/(4x²)`: the entire motion of
  the frame is the perturbation.
- `norm_besselWDeriv_le`, `integrableOn_besselWDeriv`, **`exists_besselW_limit`** — the frame has a
  limit, with the explicit tail bound `‖w(x) - L‖ <= 18 sqrt 2 / x`.
- **`exists_besselJ0_phase_asymptotic`** — the large-argument asymptotic
  `|sqrt x J_0(x) - (p cos x + q sin x)| <= 18 sqrt 2 / x`, i.e.
  `J_0(x) = A x^(-1/2) cos(x - delta) + O(x^(-3/2))` with `A = sqrt(p²+q²)`.  The constants are the
  real and imaginary parts of `L`; their values are deliberately not identified, since every estimate
  in `(13)` uses only their finiteness.

The three-region decomposition that `(13)` runs on is now proved, in
`formal/GaloisForLFunctions/RHTower/CCMFirstRowVanDerCorputBlocks.lean` (split off from the
stationary-phase module, which keeps the exact stationary point, the bracket `(4)`, the differentiation
laws `(10)` and the weighted first-row sum `(18)`):

- `xiSpeedDeriv_eq` — the speed derivative in root coordinates,
  `t(s-1)/[(t²-1)^{3/2}(t²-s)^{1/2}]`.  Both roots have polynomial squares, which is what turns every
  window estimate into a rational inequality.
- **`abs_xiDiffSecond_window_bounds`** — on the window `k^{-2}/4 <= x²-1 <= 2k^{-2}`, which contains the
  stationary point, `k³/16 <= |phi_(s,k)''(x)| <= 15 k³` for all `k >= 2`, `0 <= s <= 1/2`.  This is the
  uniform form of `(11)`; the mechanism is that the far block is smaller than the near one by `k^{-4}`,
  which after squaring is a polynomial comparison.
- `one_le_xiSpeed` — the dilated Liouville ratio never drops below `1`.
- **`xiDiffSpeed_ge_of_inner`** — below the window, `phi_(s,k)'(x) >= k/5`: the near speed is at
  least `1.41 k` there and the far speed at most `1.2 k`, so no cancellation is possible.  The signed
  form is what the first-derivative test needs; the absolute-value form is the second component.
- **`xiDiffSpeed_le_of_outer`** — above the window, `phi_(s,k)'(x) <= -k/8`: the far speed
  contributes at least `k` and the near speed at most `(7/8) k`.

Together these are exactly the hypotheses of a second-derivative test on the window and a
first-derivative test on each of the two complementary regions.

The leading Bessel term of `(13)` is now an unconditional estimate on the stationary window.  The key
structural discovery is that **the endpoint phases cancel**: the two Liouville–Green amplitudes
`A_s(x) A_s(k x)` multiplied by the two Bessel symbol prefactors `(c xi_s(x))^{-1/2}(c xi_s(k x))^{-1/2}`
leave the elementary algebraic fourth root

```text
c^(-1) * [(x²-1)(x²-s)(k²x²-1)(k²x²-s)]^(-1/4),
```

with no integral in it at all, and the prefactor `c` of `(5)` cancels the `c^{-1}`.

- `ampPoly`, `ampPolyDeriv`, `ampPoly_pos`, `ampPolyDeriv_pos`, `hasDerivAt_ampPoly` — the polynomial
  under the fourth root and its derivative, both positive on the ray.
- **`xiAmplitude_mul_eq`** — the cancellation identity itself.
- `ampFourthRoot`, `ampFourthRoot_pos`, **`ampFourthRoot_le`** — the amplitude and its bound
  `2 k^{-1/2}` from the window on.
- `ampFourthRootDeriv`, `hasDerivAt_ampFourthRoot`, **`ampFourthRootDeriv_nonpos`**,
  `continuousOn_ampFourthRootDeriv` — the amplitude is decreasing with a continuous derivative, which
  is exactly the weight hypothesis of the weighted van der Corput tests.
- **`xiDiffSecond_neg`** — the difference phase is strictly concave on the *whole* ray, for a
  structural reason: `sqrt(k²x²-1) > k sqrt(x²-1)` and `sqrt(k²x²-s) > sqrt(x²-s)`, so the far block
  loses to the factor `k³` outright.  No window is needed for the sign.
- `continuousOn_xiSpeedDeriv` — interior continuity of the second derivative.
- **`norm_integral_window_block_le`** — the window block of `(13)`:

  ```text
  ‖int_a^b amp(x) exp(-i c phi_(s,k)(x)) dx‖ <= 80 / (sqrt c * k²)
  ```

  for every subinterval of the stationary window, `k >= 2`, `c > 0`, `0 <= s <= 1/2`.  This is exactly
  the `O(c^{-1/2} k^{-2})` of `(13)`, with an explicit constant.  The estimate is the corpus weighted
  second-derivative van der Corput bound `RHTower.norm_integral_weight_cexp_secondDeriv`, whose
  right-hand side involves only the amplitude at the left endpoint — which is why the decreasing
  fourth root is all the amplitude regularity that is needed.

The two off-window blocks and the endpoint layer are now proved as well:

- **`norm_integral_outer_block_le`** — above the window,
  `‖int_a^b amp exp(-i c phi)‖ <= 64/(c k sqrt k)`, uniformly in the length of the block.  One
  integration by parts: the derivative is at most `-k/8` and the second derivative keeps a fixed sign,
  so the corpus weighted first-derivative test (`RHTower.norm_integral_weight_cexp_le`) applies.
- **`norm_integral_inner_block_le`** — below the window,
  `‖int_a^b amp exp(i c phi)‖ <= 20 amp(a)/(c k)`, from the nonincreasing-derivative companion
  (`RHTower.norm_integral_weight_cexp_le_anti`).  The amplitude at the left end is unbounded as the
  block reaches the endpoint, which is exactly why `(12)` is split off first.
- `continuousOn_ampFourthRoot`, **`ampFourthRoot_le_endpoint`** — the exact endpoint singularity
  `amp(x) <= 2^{1/4} k^{-1} (x-1)^{-1/4}`: the two far factors contribute `k^{-1}` and the near factor
  the fourth-root singularity.
- `integral_Ioc_rpow_sub_one_gen` — the exact mass `int_1^X (x-1)^{-1/4} dx = (4/3)(X-1)^{3/4}`.
- **`integral_Ioc_ampFourthRoot_le`** — equation `(12)`: the amplitude is integrable up to the endpoint
  and `int_1^X amp <= (4/3) 2^{1/4} k^{-1} (X-1)^{3/4}`.  At the Bessel endpoint scale `X - 1 = c^{-2}`
  this is `O(c^{-3/2} k^{-1})`, below the window contribution whenever `k <= c`.

All four blocks of `(13)` are therefore proved.  What remains is the bookkeeping that adds them: the
four-way split of the ray at the endpoint cut `1 + c^{-2}`, the two window edges
`x² - 1 = k^{-2}/4` and `x² - 1 = 2k^{-2}`, and the passage from the complex oscillatory integrals to
the real `cos`/`sin` ones.  With the aperture hypothesis `3k <= c` (implied by the card's
`k <= c/(2 pi)`) the endpoint cut does sit below the window, and the four constants add to
`O(c^{-1/2} k^{-2})`.

**Equation `(13)` is now assembled.**  In the same module:

- **`abs_integral_mul_cos_le_norm`** — the real cosine integral is dominated by the complex oscillatory
  integral, for *either* sign of the phase (`cos` is even).  This is what lets the three block
  estimates, each carrying the phase sign its van der Corput test demands, all bound the same real
  quantity.
- `continuousOn_xiDiffPhase`, `intervalIntegrable_ampCexp`, `integrableOn_ampFourthRoot` — the
  integrability bookkeeping: both factors are continuous on the open ray, and the amplitude is
  integrable up to the endpoint.
- **`abs_integral_firstRow_leading_le_of_cuts`** — the four-block assembly at arbitrary cut points: the
  split of `[1, R]` at the endpoint cut and the two window edges, bounded by the sum of the four block
  estimates with no arithmetic between them.
- `endpoint_cut_le`, `endpoint_term_le`, `inner_term_le`, `outer_term_le`, `four_terms_sum_le`,
  `sqrt_sqrt_two_le` — the numeric comparisons, isolated so each runs in a small context.
- **`abs_integral_firstRow_leading_le`** — equation `(13)`:

  ```text
  |int_1^R amp(x) cos(c phi_(s,k)(x)) dx| <= 170 / (sqrt c * k²)
  ```

  for every `R` beyond the stationary window, `k >= 2` and every aperture with `3k <= c` — which the
  card's range `k <= c/(2 pi)` implies.  The endpoint cut is `1 + c^{-2}` and the window edges are
  `x² - 1 = k^{-2}/4` and `x² - 1 = 2 k^{-2}`; the aperture hypothesis is exactly what puts the endpoint
  layer `O(c^{-3/2}k^{-1})` and the outer block `O(c^{-1}k^{-3/2})` below the two middle blocks, both of
  which are `O(c^{-1/2}k^{-2})`.

The first step of `(14)` is proved, in
`formal/GaloisForLFunctions/RHTower/CCMFirstRowDunsterModel.lean`.  Dunster's pole-uniform
approximation compares the radial prolate equation with a Bessel equation in the Liouville–Green
variable, and the comparison equation itself is an exact identity, not an asymptotic one:

- `lgBesselModel`, `lgBesselModelDeriv`, `lgBesselModelSecondDeriv`, `hasDerivAt_lgBesselModel`,
  `hasDerivAt_lgBesselModelDeriv` — the model `V(x) = J_0(c xi_s(x))` and its two derivatives.
- **`lgBesselModel_ode`** — the comparison equation, exactly:

  ```text
  V'' + (xi'/xi - xi''/xi') V' + c² (xi')² V = 0,     x > 1,
  ```

  for every `c > 0` and every admissible `s`.  The proof is the chain rule plus Bessel's equation: the
  `J_0'` term produced by the second derivative cancels against the first-order coefficient and the
  `J_0` terms cancel against `c²(xi')²`.  This is the equation the true radial equation is compared
  *with*; the two differ by a potential of size `O(1)` rather than `O(c²)`, which is the source of the
  relative error `O(c^{-1})` in `(14)`.

The exact skeleton of the comparison estimate is proved as well:

- `lgFirstOrderCoeff`, `lgWeight`, `xiSpeed_pos`, `xiEndpointPhase_pos`, **`hasDerivAt_lgWeight`** —
  the first-order coefficient `xi'/xi - xi''/xi'` and its exact integrating factor `m = xi/xi'`.
- **`hasDerivAt_weightedWronskian`** — the transport law: two solutions of the comparison equation whose
  potentials differ by `a - b` have weighted Wronskian with derivative exactly `m (a - b) U V`.  Every
  hypothesis is at a single point and the identity is exact.
- `hasDerivAt_lgBesselModelDeriv_ode` — the model as a solution with zero potential defect.
- **`hasDerivAt_lgBesselWronskian`** — the exact deviation law: for any solution `U` of the true equation
  the weighted Wronskian against the Bessel model has derivative `m a U V`, where `a` is the potential
  defect.  Integrating this *is* the Volterra equation of the pole-uniform expansion, and the `O(c^{-1})`
  of `(14)` is the size of that integral.
- **`hasDerivAt_lgWronskian_const`** — Abel's identity for the comparison equation, the normalisation the
  Green kernel is built from.

The second solution needed for the Green kernel is under construction in
`formal/GaloisForLFunctions/RHTower/BesselJZeroSecondSolution.lean`.  Rather than importing the
classical `Y_0` — whose definitions are a Frobenius series or a conditionally convergent integral — the
second solution is built from absolutely convergent data,

```text
K(u) = (pi/4) log u J_0(u) + M(u),      M(u) = int_0^(pi/2) cos(u cos θ) log(sin θ) dθ,
```

using that `log (sin θ)` is integrable (mathlib's `intervalIntegrable_log_sin`), so `M` is an honest
Bochner integral and differentiation under the integral sign applies with the dominating function
`|log (sin θ)|`:

- `besselJ0_cos_form`, `besselJ0Deriv_cos_form` — the cosine forms of `J_0` and `J_0'`, from the sine
  forms by the reflection `θ ↦ pi/2 - θ`.
- `besselM`, `besselMDeriv`, `besselMSecondDeriv`, `intervalIntegrable_besselMIntegrand`,
  **`hasDerivAt_besselM`**, **`hasDerivAt_besselMDeriv`** — the log-weighted integral and its two
  derivatives, both by differentiation under the integral sign.

The second solution is now complete:

- `besselMPrimitive`, `besselMPrimitiveDeriv`, `continuous_besselMPrimitive`,
  `hasDerivAt_besselMPrimitive`, `intervalIntegrable_besselMPrimitiveDeriv`,
  **`integral_besselMPrimitiveDeriv`** — the integration by parts, run as a one-sided fundamental
  theorem: the primitive `sin θ log (sin θ) · sin(u cos θ)` is continuous on the closed quarter period
  (because `x log x` is continuous, mathlib's `Real.continuous_mul_log`), differentiable on the open one,
  and vanishes at both ends — at `pi/2` because `log 1 = 0`, at `0` because `sin θ log (sin θ) → 0`.  So
  its derivative integrates to zero.
- `besselMSecondDeriv_add_besselM` — the `sin²`-weighted form of `M'' + M`.
- **`besselM_defect`** — the defect identity `u(M'' + M) + M' = -(pi/2) J_0'(u)`.
- `besselK`, `besselKDeriv`, `besselKSecondDeriv`, `hasDerivAt_besselK`, `hasDerivAt_besselKDeriv`,
  **`besselK_ode`** — Bessel's equation for the second solution, in the division-free self-adjoint form
  `u K'' + K' + u K = 0`.  The `log u` terms cancel through Bessel's equation for `J_0`, and the
  inhomogeneous defect cancels the `2 J_0'/u` produced by differentiating `log u · J_0` twice.

The Wronskian normalisation of the pair is proved too:

- `integral_abs_log_sin_quarter` — the exact mass `int_0^(pi/2) |log (sin θ)| = (pi/2) log 2`, from
  mathlib's `integral_log_sin_zero_pi_div_two` and `log (sin θ) <= 0` on the quarter period.
- `abs_besselM_le`, `abs_besselMDeriv_le` — both log-weighted integrals are bounded by `(pi/2) log 2`
  *uniformly in `u`*.
- `abs_besselJ0Deriv_le_one`, **`one_sub_sq_div_two_le_besselJ0`** — the elementary bounds
  `|J_0'| <= 1` and `J_0(u) >= 1 - u²/2` (the latter from `1 - x²/2 <= cos x` under the integral).
- `besselWronskian`, **`besselWronskian_eq`** — the log terms cancel:
  `u(J_0 K' - J_0' K) = (pi/4) J_0² + u(J_0 M' - J_0' M)`.
- `besselJ0_ode_cleared`, **`hasDerivAt_besselWronskian`** — Abel's identity: the weighted Wronskian has
  zero derivative, by `linear_combination J_0 · (K-ode) - K · (J_0-ode)`.
- `besselWronskian_const`, **`besselWronskian_pos`**, `besselWronskian_ne_zero` — it is a *positive*
  constant.  Evaluated at `u = 1/10` the `(pi/4) J_0²` term is at least `(3/4)(199/200)²` while the
  remainder is at most `2 (1/10)(pi/2) log 2 <= 0.278`, so the constant is positive; constancy then
  transports that to the whole ray.  No numerical evaluation of `J_0` is used — only `J_0 >= 1 - u²/2`,
  `pi > 3`, `pi <= 4` and `log 2 < 0.6931471808`.

The envelope of the second solution is proved too, and with it `K` is a complete admissible partner of
`J_0`:

- **`sq_add_sq_le_of_perturbed_harmonic`** — the energy law: if `v'' = -(1 + 1/(4x²)) v` on `x >= 1` then
  `v² + v'² <= (v(1)² + v'(1)²) exp(1/2)`.  The mechanism is exact rather than Grönwall: the weighted
  energy `(v² + v'²) exp(1/(2x) - 1/2)` has derivative `-2q E (v v' + v² + v'²) <= 0`, because
  `v v' + v² + v'² = (v + v'/2)² + (3/4) v'²`.  mathlib's Grönwall lemma is not usable here — it needs a
  *constant* coefficient, and `q = 1/(4x²)` used as the constant `1/4` would give an exponentially
  growing bound.
- `besselKV`, `besselKVDeriv`, `hasDerivAt_besselKV`, **`hasDerivAt_besselKVDeriv`** — the
  Liouville–Green normalisation `sqrt x K(x)`, which satisfies exactly the perturbed harmonic equation.
- **`exists_besselK_envelope`** — `|K(u)| <= C u^{-1/2}` for `u >= 1`, with
  `C = sqrt((K_V(1)² + K_V'(1)²) exp(1/2))`.  No asymptotic information about `K` is used.

So the pair `(J_0, K)` now has, unconditionally: the two ODEs, matching `u^{-1/2}` envelopes, and a
nonzero constant weighted Wronskian.

The Green kernel of Dunster's comparison is assembled from it in
`CCMFirstRowDunsterModel.lean`:

- `lgBesselModel2`, `lgBesselModel2Deriv`, `lgBesselModel2SecondDeriv`,
  `hasDerivAt_lgBesselModel2`, `hasDerivAt_lgBesselModel2Deriv`, **`lgBesselModel2_ode`**,
  `hasDerivAt_lgBesselModel2Deriv_ode` — the second model solution `K(c xi_s(x))` solves the *same*
  comparison equation, by the identical chain-rule cancellation.
- **`lgWronskian_model_eq`** — the Green kernel normalisation is exactly the Bessel Wronskian constant:
  `m (V1 V2' - V1' V2) = W(c xi_s(x))`.  The Liouville weight `xi/xi'` cancels the Jacobian `c xi'` of
  the substitution against the `1/(c xi)` of Abel's identity for Bessel.
- `lgWronskian_model_pos` — hence it is positive, uniformly in `x`.
- **`lgReconstruction`**, `lgReconstruction_eq` — the reconstruction identity
  `U · [m (V1 V2' - V1' V2)] = F2 V1 - F1 V2` with `F_i = m (U V_i' - U' V_i)`: a solution of the
  perturbed equation is recovered *algebraically* from its two weighted Wronskians against the model
  pair.  No integral and no hypothesis on the defect enter.  Together with the transport law
  `F_i' = m a U V_i` this is the Volterra equation of the pole-uniform expansion.

The Volterra equation is now available in integral form:

- **`hasDerivAt_lgBessel2Wronskian`** — the transport law against the second model solution.
- **`integral_lgBesselWronskian`**, **`integral_lgBessel2Wronskian`** — integrating the two transport
  laws: each weighted Wronskian moves exactly by `int m a U V_i`.  The defect enters *only* through that
  integral.
- **`abs_lgBesselWronskian_deviation_le`** — the deviation inequality
  `|F1(B) - F1(A)| <= int |m a U V1|`, which is the inequality the pole-uniform `O(c^{-1})` is read off
  from once the two envelopes and the size of `a` are inserted.

The Grönwall step the quantitative estimate needs is now built as general infrastructure, in
`formal/GaloisForLFunctions/HTGeometry/IntegralGronwall.lean`:

- **`le_mul_exp_integral_of_le_add_integral`** — Grönwall's inequality in *integral* form with a
  *variable* coefficient: `S x <= C + int_A^x k S` with `k >= 0` continuous gives
  `S x <= C exp(int_A^x k)`.  mathlib has only the differential form with a **constant** coefficient
  (`norm_le_gronwallBound_of_norm_deriv_right_le`), which is useless for an error analysis: replacing a
  decaying `k` by its supremum turns an integrable perturbation into an exponentially growing bound.
  The proof is exact rather than iterative — the primitive `R x = C + int_A^x k S` satisfies
  `R' = k S <= k R`, so `R exp(-int_A^x k)` is antitone with value `C` at `A`.
- `le_mul_exp_of_le_add_integral_of_mass_le` — the uniform form: if the total mass of `k` is at most `M`,
  the bound `C exp M` holds independently of the length of the interval.  This is the form the
  pole-uniform estimate consumes, since the Liouville defect has finite total mass.

- **`abs_le_envelope_mul_exp_of_two_wronskian`** — the abstract error analysis of a comparison expansion,
  assembled from the Grönwall lemma: given the algebraic reconstruction of the solution from its two
  Wronskians against the model pair (divided by the Green kernel constant `W`), a common envelope `E` for
  the two model solutions, and the two integrated transport laws, the solution obeys

  ```text
  |U x| <= (E x / W) (|F1 A| + |F2 A|) exp(int_A^x 2 kappa E² / W).
  ```

  The exponential is `1 + O(mass)` when the defect mass is small, and that is exactly where the relative
  `O(c^{-1})` of a pole-uniform expansion comes from.  Every hypothesis of this theorem is supplied by
  the objects already built: `lgReconstruction` gives the reconstruction, `abs_besselJ0_le_envelope` and
  `exists_besselK_envelope` the common envelope, `lgWronskian_model_pos` the constant `W`, and
  `integral_lgBesselWronskian` / `integral_lgBessel2Wronskian` the transport laws.

The interval-level inputs of that instantiation are now proved in the Dunster module:

- **`xiEndpointPhase_le_of_le`** — the endpoint phase is nondecreasing (its increment is the integral of
  the nonnegative speed), so the Bessel argument `c xi_s(x)` only grows along the ray.  This is what lets
  the Green kernel constant be evaluated once, at the left endpoint, and what propagates the condition
  `c xi >= 1` from that endpoint to the whole interval.
- **`abs_lgBesselModel_le`** — the first model solution inherits the Bessel envelope
  `72 sqrt 2 / sqrt(c xi_s(x))`.
- **`exists_lgBesselModel2_envelope`**, **`exists_lgBesselModel_common_envelope`** — the second model
  solution inherits the envelope of `K`, with a constant independent of every parameter, and the pair has
  a common envelope `C / sqrt(c xi_s(x))`.

Three of the four hypotheses of the abstract error analysis are now discharged in the Dunster module:

- `continuousOn_lgWeight`, `continuousOn_lgBesselModel`, `continuousOn_lgBesselModelDeriv`,
  `continuousOn_lgBesselModel2`, `continuousOn_lgBesselModel2Deriv`, `continuousOn_xiEndpointPhase'` —
  interior continuity of every model object, each from its own `HasDerivAt`.
- **`besselWronskian_phase_eq`**, `besselWronskian_phase_pos` — the Green kernel constant may be
  evaluated once at the left endpoint: the Bessel argument only grows along the ray, so Abel's identity
  applies in the single direction the constancy lemma needs.
- **`lgReconstruction_const`** — the reconstruction with that single constant
  `W = besselWronskian (c xi_s(A))`.
- **`abs_perturbed_le_envelope_mul_wronskianSum`** — the pointwise bound
  `|U x| W <= E x (|F1 x| + |F2 x|)`, which is the inequality that closes the Volterra loop: it is what
  turns the transport laws into an integral inequality for `|F1| + |F2|` alone.

**The pole-uniform comparison theorem is proved.**
**`abs_perturbed_le_lgEnvelope_mul_exp`**: let `U` solve the comparison equation perturbed by a defect
`a` on `[A, B] ⊂ (1, ∞)`, with `c xi_s(A) >= 1`.  Then

```text
|U x| <= (C / sqrt(c xi_s(x))) / W · S(A) · exp(int_A^x 2 m |a| E² / W),
```

with `W = besselWronskian (c xi_s(A))` the Green kernel constant, `S(A)` the total Wronskian size at the
left endpoint and `E = C / sqrt(c xi_s(·))` the common envelope of the model pair.  The exponential is
`1 + O(mass)` for small defect mass: that factor *is* the relative error of the pole-uniform expansion,
and with the Liouville defect of the radial prolate equation it is `1 + O(c^{-1})`.

The proof composes, with nothing left over: the two model ODEs, their common `u^{-1/2}` envelope, the
positive constant Green kernel normalisation, the two transport laws in integral form, the algebraic
reconstruction, and the variable-coefficient Grönwall inequality.  So the pole-uniform *mechanism* of
`(14)` is now unconditional in the corpus, for an arbitrary perturbation of the comparison equation.

The route to the last input is prepared as well.  Writing a concrete equation `u'' + Q u = 0` in the
comparison form produces the defect `a = Q + P²/4 + P'/2 - c²(xi')²`, so identifying it needs one more
derivative of the phase.  Both differentiations are now proved:

- **`xiSpeedSecondDeriv`**, `hasDerivAt_xiSpeedDeriv` — the third derivative of the endpoint phase, in
  closed form.
- **`lgFirstOrderCoeffDeriv`**, `hasDerivAt_lgFirstOrderCoeff` — the derivative `P'` of the first-order
  coefficient of the comparison equation.
- `lgNormalFormDefect` — the defect itself, recorded as a definition of the four explicit terms.

The endpoint asymptotics of the phase that the cancellation needs are now available as general
infrastructure, in `formal/GaloisForLFunctions/HTGeometry/ArcoshComparison.lean`:

- `endpointLog`, **`hasDerivAt_endpointLog`**, `continuousOn_endpointLog` — the antiderivative of
  `1/sqrt(x²-1)` on the ray, namely `log(x + sqrt(x²-1))`.  mathlib has `Real.arcosh` but no derivative
  for it, so the antiderivative is built directly.
- **`endpointLog_le_sqrt`**, **`sqrt_mul_one_sub_le_endpointLog`** — the two-sided comparison
  `sqrt(x²-1)(1 - (x²-1)/6) <= log(x + sqrt(x²-1)) <= sqrt(x²-1)`.  Both are proved the same way: the
  difference vanishes at the endpoint and its derivative has a fixed sign, the sign reducing to the
  elementary inequality `x(x+1) >= 2`.  This is what makes `log(x + sqrt(x²-1))` and `sqrt(x²-1)`
  interchangeable to relative order `x²-1`, which is the accuracy the singular-term cancellation needs.

The phase is now bracketed by the endpoint logarithm to that accuracy, in the stationary-phase module:

- **`xiSpeed_eq_factored`** — the exact factorisation
  `sqrt((t²-s)/(t²-1)) = sqrt(1-s) (t²-1)^(-1/2) sqrt(1 + (t²-1)/(1-s))`.
- `intervalIntegrable_invSqrtSqSubOne`, **`integral_invSqrtSqSubOne`** — the endpoint logarithm is the
  exact primitive of `(t²-1)^{-1/2}` from the endpoint, the integrand being singular but integrable.
- **`sqrt_one_sub_mul_endpointLog_le_xiEndpointPhase`**,
  **`xiEndpointPhase_le_sqrt_one_sub_mul_endpointLog`** — the two-sided bracket

  ```text
  sqrt(1-s) L(x)  <=  xi_s(x)  <=  sqrt(1-s) sqrt(1 + (x²-1)/(1-s)) L(x),   L = endpointLog,
  ```

  whose correction factor is `1 + O(x²-1)`.  Combined with the `arcosh`-vs-`sqrt` comparison this gives
  `xi_s(x) = sqrt(1-s) sqrt(x²-1) (1 + O(x²-1))`, which is exactly the accuracy at which the two
  singular terms of the defect cancel.

For the radial prolate equation of order zero,
`(x²-1) R'' + 2x R' - (chi - c²x²) R = 0`, the substitution `u = sqrt(x²-1) R` gives the normal form
`u'' + Q u = 0` with `Q = c²(x²-s)/(x²-1) + 1/(x²-1)²` and `s = chi/c²`.  The pole-uniform property is
therefore a statement about `a = 1/(x²-1)² + P²/4 + P'/2`, and the formalisation settles exactly what that
statement is.  **The double pole cancels but a simple pole survives.**  Writing `g = sqrt(xi/xi')` one has
`P²/4 + P'/2 = g''/g` and `g = sqrt(x²-1) A_s(x)`, and `(sqrt(x²-1))''/sqrt(x²-1) = -1/(x²-1)²`
identically, so the `1/(x²-1)²` cancels *exactly*; what is left is
`2 (r'/r)(A_s'/A_s) + A_s''/A_s` with `r = sqrt(x²-1)`, which has a simple pole because `A_s(1) = 1` with
`A_s'` of size `O(1)`.  In closed form

```text
a = [-(x⁴) + (8s-3) x² - 2 s(s+1)] / [4 (x²-s)² (x²-1)]
      - x Δ/(2(x²-1)) - Δ²/4,        Δ = xi'/xi - x/(x²-1),
```

and at `s = 0`, where `xi_0 = sqrt(x²-1)` and `Δ = 0`, this is exactly
`a = -(x²+3)/(4 x² (x²-1)) = -1/(x²-1) + 3/(4x²)`.  So the reading "the two singular pieces cancel and `a`
stays bounded" is too strong: only the second-order pieces cancel.  That is enough, and it is what the
Volterra estimate needs — the deviation integral carries the Liouville measure `dx/xi'`, which vanishes
like `sqrt(x²-1)` at the endpoint, so `|a| <= C/(x²-1)` has finite total mass while `1/(x²-1)²` would not.
That the surviving pole is simple rather than double is precisely the reason the comparison is with `J_0`
rather than with a trigonometric function.

The PSWF-specific input of `(14)` is now formalized too, and it needs no asymptotics of the eigenvalue:
the defect is independent of the aperture `c` (it cancels identically) and the separation law `(2)` enters
only through the range `0 <= s <= 1/2`.  What remains of `(14)` is the estimate on the deviation integral,
i.e. the total Liouville mass of `a`.

**Why the Bessel comparison cannot be replaced by a harmonic one.**  It is tempting to avoid the second
Bessel solution by comparing with the harmonic oscillator instead, using the corpus interaction picture
for `W'' + c² W = psi W` (`RHTower.radialInteractionPlus/Minus`) and converting back with the phase
asymptotic `exists_besselJ0_phase_asymptotic`.  That fails at the required scale: the WKB error control
function for this Liouville datum is `(1/c) int |q^(-1/4) (q^(-1/4))''|` with `q = (xi')² ~ (x-1)^(-1)`,
whose integrand is `~ (x-1)^(-3/2)`, so the error accumulated from `x - 1 = delta` on is
`~ 1/(c sqrt delta)`.  At the endpoint scale `delta = c^(-2)` that is `O(1)`, not `O(c^(-1))`.
Uniformity through the pole is exactly what the Bessel comparison buys, so the second Bessel solution is
genuinely needed.

Note: the same Liouville speed already exists in the tree as
`RHTower.radialPSWFExteriorSpeed sigma z` with `s = sigma²`, normalised at `z = 2` instead of the
endpoint; the endpoint normalisation is what the bracket `(4)` needs, so the two coexist.

**The last PSWF-specific input of `(14)` is proved**, in
`formal/GaloisForLFunctions/RHTower/CCMRadialProlateDefect.lean`.  Nothing about prolate spheroidal
spectral theory is imported: the theorem is about an arbitrary solution of the radial equation with
separation constant `chi = s c²` in the range the separation law `(2)` provides.

- `xiSpeed_sq_mul`, `radialProlateQ`, **`radialProlateQ_sub_comparison`** — the normal-form potential and
  the exact cancellation of the aperture: `Q - c²(xi')² = 1/(x²-1)²`, because `(xi')² = (x²-s)/(x²-1)`.
  The defect therefore does not depend on `c` at all.
- **`xiSpeedDeriv_div_xiSpeed_eq`**, **`xiSpeedSecondDeriv_div_xiSpeed_eq`** — the two logarithmic
  derivatives of the speed, `xi''/xi'` and the third-derivative ratio, in closed rational form.  Both are
  proved by substituting `x² - s = (x²-1)(xi')²` and clearing: after that substitution the identities are
  *free* of the square root, hence pure `field_simp`/`ring`.
- **`lgNormalFormDefect_radialProlate_eq`** — the defect in logarithmic-derivative form,
  `a = 1/(x²-1)² - (xi'/xi)²/4 + (3/4)(xi''/xi')² - (1/2) xi'''/xi'`.  The `c²` terms cancel identically.
- `prolateDefectAlg`, `phaseLogDefect`, **`lgNormalFormDefect_radialProlate_eq_alg`** — the defect with
  its double pole removed: the explicit rational function
  `(-(x⁴) + (8s-3)x² - 2s(s+1)) / (4 (x²-s)²(x²-1))` plus two terms carrying the bounded phase defect
  `Δ = xi'/xi - x/(x²-1)`.  The divisibility of the numerator by `x²-1` *is* the cancellation of the
  double pole, and it is displayed as a polynomial identity.
- **`abs_prolateDefectAlg_le`** — `|a_alg| <= 6/(x²-1)`, from `(x²-s)² >= x⁴/4`.
- `xiSpeed_mul_sub_one`, **`phaseLogDefect_eq`** — the phase defect as a single quotient
  `(sqrt(x²-s) sqrt(x²-1) - x xi)/(xi (x²-1))`.
- **`xiSpeed_div_xiEndpointPhase_le`**, **`abs_phaseLogDefect_le_far`** — away from the endpoint the
  defect is bounded by `x/(x²-1)`, because `xi' <= x/sqrt(x²-1)` and `xi >= sqrt(x²-1)/sqrt 2` bound the
  logarithmic derivative by `sqrt 2 x/(x²-1)` and it is positive.
- `near_defect_numeric`, **`abs_phaseLogDefect_le_near`** — near the endpoint `|Δ| <= 2`.  The mechanism
  is that the numerator is a difference of two quantities of the same size `sqrt(1-s) sqrt(x²-1)` whose
  leading terms cancel: `xi >= sqrt(1-s) L` with `L >= r(1 - r²/6)` bounds it above by
  `r[(sqrt(x²-s) - x sqrt(1-s)) + x sqrt(1-s) r²/6]`, and `sqrt(x²-s) - x sqrt(1-s)` is itself
  `O(x²-1)` because its product with `sqrt(x²-s) + x sqrt(1-s)` is exactly `s(x²-1)`; and
  `xi <= sqrt(x²-s) L` with `L <= r` bounds it below by `-sqrt(x²-s) r (x-1)`.  No sharp expansion of
  `xi` is needed, only the two brackets already in the tree.
- **`abs_lgNormalFormDefect_radialProlate_le`** — the pole-uniform bound `|a| <= 40/(x²-1)` for every `c`,
  every `0 <= s <= 1/2` and every `x > 1`.
- `nfWeight`, `nfWeightDeriv`, `nfWeightSecondDeriv`, `hasDerivAt_nfWeight`,
  `hasDerivAt_nfWeightDeriv`, `prolateNormalFormSol`, `prolateNormalFormSolDeriv`,
  `prolateNormalFormSolSecondDeriv`, `hasDerivAt_prolateNormalFormSol`,
  `hasDerivAt_prolateNormalFormSolDeriv`, **`prolate_normalForm_ode`** — the Liouville normal form: the
  whole expression `u'' + Q u` equals the radial equation divided by `sqrt(x²-1)`, so the transformation
  is an identity, not an approximation.
- `lgAmplitude`, `lgAmplitudeDeriv`, `lgAmplitudeSecondDeriv`, `lgWeight_pos`, `lgAmplitude_pos`,
  **`hasDerivAt_lgAmplitude`**, **`hasDerivAt_lgAmplitudeDeriv`** — the comparison amplitude
  `g = sqrt(xi/xi')` and its two derivatives `g' = gP/2`, `g'' = g(P²/4 + P'/2)`, from the
  integrating-factor law `m' = mP` already in the tree.
- `comparisonSol`, `comparisonSolDeriv`, `hasDerivAt_comparisonSol`,
  **`hasDerivAt_comparisonSolDeriv`** — dividing a solution of the normal form by `g` produces a solution
  of the comparison equation with defect exactly `lgNormalFormDefect`, in the very form
  `U'' = -P U' - (c²(xi')² + a) U` that the transport law and the Volterra estimate consume.
- **`radialProlate_comparison_pole_uniform`** — the gate: for any solution of
  `(x²-1) R'' + 2x R' - (s c² - c² x²) R = 0` at `x > 1` with `0 <= s <= 1/2`, the function
  `U = sqrt(x²-1) R / g` satisfies the comparison equation with a defect obeying `|a| <= 40/(x²-1)`,
  uniformly in `c`.

## Lean gates

- [x] Lean: exact reduction of the stationary equation to the quadratic `(7)`
- [x] Lean: the root `(8)` verified, and `(9)` in exact rationalised form
- [x] Lean: `y - 1 ≍ k^{-2}` with explicit absolute constants
- [x] Lean: weighted first-row sum bound `(18)` from the pointwise two-term bound
- [x] Lean: the `o(1)` conclusion of `(18)`
- [x] Lean: the `xi_s` two-sided bracket `(4)` (improper endpoint integral)
- [x] Lean: amplitude half of `(4)`, `|A_s(x)| <= 2^{1/4} x^{-1/2}`
- [x] Lean: the differentiation law `(10)` for the dilated phase
- [x] Lean: the exact speed collapse at the stationary point and the closed form of `phi''`
- [x] Lean: the `k³` law `(11)` with absolute constants
- [x] Lean: the Bessel envelope `|J_0(u)| <= C u^{-1/2}` (own module, van der Corput)
- [x] Lean: the envelope tail integral `(16)`, with the explicit constant `3`
- [x] Lean: the full envelope product bound `(15)`, with the explicit constant `8`
- [x] Lean: Bessel's equation for the integral representation
- [x] Lean: the derivative envelope `|J_0'(u)| <= C u^{-1/2}`
- [x] Lean: the large-argument phase asymptotic `J_0(x) = A x^{-1/2} cos(x - delta) + O(x^{-3/2})`
- [x] Lean: the uniform window bound `|phi''| ≍ k³` and the two off-window bounds `|phi'| ≳ k`
- [x] Lean: the exact amplitude of the leading term (endpoint phases cancel) and its monotonicity
- [x] Lean: strict concavity of the difference phase on the whole ray
- [x] Lean: the **window block** of `(13)`: `O(c^{-1/2} k^{-2})` with the constant `80`
- [x] Lean: the two off-window blocks of `(13)` (weighted first-derivative tests)
- [x] Lean: the endpoint layer `(12)`, with the exact `(x-1)^{-1/4}` singularity
- [x] Lean: the four-way assembly of `(13)`, with the explicit constant `170`
- [x] Lean: the exact pole-uniform **comparison equation** of `(14)`, solved by `J_0(c xi_s(x))`
- [x] Lean: the exact **deviation law** of `(14)` (weighted Wronskian transport, Abel identity)
- [x] Lean: a second solution of Bessel's equation, its envelope and the Wronskian normalisation
- [x] Lean: the Green kernel, the two transport laws and the algebraic reconstruction
- [x] Lean: variable-coefficient Grönwall (integral form) — new general infrastructure
- [x] Lean: **the pole-uniform comparison estimate** for an arbitrary perturbation of the comparison
  equation
- [x] Lean: the PSWF-specific input of `(14)` — the actual radial prolate mode solves the comparison
  equation with a defect that has only a **simple** pole, `|a| <= 40/(x²-1)`, uniformly in the aperture
  and in `0 <= s <= 1/2`; the eigenvalue enters only through that range, so nothing is imported
- [ ] Lean: the total Liouville mass `int m |a| E² = O(1/c)` of that defect, which is the exponential
  factor of the Volterra estimate

## Gates

- [x] exact low radial index range established before asymptotics
- [x] nonzero fixed-degree phase retained
- [x] unique stationary point solved exactly
- [x] leading Bessel first row bounded uniformly on the finite aperture
- [x] Dunster envelope remainder summed on that aperture
- [x] logarithmically weighted exact first row proved `o(d_1)`
- [ ] prove the high truncated-divisor weighted radial tail
- [ ] combine with the intact Poisson central correction
- [ ] prove the archimedean and true-Weil gap comparison
