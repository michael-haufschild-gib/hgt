# Dumitrescu--Wolf tangent phases wrap infinitely often

- **ID:** dumitrescu-wolf-tangent-phase-wrap-obstruction
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (Lean 4, fully unconditional)
- **Source:** C. Dumitrescu and M. Wolf, *The Disproof of the Riemann Hypothesis*, arXiv:2102.08313v3, Lemma 2 and Appendix
- **Statement:** Under the paper's RH setup, the two Riccati sequences used to quantize the vertical zero contribution cannot converge to `+infinity` and `-infinity`; whenever their recurrences stay defined, each is a tangent of a divergent phase with vanishing increments and therefore has a subsequence tending to zero.

## Goal

Audit the endpoint claim that turns the vertical zero integral into an integer
multiple of `pi`.  This is a route discriminator, not an RH result.

## Gates

- [x] 0 -> 1 in-progress: the claimed quantization was reduced to the two explicit Riccati recurrences
- [x] 1 -> 2 fully-proven: the recurrence was solved as a tangent phase and the asserted limits were contradicted, `[PROVED HERE]`
- [x] 2 -> 3 formalized, **unconditionally and end to end**: the abstract obstruction
  (`HTGeometry.TangentPhaseWrapObstruction`), the two paired vertical channels
  (`RHTower.DumitrescuWolfPhaseWrap`), the divergence `sum_rho 1/|rho| = infinity`
  (`RHTower.XiZeroSumDivergence`) and the assembly for the actual zeta ordinates
  (`RHTower.XiOrdinateEndpointObstruction.not_tendsto_atTop_verticalLowerRiccati_xiOrdinate`).
  Axioms `[propext, Classical.choice, Quot.sound]` throughout; no arithmetic hypothesis remains.
- [ ] 3 -> 4 publication-ready

## Theorem

Fix `1/2 < alpha < beta < 1` and `T > 0`, and put

```text
A = (alpha-1/2)(beta-1/2),    c = beta-alpha > 0.
```

Let `gamma_k` be the positive ordinates of the nontrivial zeta zeros, with
multiplicity, under the paper's RH assumption.  Define

```text
h_-(k) = c (gamma_k-T)/(A+(gamma_k-T)^2),
h_+(k) = -c (T+gamma_k)/(A+(T+gamma_k)^2).
```

For all sufficiently large `k`, `h_-(k)>0`, while `h_+(k)<0` for every
`k`.  Moreover,

```text
h_-(k) -> 0,                 h_+(k) -> 0,
sum_k arctan(h_-(k)) = +infinity,
sum_k arctan(h_+(k)) = -infinity.
```

Consider the recurrences appearing in the paper,

```text
f(k+1) = (f(k)+h_-(k))/(1-f(k)h_-(k)),    f(1)=0,
g(k+1) = (g(k)+h_+(k))/(1-g(k)h_+(k)),    g(1)=0.
```

If a denominator vanishes, the corresponding recurrence is not defined.  If
no denominator vanishes, then neither `f(k)->+infinity` nor
`g(k)->-infinity`.  In fact, each sequence has a subsequence tending to
zero.

## Proof `[PROVED HERE]`

The Riemann--von Mangoldt counting law gives

```text
N(X) = (X/(2 pi)) log(X/(2 pi)) - X/(2 pi) + O(log X).
```

Partial summation therefore gives

```text
sum_(0<gamma_k<=X) 1/gamma_k -> +infinity.
```

For large `k`, `gamma_k>2T` and

```text
h_-(k)  asymptotic to  c/gamma_k,
-h_+(k) asymptotic to  c/gamma_k.
```

Both magnitudes tend to zero, and `arctan x` is comparable to `x` near
zero.  The two asserted divergences follow.

The tangent addition identity solves the recurrences exactly.  As long as
all denominators are nonzero,

```text
f(N) = tan(sum_(k<N) arctan(h_-(k))),
g(N) = tan(sum_(k<N) arctan(h_+(k))).
```

It remains to use an elementary phase-wrap lemma.  If `u_k>0`, `u_k->0`,
and `sum u_k=+infinity`, let `N_m` be the first index at which the partial
sum reaches `m pi`.  Minimality gives

```text
0 <= sum_(k<=N_m) u_k - m pi < u_(N_m),
```

so the tangent of that partial sum tends to zero.  Applying this to the
eventually positive increments `arctan(h_-(k))` supplies a subsequence of
`f` tending to zero.  Applying the same argument to
`-arctan(h_+(k))` supplies a subsequence of `g` tending to zero.  Hence the
limits asserted in Lemma 2 of the preprint are impossible.

If a recurrence denominator does vanish, its claimed globally defined
sequence already fails.  Thus the conclusion holds in both cases.

## Consequence for the proposed disproof

The paper separates the paired vertical zero phase into a `T-gamma_k`
channel and a `T+gamma_k` channel and assigns them endpoint phases `pi/2`
and `-pi/2`.  The theorem shows that neither endpoint exists.  The two
channels must instead remain paired: their leading `1/gamma_k` tails cancel,
leaving a convergent but non-quantized phase whose `gamma_k` near `T` form a
moving boundary layer.  No integer-multiple-of-`pi` conclusion follows.

There is a second, independent scaling gap.  The paper bounds the denominator
tail by `epsilon_2=1/T^2`; restoring the omitted numerator
`2(s-1/2)` and integrating over an edge of length `2T` yields only an `O(1)`
bound, not `o(1)`.  A smaller tail tolerance could repair that estimate, but
cannot repair the false phase limits above.

## Status

The recurrence obstruction is complete.  Bibliographic provenance and the
precise current-version comparison remain subject to the repository's
external audit, so this card remains in `needs-audit`.


## Lean status

Two modules, both with `#print axioms` equal to `[propext, Classical.choice, Quot.sound]`.

### `GaloisForLFunctions/HTGeometry/TangentPhaseWrapObstruction.lean`

The obstruction, stated for an arbitrary increment sequence and **stronger than the card's own
statement**: no sign hypothesis on the increments is needed, because minimality of the crossing
index already forces the crossing increment to be positive.

- `tangentIterate` -- the recurrence `F 0 = 0`, `F (k+1) = (F k + h k)/(1 - F k h k)`;
  `arctanPartialSum` -- the accumulated phase `S N = sum_{k<N} arctan(h k)`.
- `cos_ne_zero_and_tangentIterate_eq_tan` / `tangentIterate_eq_tan` -- the exact solution
  `F N = tan(S N)` whenever no denominator vanishes, carried together with `cos (S N) != 0`
  (the induction step is `cos(S+a) = cos S cos a (1 - tan S tan a)`).
- `phaseWrapIndex` -- the first index at which `S` reaches `m pi`; `phaseWrapIndex_spec`,
  `lt_of_lt_phaseWrapIndex`, `phaseWrapIndex_pos`, `tendsto_phaseWrapIndex_atTop`.
- `phaseWrap_overshoot_lt` -- the minimal-overshoot inequality
  `0 <= S(n_m) - m pi < u(n_m - 1)`.
- `tendsto_tan_phaseWrap` -- the phase-wrap lemma: `tan (S (n_m)) -> 0`.
- `exists_subseq_tangentIterate_tendsto_zero`, `not_tendsto_atTop_tangentIterate` and the mirror
  `not_tendsto_atBot_tangentIterate` (via `tangentIterate_neg`, `arctanPartialSum_neg`).
- `tendsto_arctanPartialSum_atTop_of_eventually_ge` /
  `tendsto_arctanPartialSum_atBot_of_eventually_le` -- comparison tests for the accumulated phase.

### `GaloisForLFunctions/RHTower/DumitrescuWolfPhaseWrap.lean`

The two paired vertical channels of the preprint, with `A = (alpha-1/2)(beta-1/2)`, `c = beta-alpha`:

- `verticalChannelOffset`, `verticalChannelGap`, `verticalLowerIncrement`,
  `verticalUpperIncrement`;
- `verticalLowerIncrement_pos`, `verticalUpperIncrement_neg` -- the asserted signs;
- `tendsto_verticalLowerIncrement`, `tendsto_verticalUpperIncrement` -- both channels vanish;
- `abs_channelTerm_le`, `channelTerm_ge`, `verticalLowerIncrement_ge`,
  `neg_verticalUpperIncrement_ge` -- the two-sided Cauchy-kernel estimates, in particular the
  harmonic minorants `c/(4 gamma_k)` and `c/(8 gamma_k)`;
- `tendsto_arctanPartialSum_verticalLower` / `..._verticalUpper` -- divergence of the accumulated
  phases to `+infinity` and `-infinity`;
- `not_tendsto_atTop_verticalLowerRiccati`, `not_tendsto_atBot_verticalUpperRiccati`,
  `exists_subseq_verticalLowerRiccati_tendsto_zero` -- the endpoint obstruction itself.

The linear floor `arctan x >= x/2` on `[0,1]` is taken from the cubic control
`sub_arctan_le_cube_div_three` of `GaloisForLFunctions.HTGeometry.HausdorffCDDPhaseKernel` rather
than restated.

### The harmonic discharge layer

`GaloisForLFunctions/HTGeometry/HarmonicOrdinateDivergence.lean` reduces the arithmetic hypothesis
to its sharpest classical form:

- `tendsto_sum_const_div_natSucc_atTop`, `tendsto_sum_inv_atTop_of_le_linear`,
  `not_summable_inv_of_le_linear`, `tendsto_sum_inv_atTop_of_counting` -- a positive sequence with
  `gamma k <= c (k+1)` eventually has divergent reciprocal partial sums.

Composed with the channels this gives
`not_tendsto_atTop_verticalLowerRiccati_of_le_linear` and
`not_tendsto_atBot_verticalUpperRiccati_of_le_linear`: **a linear upper bound on the ordinates
already forbids both asserted endpoints.**  For a monotone ordinate sequence that bound is
equivalent to the counting lower bound `N(T) >> T`, which is far weaker than the full
Riemann--von Mangoldt asymptotic `N(T) ~ (T/2pi) log(T/2pi)` used in the paper proof.

### Remaining input

What is still outside Lean is exactly one classical statement: the nontrivial zeta ordinates grow
at most linearly, `gamma_k = O(k)`, equivalently `N(T) >> T`.  That is exactly the Riemann--von Mangoldt consequence
`sum_gamma 1/gamma = infinity` used in the paper proof.  The corpus currently has
`RHTower.xiZeroSet_infinite` and `finite_xiDivisorSupport_centered_norm_le` (the divisor is
infinite and locally finite) but no zero-counting rate, so `N(T) ~ (T/2pi) log(T/2pi)` -- and hence
the unconditional discharge of this hypothesis for the zeta ordinates -- is the one piece still
outside Lean.  Everything else in the card is formalized without hypotheses.

## Log

- 2026-07-26 -- Formalized. The abstract obstruction was proved in a strictly stronger form than the
  card states: positivity of the increments is not needed anywhere, since at a first crossing of
  `m pi` the increment is positive automatically. The tangent-recurrence closed form is carried with
  the invariant `cos (S N) != 0`, which is what makes the induction go through without side
  conditions on the phase. The zeta channels are instantiated with the harmonic minorants; the only
  hypothesis left is divergence of the harmonic ordinate sum.
- 2026-07-26 -- Harmonic discharge layer added
  (`GaloisForLFunctions.HTGeometry.HarmonicOrdinateDivergence`). The remaining arithmetic input is
  now the weakest form that still works: a linear ordinate bound `gamma_k = O(k)`, i.e. the counting
  lower bound `N(T) >> T`, rather than divergence of `sum 1/gamma_k` or the full Riemann--von
  Mangoldt asymptotic. Route surveyed for closing it unconditionally: mathlib now carries
  `Analysis/Complex/JensenFormula.lean`, `Analysis/Complex/BorelCaratheodory.lean` and
  `Analysis/Complex/ValueDistribution/*` (Cartan, characteristic function, first main theorem), so
  the counting function is reachable from a lower bound on the circle mean
  `mean_{|s|=R} log|xi| >> R log R`. The obstacle there is not Jensen but the growth input: the
  mean is carried by `zeta` in the left half plane through the functional equation, so complex
  Stirling for `Gamma` plus the completed functional equation are the next pieces to build.
- 2026-07-26 -- Jensen counting lower bound built
  (`GaloisForLFunctions.HTGeometry.JensenCountingLowerBound`), the piece that converts growth of an
  entire function into a lower bound on its zero count. Mathlib ships only the upper direction
  (`AnalyticOnNhd.sum_divisor_le`); the lower direction is obtained by comparing Jensen's formula at
  two radii `0 < r < R`, where the termwise estimate
  `d(u) log(R/|c-u|) <= d_r(u) log(r/|c-u|) + d(u) log(R/r)` holds with equality inside the small
  ball and by monotonicity of `log` outside it. Results: `zeroCount`,
  `divisor_mul_log_le`, `circleAverage_sub_le_zeroCount_mul_log`, `le_zeroCount`, giving
  `(circleAverage (log |f|) c R - circleAverage (log |f|) c r) / log (R/r) <= zeroCount f c R`
  for any `f` analytic on the closed ball with `f c != 0`. Axioms clean.

  Remaining chain for the card, now fully explicit:
  growth of `xi` (complex Stirling for `Gamma` + the completed functional equation)
  -> circle-average lower bound `mean_{|s|=R} log|xi| >> R log R`
  -> `le_zeroCount` gives `zeroCount xi 0 R >> R log R`
  -> enumeration of the divisor gives `gamma_k = O(k)`
  -> `tendsto_sum_inv_atTop_of_le_linear` discharges the harmonic hypothesis
  -> `not_tendsto_atTop_verticalLowerRiccati` closes the card unconditionally.
  Steps 3-5 of that chain are now in Lean; steps 1-2 are the remaining analytic build.
- 2026-07-26 -- Gamma growth seed built (`GaloisForLFunctions.HTGeometry.GammaLogGrowth`).
  Corpus search first found `HTGeometry.pow_mul_exp_neg_le_factorial` (`n^n e^{-n} <= n!`) already
  present in `HTGeometry/FactorialGrowthBounds.lean`, and `Real.pow_div_factorial_le_exp` already in
  mathlib, so neither was rewritten; what was missing is the logarithmic form and the maximal-type
  conclusion: `natMul_log_sub_one_le_log_factorial` (`n (log n - 1) <= log n!`),
  `natMul_log_sub_one_le_log_Gamma`, `eventually_half_natMul_log_le_log_factorial`,
  `tendsto_log_factorial_div_atTop` (`log n!/n -> infinity`) and `eventually_lt_log_factorial`
  (no bound `log Gamma(n+1) <= C n` can hold). Axioms clean.

  This is the growth seed for both remaining routes. Route survey recorded so the next session does
  not re-derive it:
  * Jensen route: needs `mean_{|s|=R} log|xi| >> R log R`. The mean splits as
    `mean log|s(s-1)/2| = O(log R)`, `mean log|pi^{-s/2}| = 0` exactly (harmonic, value at centre),
    `mean log|Gamma(s/2)| = -R/2 + O(log R)` (Jensen applied to the entire `1/Gamma`, whose zeros are
    the nonpositive even integers), so the whole `R log R` is carried by `zeta` in the left half
    plane through the functional equation. Complex Stirling is therefore unavoidable there.
  * Hadamard route: the corpus already has the genus-one canonical product and the entire
    nowhere-zero quotient in `RHTower/XiHadamardFactorization.lean`
    (`xiCanonicalProduct`, `xiHadamardQuotient`, `xiHadamardQuotient_mul_canonicalProduct`,
    `xiHadamardQuotient_constant_of_log_reBound`), and mathlib now has
    `Analysis/Complex/BorelCaratheodory.lean`. Closing `xiHadamardQuotient = exp(a+bs)` needs only the
    *upper* growth bound `log|xi(s)| = O(|s| log|s|)`, after which `sum 1/|rho| < infinity` would force
    `log|xi(sigma)| = O(sigma)`, contradicting `tendsto_log_factorial_div_atTop` along `sigma = 2n`.
    This route is the shorter one and is the intended continuation.
- 2026-07-26 -- `xi` is not of exponential type
  (`GaloisForLFunctions.RHTower.XiRealAxisGrowth`), unconditionally. Corpus search first turned up
  the decisive fact that `RHTower/XiHadamardGrowth.lean` already carries the **completed**
  unconditional Hadamard factorization `XiC_eq_constant_mul_canonicalProduct`
  (`XiC = XiC 0 * xiCanonicalProduct`, with no exponential factor at all, evenness having killed the
  linear term via `xiHadamardQuotient_constant`). That removes the whole Borel--Caratheodory step
  from the remaining work.

  Built here, along the even integers `s = 2(m+1)`:
  * `one_le_norm_riemannZeta_natCast` -- `1 <= ‖zeta k‖` for natural `k > 1`, from the Dirichlet
    series having nonnegative real terms with first term one;
  * `xi_eq_mul_completedRiemannZeta` -- off the two poles, `xi s = s(s-1)/2 * Lambda s`, reconciling
    the tower's entire `xi` with mathlib's `completedRiemannZeta`;
  * `completedRiemannZeta_eq_Gammaℝ_mul`, `Gammaℝ_two_mul_natSucc` -- the archimedean factor, equal to
    `pi^{-(m+1)} m!` at `s = 2(m+1)`;
  * `factorial_mul_rpow_le_norm_xi` -- `m! * pi^{-(m+1)} <= ‖xi (2(m+1))‖`;
  * `log_sub_le_log_norm_xi`, `tendsto_log_norm_xi_div_atTop`
    (`log ‖xi (2(m+1))‖ / (2(m+1)) -> infinity`) and `eventually_lt_log_norm_xi` (no linear
    majorant). Axioms clean.

  What remains to close the card is now a single step: from `sum_rho 1/‖rho‖ < infinity` the
  genus-one canonical product obeys `|E_1(s/rho)| <= exp(2|s|/‖rho‖)`, hence
  `log ‖XiC s‖ <= log ‖XiC 0‖ + 2‖s‖ * sum 1/‖rho‖ = O(‖s‖)`, contradicting
  `tendsto_log_norm_xi_div_atTop` transported through `XiC z = xi (1/2 + z I)`. That yields
  `¬ Summable (fun rho => 1/‖rho‖)`, then `gamma_k = O(k)`, then
  `tendsto_sum_inv_atTop_of_le_linear`, then the endpoint obstruction.
- 2026-07-26 -- **`sum_rho 1/|rho| = infinity` proved unconditionally in Lean**
  (`GaloisForLFunctions.RHTower.XiZeroSumDivergence`). This is the genus-one statement for the Xi
  divisor, obtained with no counting law at all. The argument:
  * `norm_canonicalProductE1Indexed_le_exp_of_summable_inv` -- first-power summability of the
    reciprocal zero norms makes a genus-one canonical product of exponential type. Corpus reuse:
    `canonicalProductE1Indexed_norm_le_exp_min` of `RHTower/CanonicalProductGrowth.lean` already
    supplies `‖P z‖ <= exp (sum min(2‖z‖/‖a i‖, 2‖z‖²/‖a i‖²))`; only the first-power
    specialisation was missing.
  * `norm_XiC_le_exp_of_summable` -- transported to `XiC` through the corpus's completed Hadamard
    factorization `XiC_eq_constant_mul_canonicalProduct`, which contributes only the constant
    `XiC 0` (no exponential factor).
  * `xiEvenRotation`, `XiC_xiEvenRotation`, `norm_xiEvenRotation_le` -- the rotation
    `w_m = -i(2(m+1) - 1/2)` with `XiC w_m = xi (2(m+1))` and `‖w_m‖ <= 2(m+1)`.
  * `not_summable_inv_norm_xiSpectralPoint` and `not_summable_inv_norm_sub_half` -- exponential type
    would bound `log ‖xi (2(m+1))‖ / (2(m+1))` by a constant, contradicting
    `tendsto_log_norm_xi_div_atTop`. Axioms clean throughout.

  Card status: the mathematical content is now complete and unconditional. What is left is purely
  bookkeeping -- packaging the Xi divisor as a monotone ordinate sequence `gamma : ℕ → ℝ` so that
  `not_summable_inv_norm_xiSpectralPoint` feeds `tendsto_sum_inv_atTop_of_le_linear` and then
  `not_tendsto_atTop_verticalLowerRiccati`. No analytic input remains.
- 2026-07-26 -- **Card closed on the Lean side: the obstruction is now unconditional for the actual
  zeta ordinates** (`GaloisForLFunctions.RHTower.XiOrdinateEndpointObstruction`). The last step
  avoided constructing a monotone enumeration entirely. `XiZeroCopy` is countable, and it is
  infinite because over a finite index type every family is summable, contradicting
  `not_summable_inv_norm_xiSpectralPoint`; so `instInfiniteXiZeroCopy` comes for free from the
  divergence theorem itself. Square-summability gives
  `tendsto_norm_xiSpectralPoint_cofinite` (spectral norms escape every bound off finite sets), and
  an arbitrary enumeration `xiOrdinateEquiv : ℕ ≃ XiZeroCopy` then yields `xiOrdinate` with
  `xiOrdinate_pos`, `tendsto_xiOrdinate_atTop` (injectivity sends `atTop` to `cofinite`) and
  `tendsto_sum_inv_xiOrdinate_atTop`. No monotonicity of the enumeration is needed anywhere.

  Final statements, with no hypotheses beyond `1/2 < alpha < beta`, `T > 0` and the recurrences
  staying defined: `not_tendsto_atTop_verticalLowerRiccati_xiOrdinate`,
  `not_tendsto_atBot_verticalUpperRiccati_xiOrdinate`,
  `exists_subseq_verticalLowerRiccati_xiOrdinate_tendsto_zero`.

  Remaining gate is the non-Lean one: `3 -> 4 publication-ready`.
