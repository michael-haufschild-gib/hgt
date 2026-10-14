# JAS constant-vector positivity at infinitely many dyadic scales

## Conjecture (cycle 215)

RH holds iff, for infinitely many `N`, the level-one constant-vector JAS test on the primes of
`(N, 2N]` is nonnegative for every `z ∈ ℂ`. This is `JasConstProductPositiveOn (primes in (N,2N]) 1`.

## Mechanism

Write `u = z/(1+|z|²)`, so `|u| ≤ ½` with arbitrary phase. The test divided by `(1+|z|²)^{|P|}` is

`T(P, u) = Re Σ_q w_q ∏_{p∈P} (1 + u A_p(q) + ū B_p(q))`,

where:

- `A_p(q) = p^{−1} p^{−(q−½)}` and `B_p(q) = p^{−1} p^{q−½}`;
- `w_q = 1/(q(1−q))`.

For an off-line zero `q = ½ + δ + iγ` the kernel is `≈ exp(ū S_q(N))`, with
`S_q(N) = Σ_{N<p≤2N} p^{q−3/2}` and `|S_q(N)| ≍ N^δ/(|q−½| log N) → ∞`.

The free phase of `u` aligns the dominant zero at every scale. Choosing `ū = Z/S_q` with
`Z = R + i(π − arg w_q)` gives `w_q e^Z = −|w_q| e^R`. No Dirichlet alignment over scales is needed.

## Verdict

**REDISCOVERED** for the mechanism. `JointAncestryRealAmplitudeDetection`
(`not_jasRealPositiveAbove_of_maximal_offLine`) has it, with real amplitudes, the window edge `N` as
the phase source, small amplitude `t = κ/E(N)`, and a maximal attained off-line zero.

**OPEN** for the full conjecture. Chains, where the supremum of the distances is not attained, are not
excluded.

## Positive survivor (paper)

**T216.** Let some off-line zero have maximal distance `δ`. Then for every sufficiently large `N`
there is `z` with a negative constant-vector test on `(N, 2N]`. Hence:

- RH ⟺ ZAL ∧ (∃ᶠ N: dyadic constant-vector positivity on `(N,2N]`);
- RH ⟺ no off-line chain ∧ (the same).

This replaces "all `m` and all `L` along a progression" in `JasProgressionPositive`.

Proof sketch:

- **Dominant zero.** Take `q*` with distance `δ` and minimal `|γ|`. Zeros at the same distance and
  larger height have `|S|` smaller by the fixed ratio `ρ₂ = |1−s₀|/|1−s₁| < 1`. Zeros closer to the
  line have `S = o(S*)`.
- **Two cases** for the conjugate pair `q*, q̄*` (with `S(q̄*) = conj S(q*)`, `φ = arg S(q*)`):
  - (B) `|φ| ≤ 1/R₀` mod `π`: take `ū S* = ±(R₀ + iπ)·e^{iφ}`. The pair contributes
    `≈ −2|w| e^{R₀} cos(R₀φ + arg w) < 0`, since `|arg w| ≤ 1/14`.
  - (A) otherwise: take `ū S* = R₁ + i(π − arg w)` with `R₁ = R₀³`. The conjugate exponent has real
    part `≤ R₁ cos 2φ + π ≤ R₁ − 2R₁/R₀² + π`, so it is dominated.
- **Competitors.** In both cases they stay below `ρ₂|Z| < Re Z − O(1)`.
- **Four-fold symmetry.** The reflections `1 − q*` and `1 − q̄*` repeat the real parts of `q̄*` and
  `q*`.

## The chain obstruction (exact form)

Positivity for all `|u| ≤ ½` at scale `N` gives, through the Fourier coefficients in `arg u` (a
nonnegative function's coefficients are bounded by its mean), approximately

`|Σ_q w_q S_q(N)^k| ≤ 2^{k+1} k! W` for every `k ≥ 1`, where `W = Re Σ_q w_q`.

Weighted Turán (`HTGeometry.exists_norm_weightedPowerSum_ge`, no separation needed) then shows the
following. With `R = max_q |S_q(N)|` and the near-maximal set `{|S_q| ≥ R(1 − η)}` of size `n`, either
`R ≲ n log R + log(1/β)` (`β` = top-group weight), or the test fails. So positivity at a large scale
forces one of:

- ≳ `R/log R` off-line zeros with almost equal `|S_q|` whose phases cancel like roots of unity
  (equal weights, heights within relative `O(1/R)`);
- near-maximal zeros of weight `≤ e^{−cR}`, i.e. at heights `≥ e^{cR/2}`.

Zero counting rules out the first option for zeros below height `≈ R²`. The second option, off-line
zeros at astronomically large heights, can dominate any single-scale test. Neither zero-density
estimates nor any finite-height input excludes them. Hence a sparse-scale JAS receiver **cannot**
exclude chains without a large-height input such as ZAL.

## Self-interaction phenomenon (new, paper)

For an off-line zero `q = ½ + δ + iγ`, the explicit formula for `Σ_{p≤x} p^{q−3/2} log p` contains the
term of its conjugate zero `q̄`. That term is `−x^{2δ−½}/(2δ−½)`: real, independent of `γ`, and growing
when `δ > ¼`.

Neighbouring off-line zeros `ρ'` near `q̄` add `x^{δ+δ'−½} e^{i(γ−γ')log x}/(δ+δ'−½+i(γ−γ'))`. The
cluster matrix `y^{a_j+ā_l}/(a_j+ā_l)`, with `a = q − ¾` and `Re a > 0`, is a positive definite
Cauchy–Gram matrix.

So an isolated high off-line zero with `Re q > ¾` is coherent (a real exponent) at every scale.
Cancelling clusters must come from ill-conditioned Cauchy–Gram configurations.

## Sweep (cycle 215, all killed)

| # | Conjecture | Verdict |
|---|---|---|
| S12 | The self-interaction bias in `Σ_p Φ(log p)/p` contradicts a bounded lag | INSIGNIFICANT: an internal consistency of the explicit formula |
| S13 | Temperedness enters the JAS kernel as an abscissa shift | INSIGNIFICANT: `ζ(s−a)ζ(s+a)` just shifts `σ*` by `a` |
| S14 | Hecke averaging `n ↦ qn` preserves dressed PD and improves the level | FALSE: no positivity transfer |
| S15 | Box test vectors `1_{[1,N]}` detect off-line zeros | FALSE: off-line pairs contribute `≈ N²/γ⁴ > 0` (blind) |
| S16 | Continuity of `σ*` along a deformation, plus the gap `σ* ∈ {0} ∪ [½,2]`, forces `σ* = 0` | FALSE: `σ*` jumps by `−1` at every RH transition (only lower semicontinuous) |
| S17 | Lebesgue-point or unique-ergodicity transfer at the identity of `T^∞` | CIRCULAR: BAG core (`z = 1` is a continuity point ⟺ RH) |

NO POSITIVE SALVAGE beyond T216 (paper) and the chain-obstruction law above.
