# Connections across the open obstacles of review 1511

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Target:** 250 significant, unconditional, Lean-verified contributions to O1–O16 in `docs/reports/review-1511/obstacles-summary.md` §2.2.
- **Accepted contributions:** 3/250. Existing results, numerical refinements, conditional receivers and renamed statements do not count.
- **Evidence:** local corpus searches, exact source statements and kernel compilation. No external literature checks. Further axiom checks skipped at user request.

## Pending conjecture: O3, angular twists of the cubic probe

[Active proof card](the-angular-cubic-probe-has-a-rung-seed.md).

The finite-order probe estimates extend to each fixed sextic infinity type without changing their exponents. This would give the first half-plane left of 1 for the Grössencharacter rungs and lower the cubic correction boundary below 2/3.

**Connection:** the arbitrary multiplicative twist in the theta-to-Gauss conversion, the normalized cubic Gauss-sum description of rung coefficients, and the existing detector bounds.

**Required proof:** construct the angularly twisted analytic probe; verify every estimate used by the finite-order seed; prove nonvanishing for the actual `grossenLFunction`. Unit norm alone does not justify transferring a cancellation estimate.

**Known obstruction:** `HeckeFamily.Character` contains a periodic residue character and no infinity type. No theorem about its `LFunction` alone proves the conjecture.

**Verified subroute obstruction:** compensating the column character with an angular physical test transfers it to frequency and replaces the free sixth-power zeta pole by a regular, nonzero Grössencharacter factor. Six analytic/arithmetic helper modules passed plain Lean checks; no rung estimate follows. [Exact failure and positive survivor](../5-failed/angular-compensation-preserves-the-sixth-power-pole.md).

**Verified plain-slot input:** two additional modules give rapid angular periodic cancellation,
its exact six-unit ideal transfer and polynomial Mellin-height control. Every finite character
is included. Final plain checks passed; umbrellas wired. Actual-row transfer and its normalized two-slot bound also passed final checks.
Primitive reflection, uniform Euler-derivative control and actual radial energy also
passed final checks and are umbrella-wired. Primitive and original-modulus family bridges,
polynomial strip growth, actual Euler logarithms and subpower reciprocal bounds beyond
the actual angular zero supremum also passed final checks. Higher pure cusp jets now reflect
with an order-independent normalized absolute scale. Joint infinite smoothness of the actual
cubic source is proved by Fourier–Bessel derivative closure. Actual automorphy now gives
higher reflection into the same three cusp representatives; the order-one profiles and multiplier
are recovered exactly. The actual sextic twists and exact cusp-width normalization are also
verified. The actual angular Dirichlet reflection has the original conductor factor and
Gamma shifts by `3k`, with vertical degree independent of `k`. Entire-source Mellin convergence
and normalized angular continuation are verified. Smooth angular kernels and arbitrary radial decay of every logarithmic derivative are verified.
Exact smoothed angular reflection and finite-cusp reflection of the actual completed sum are verified. The extra cusp phase is multiplicative in the denominator and independent of finite residue. Finite source-seminorm bounds and uniform height separation with gain `min(1,R^(1/4))` are verified. Finite arithmetic contraction also preserves this gain. Low completed-sum energy,
high moment induction and the common-signal estimates remain open; no further contribution counted.

## Completion gate

Each accepted entry must identify the obstacle moved, the distinct mathematical connection, a dependency-closed proof, exact Lean declarations, umbrella import and final `lake --old env lean` audit. Working log: `logs/review-1511-connect-the-dots-250.md`.

## Accepted 1: O11, positive arithmetic twins are passive

The reciprocal quadratic twins in `SelbergClass.PositiveFiniteEulerTwins` also satisfy the global Schur passivity and continuous-spectrum unitarity of the modular horizon. For a prime `p` and `1/2 < σ < 1`, take `r=p^σ`, `u=p^(1−σ)`, `A=r+u`. The completed multiplier is `p^s+A+p^(1−s)`; its scattering quotient is `schurNum p (−A) v / schurDen p (−A) v`, `v=p^(−2w)`. Since `(r−1)(u−1)>0`, `A<p+1`, so the existing Schur criterion applies.

**Arithmetic survivor:** no nonnegative, absolutely convergent logarithmic Dirichlet series represents these twins on any right half-plane. The obstruction is `a(p)²>2a(p²)`. Every real reciprocal quadratic, including critical-circle factors, has a negative logarithmic coefficient at one of `p²,p⁴,p⁶,p⁸`. Both results are Lean-verified and umbrella-wired: [passive twins](../3-formalized/positive-euler-twins-passive-horizons.md), [finite separator](../3-formalized/reciprocal-quadratics-fail-a-finite-logarithmic-count-test.md).

**Internal duplicate rejected:** the sign pattern of the original positive-trace prime-two deformation follows from `PositiveFiniteEulerCoefficients`; the strict Euler-growth obstruction is already `PositiveFiniteEulerBound.not_fullClass`. Neither counts as a contribution.

**Backlog strengthening:** ordinary coefficient integrality also survives. At a prime `p>4`, choose `A=p`; the two reciprocal root radii are `(p±√(p²−4p))/2`, both greater than one and distinct. The ordinary coefficients then lie in `{0,1,1+p,1+2p}`. This exact family requires a separate audit; count it as a strengthening of the same contribution.

**Verified strengthening:** [rational Euler rigidity at one prime](../3-formalized/finite-euler-logarithmic-counts-force-unit-disk-roots.md). Every nontrivial reduced rational modification in `p⁻ˢ` fails either entire reflected completion or nonnegative logarithmic representation. The proof combines one-sided power-sum recurrence, uniqueness of logarithmic coefficients and ξ's exclusion of complete Euler fibres. All three modules passed final plain Lean checks and are umbrella-wired; this strengthens contribution 1.

**Verified finite-prime strengthening:** [finite-prime rational Euler rigidity](../3-formalized/finite-prime-rational-euler-rigidity.md) extends this to any finite product of local rational functions. Every nontrivial edit forces negative logarithmic coefficients at arbitrarily large powers of one edited prime. Prime-log independence prevents cancellation between distinct-prime fibres. Three new modules passed final plain checks and are umbrella-wired; contribution count unchanged.

## Accepted 2: O2, the actual untwisted squarefree theta pole

Opposite translations by `±ω` connect the source Fourier mask to a single-cusp spectral subtraction. They isolate the unramified square, whose double pole survives cube removal as a nonzero simple pole of `twistedSquarefreeSeries 1` at `2/3`, with explicit residue. [Dependency-closed proof and exact Lean declarations](../3-formalized/the-unramified-theta-square-has-a-nonzero-pole.md).

All nine modules passed final plain Lean checks and are umbrella-wired. This is one contribution. The row-root conductor phase and column-uniform remainder remain open; the existing rotated correlation alone did not isolate this series.

**Verified strengthening:** [Mellin nonvanishing](../3-formalized/the-untwisted-continuation-has-no-mellin-poles.md). The positive-ray/cosh Bessel normalization bridge identifies `M` with a nonzero Gamma quotient on `Re s>2/3`. The untwisted continuation is holomorphic throughout its upper strip and agrees pointwise on the initial strip. Final plain Lean check passed; umbrella-wired. Same contribution 2.

## Accepted 3: O2, the Gaussian-smoothed arithmetic main term

[Dependency-closed proof](../3-formalized/the-untwisted-theta-series-has-a-smoothed-main-term.md).
The actual signed squarefree ideal sum with normalized logarithmic Gaussian weight equals
`exp(4/9) untwistedThetaResidue · X^(2/3) + O_a(X^a)` for every `5/8<a<2/3`, with nonzero main coefficient.
The proof connects self-adjoint vertical bounds, cutoff-independent spectral residues, the Hecke
reciprocal seed and Gaussian Mellin inversion. All fourteen modules passed final plain Lean checks;
umbrellas wired. Analytic helpers are included in this single contribution.

The conductor-phase transfer to row-root moments, sharp cutoffs and column-uniform remainders
remain open. The active next conjecture is the O3 angular-probe extension above.
