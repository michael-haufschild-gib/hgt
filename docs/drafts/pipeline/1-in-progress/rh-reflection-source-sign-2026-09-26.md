# Reflection-orbit exclusion from the actual arithmetic source

- **ID:** RH-REFLECTION-SOURCE-SIGN-20260926
- **Stage:** 1-in-progress
- **Type:** RESEARCH — no unconditional RH proof or falsification
- **Goal:** An unconditional, closed Lean proof of RH or its negation. A new criterion is not completion.
- **Constraints:** No numerical experiments; one foreground Lean process; scratch checks before a named leaf build; no full builds.

## Frozen target and route test

Prove the full arithmetic source moment form nonnegative on every real polynomial, or find an exact negative test. Corpus `ReciprocalAtomPolynomialApproximation` already converts polynomial positivity into exclusion of every free reflection orbit. The hard input is the source sign, not a missing detector. A finite minor is useful only if its proof exposes a mechanism extending to arbitrary degree.

## Scientific interrogation

- **What would a scientist do?** Identify the exact source-specific step, freeze a falsifiable mechanism, test its boundary cases symbolically, and distinguish established evidence from a proposed proof.
- **Right problem?** The source-to-sign implication is required. Reproving ordinate injectivity, orbit counting, or polynomial isolation would not advance it.
- **Where is arithmetic used?** In the exact full theta density and its modular boundary cancellations; generic positive measures and finite shell prefixes do not inherit the target sign.
- **What is being removed?** The omitted theta tail. Retain it: every nonempty finite prefix has a nonzero boundary slope whose leading Fourier contribution is canceled by the complete tail.
- **Symmetry invariant?** Reflection-even quantities can detect a free orbit, although they cannot distinguish its two orientations. Their vanishing requires an independent source proof.
- **Primitive/derived reversal under examination:** Treat full-source boundary cancellation as constitutive data for the moment form, rather than regarding the omitted tail as an error estimated in absolute value. No universal law or positive representation has yet been established.

## Research plan

1. Inspect the full-source score/Schur identities and existing no-gos.
2. Freeze and symbolically attack a mechanism that retains exact boundary cancellation at every degree.
3. Formalize only a dependency-closed result, audit its hypotheses and axioms, and record its consequence for the whole route.

## Frozen mechanism test C1: monotone-source contraction

**Classification:** derived mechanism conjecture, not a new universal RH conjecture.
For every even probability density decreasing on the positive half-line, conjecture
`0 <= B <= D`, where `B` is the sign-adjusted coefficient matrix of the
denominator-cleared logarithmic moment kernel and
`D_ij = mu_(i+j+1)/((2i+1)!(2j+1)!)` is the odd raw Gram matrix.

**Motivation:** the existing actual-theta Gram comparison card leaves this representation
open; uniform interval sources have `B=D`; existing theta diagnostics suggest contraction.
The universal claim is stronger than the actual-theta statement and has a cheap exact falsifier.

**Symbolic experiment:** mix equal amounts of uniform laws on `[-1,1]` and `[-4,4]`.
The even moments are `(1+4^(2k))/(2*(2k+1))`. Test `D-B` on coefficient
indices `{1,2}` and vector `(-13,17)`. Lean verifies the exact value
`-119221/32256`. No floating-point experiment was run.

**Positive survivor, Lean-proved:** for two uniform radii with squared radii `A,B`,
the determinant of the difference-source cleared block at indices `{1,2}` is
`(A-B)^4 * (-3*A^4+36*A^3*B-2*A^2*B^2+36*A*B^3-3*B^4)/4572288000`.
For a mixing proportion `t`, the covariance block is multiplied by `t*(1-t)`.
This gives an exact sharp boundary for that compression, not an all-degree classification.

**Whole-route consequence:** monotonicity cannot establish the proposed
positive-contraction representation. The actual theta inequality remains undecided and
would need arithmetic information beyond a decreasing density. Failure of `D-B >= 0`
does not refute `B >= 0`, and neither is an RH counterexample.

Closed mechanism and exact paper proof:
`../5-failed/monotone-source-gram-contraction.md`.

## Pivot and relevance gate

The next source-sign attack must use the exact full theta assembly in the nonlinear
cumulant form. Merely adding finite moment controls or generic shape assumptions
does not meet the route test: the existing paper countermodels in
`../2-fully-proven/theta/theta-compact-critical-strip-zero-engineering.md`
preserve evenness, strong log-concavity, finite moments, exact tails and half-density
charges while inserting a nonreal strip zero. That result remains paper-only.

No new universal conjecture is frozen here: a positive-contraction representation
with an extra unspecified theta hypothesis would merely rename the missing sign.
The exact all-order theta cumulant recurrence and boundary cancellation must instead
be tested together. No source sign has been obtained, and the RH goal stays open.

## Evidence and status

## Concrete finite-prefix falsification: pending Lean transfer

The corpus already contains a paper proof that every nonempty fixed theta-shell
prefix has infinitely many nonreal Fourier zeros (`k-rvm-finite-sixth-moment-bracket.md`,
paragraph headed “Every fixed theta-shell prefix”). This is prior research, not a new
conjecture or novelty claim. Its concrete entire/subquadratic-growth transfer remains
open in Lean. Close that transfer using the literal source envelope, then combine
`ThetaFiniteShellFourierBoundary` with `FiniteZeroSubquadraticTwoRayDecay`.

**Route test:** this excludes every fixed-prefix real-zero foundation, not merely
the numerically tested first two. The positive survivor is the already formalized
exact full-tail compensation. It does not supply full-source Hankel positivity.

**Verification plan:** scratch entire transform and growth bound; prove infinitely
many nonreal zeros; audit assumptions and axioms; named leaf build and formal lint.
No numerical experiment and no edits to another researcher's log.

Separate fact log: `rh-reflection-source-sign-2026-09-26-facts.md`.
Search outputs are discovery evidence, not compilation certificates. Existing unrelated GL3 work is outside this research scope.
