# MSC arithmetic mixing obstruction

Status: formalized. Frontier map was not edited by this task.

## Objective

Construct one unconditional structural contribution to MSC that removes a hard obstruction. Exclude improved bounds, RH equivalences, and additional receivers. Work from current Lean corpus; no external search, novelty audit, numerical experiments, or old research Markdown.

## Plan

1. Completed: identify exact current source and obstruction in Lean; search whole corpus for mechanisms.
2. Completed: conjecture, attack, record failures, and obtain a structural survivor with a complete proof.
3. Completed: formalize survivor, run targeted Lean and axiom audits, wire both modules, refresh index, and run formal lint. Global lint has four unrelated reachability failures listed below.

## Established context

- Threshold-tracked real powers preserve mass by moving the affine spectral target into the zero-free Euler half-plane.
- Exact physical source/overlap columns admit a Bessel Hilbert realization only for Re rho > 1.
- Complete minimal, Markushevich, and uniformly minimal strong Markushevich realizations exist below that wall. Qualitative completeness does not provide the missing stability.
- Consequently a live construction must mix arithmetic coefficients before admission, or use genuinely singular source geometry with a proved source handoff.

## Conjecture log

1. Stable Hilbert mixing retaining both literal analysis columns: rejected by existing Bessel wall. Do not pursue.
2. Arithmetic summatory cancellation alone: already present in `SquarefreeDiscrepancyMellin`. Its continuation and square-root estimate are inputs, not contributions.
3. Fixed arithmetic Hilbert source with a strongly holomorphic evaluation family and exact conormal transport: proved. The Bessel obstruction assumes retention of both literal coefficient analysis columns; this construction first sums coefficients and removes the source-derived density. No divisor is used to construct it.
4. The first construction admits evaluation jets but does not itself establish that the fixed source lies in the logarithmic clock domain. A reciprocal factor on the continuum source repairs this: h0=h/(1+t), h1=h0-h=-t h0, K_s=k_s-k'_s=(1+t)k_s. Both h0 and h1 lie in the same L2 space, and inner(h0,K_s)=M(s), inner(h1,K_s)=M'(s). This strengthens the transport to a fixed arithmetic source/Fisher-tangent pair. The already-proved strong holomorphy supplies K_s without new arithmetic bounds. This strengthened layer now passes a direct Lean audit with no diagnostics.

## Proved construction and dependency-closed proof

Write c = squarefreeDensity and E(x) = sum_{1 <= n <= floor x} mu(n)^2 - c x.
The corpus proves |E(x)| <= 4 sqrt(x) for x >= 1, and
M(s) = integral_1^infinity E(x) x^(-s-1) dx = zeta(s)/(s zeta(2s)) - c/(s-1)
for Re s > 1/2, s != 1, with the pole-cleared version also valid at 1.

Use the fixed Hilbert space H = C direct-sum L2(R,dt). All functions below vanish for t <= 0.
Define h(t) = E(exp t) exp(-t/2)/(1+t), and k_s(t) = (1+t) exp(-(s-1/2)t).
The fixed arithmetic source is U = (c,h). Define the partition vector
W(s) = (s/(s-1), s k_s) for Re s > 1/2, s != 1. These definitions use the counting coefficients and their proved density, never Xi values or zeros.

1. |h(t)| <= 4/(1+t), so h is in L2. For every Re s > 1/2, k_s is in L2 because its norm square is (1+t)^2 exp(-2(Re s-1/2)t). Polynomial exponential moments are integrable. On a sufficiently small complex ball around s, one slower decaying such kernel dominates the whole family. The corpus L2 Cauchy holomorphy theorem therefore proves strong complex differentiability, with k'_s(t) = -t k_s(t). Iteration gives all analytic jets.
2. h is real. Change variables x = exp t in the absolutely convergent moment to obtain inner(h,k_s) = M(s). Hence inner(U,W(s)) = c s/(s-1) + s M(s) = Z_sq(s). The spectral argument s is unchanged; the density pole remains explicitly separated.
3. Strong differentiation gives inner(U,W'(s)) = Z'_sq(s), with both vectors admitted to the same fixed Hilbert space.
4. At a safe real base sigma>1, divide W(sigma+u epsilon) by Z_sq(sigma). This equals the original overlap B(u) under the fixed source functional. The vector 2(epsilon W'(sigma+u epsilon) + epsilon A_sq(sigma) W(sigma+u epsilon))/Z_sq(sigma) reproduces the original division-free Fisher numerator. Thus the full divisor orders and the exact meromorphic conormal, including multiplicity residue 2m, are preserved. This is an identity of source and jet vectors, not an RH implication.
5. Arithmetic fidelity holds in the actual L2 quotient, not just at chosen point values. Undo the positive weight in h and add c exp t. On the nonempty interval (log(n+1),log(n+2)) the resulting function equals the constant count(n+1) almost everywhere. Divide its interval integral by log(n+2)-log(n+1) to recover that count. Differences of consecutive readouts recover mu(n+2)^2; the first count recovers mu(1)^2. Thus the source transport retains every coefficient through representative-independent interval readouts.
6. To place the derivative on the source, set h0=h/(1+t), h1=h0-h, and K_s=k_s-k'_s. The multiplier 1/(1+t) is bounded on the supported ray, so h0 lies in L2; h1 lies in L2 by subtraction and is exactly -t h0 almost everywhere. K is strongly holomorphic because k and its derivative are. Pointwise cancellation proves inner(h0,K_s)=inner(h,k_s)=M(s). Then inner(h1,K_s)=M(s)-(M(s)-M'(s))=M'(s). The pair reconstructs h=h0-h1 exactly. The source-generated full jet is -c/(s-1)^2 + inner(h0,K_s) + s inner(h1,K_s), so the exact MSC Fisher numerator uses the same evaluation vector for both fixed source legs.

## Implementation

- `RHTower/SquarefreeDiscrepancyHilbertTransport.lean`: fixed L2 source, explicit evaluation/jet family, strong holomorphy, exact Mellin pairing, interval recovery of counts and coefficient differences.
- `RHTower/Hedenmalm/HedenmalmSquarefreeSummatoryConormalTransport.lean`: density channel, full partition value/jet vectors, exact overlap/Fisher/conormal identities, germ and divisor preservation, premise-free physical-admission theorem.
- Serena symbol lookup is unavailable for these ignored Lean paths; new modules use standard file edits.

## Internal source audit

Searches covered the whole `GaloisForLFunctions` corpus; the index reported complete inventory but semantic coverage unavailable and some source/compiler freshness warnings. Relevant statements were read directly in Lean. Broad deep-search hits were mostly unrelated; exact squarefree-discrepancy search supplied the actual Mellin source. No external novelty claim is made.

## Scope and attack

- A new scalar continuation is not claimed: it is already in the corpus.
- The new object is one fixed arithmetic Hilbert source and explicit analytic value/jet vectors admitting every physical strict-right strip point without moving that point. It replaces raw coefficientwise admission, so the old Bessel theorem does not apply.
- Positivity of a new Sonin energy receiver, or source coercivity sufficient for RH, is not established by Hilbert admission. Do not hide that remaining question.
- No improved discrepancy estimate is used or sought.

## Verification

- Both modules passed foreground targeted `lake --old env lean -j 1` audits with no diagnostics; matching `.olean` and `.ilean` artifacts were produced. No full or umbrella build was run.
- A separate `/tmp` audit passed `lake --old env lean -j 1` (exit 0) and printed axioms for `fixedArithmeticClockPair`, `arithmeticCoefficient_source`, `physicalSummatoryHilbertAdmission`, `fixedClockConormal_eq`, `summatoryConormal_eventuallyEq`, and `analyticOrderAt_hilbertPartition_eq_xi`. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. Temporary audit and search files were removed afterward.
- Both modules are imported by `GaloisForLFunctions/RHTower.lean`. `scripts/formal_tools.py index` completed. Scoped `git diff --check` passed.
- `scripts/formal_tools.py lint` exited 1 because four other RHTower modules were unreachable from their umbrella: `FiniteWeilNodalAdjacentCoupling`, `FiniteWeilNodalMixtureTransport`, `LeeYangPrimePivotSpinPartitionSpectrum`, and `ThetaCuspRatioBoundaryNormOrientation`. Those concurrent files were not changed. The new MSC modules had no reported lint errors.

## Exact frontier change

`fixedArithmeticClockPair` constructs a fixed arithmetic source and its genuine logarithmic tangent in one positive Hilbert space. `physicalSummatoryHilbertAdmission` admits every strict-right-strip physical point while the original literal column remains non-summable. `arithmeticCoefficient_source` proves recovery of every squarefree coefficient; the conormal germ and Xi divisor multiplicities are preserved exactly. This supplies an arithmetic, nondiagonal admission mechanism without improving the discrepancy bound or assuming RH.

The next open step is a proved Sonin energy comparison for this transported source and clock pair. Hilbert admission and conormal fidelity alone do not establish that comparison or RH.
