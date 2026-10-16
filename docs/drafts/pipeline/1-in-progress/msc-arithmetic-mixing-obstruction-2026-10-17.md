# MSC arithmetic mixing obstruction

Status: research in progress. Frontier map is read-only.

## Objective

Construct one unconditional structural contribution to MSC that removes a hard obstruction. Exclude improved bounds, RH equivalences, and additional receivers. Work from current Lean corpus; no external search, novelty audit, numerical experiments, or old research Markdown.

## Plan

1. Identify exact current source and obstruction in Lean; search whole corpus for mechanisms.
2. Conjecture, attack, record failures, and iterate until a structural survivor has a complete proof.
3. Formalize exact survivor; audit with foreground targeted Lean invocation, axioms, and formal lint; wire module into umbrella without building umbrella.

## Established context

- Threshold-tracked real powers preserve mass by moving the affine spectral target into the zero-free Euler half-plane.
- Exact physical source/overlap columns admit a Bessel Hilbert realization only for Re rho > 1.
- Complete minimal, Markushevich, and uniformly minimal strong Markushevich realizations exist below that wall. Qualitative completeness does not provide the missing stability.
- Consequently a live construction must mix arithmetic coefficients before admission, or use genuinely singular source geometry with a proved source handoff.

## Conjecture log

1. Stable Hilbert mixing retaining both literal analysis columns: rejected by existing Bessel wall. Do not pursue.
2. Arithmetic summatory cancellation alone: already present in `SquarefreeDiscrepancyMellin`. Its continuation and square-root estimate are inputs, not contributions.
3. Fixed arithmetic Hilbert source with a strongly holomorphic evaluation family and exact conormal transport: survives preliminary attack. The Bessel obstruction assumes retention of both literal coefficient analysis columns; this construction first sums coefficients and removes the source-derived density. No divisor is used to construct it.

## Exact conjecture and dependency-closed proof

Write c = squarefreeDensity and E(x) = sum_{1 <= n <= floor x} mu(n)^2 - c x.
The corpus proves |E(x)| <= 4 sqrt(x) for x >= 1, and
M(s) = integral_1^infinity E(x) x^(-s-1) dx = zeta(s)/(s zeta(2s)) - c/(s-1)
for Re s > 1/2, s != 1, with the pole-cleared version also valid at 1.

Use the fixed Hilbert space H = C direct-sum L2(R,dt). All functions below vanish for t <= 0.
Define h(t) = E(exp t) exp(-t/2)/(1+t), and k_s(t) = (1+t) exp(-(s-1/2)t).
The fixed arithmetic source is U = (c,h). Define the pole-cleared vector
V(s) = (s, s(s-1) k_s). These definitions use the counting coefficients and their proved density, never Xi values or zeros.

1. |h(t)| <= 4/(1+t), so h is in L2. For every Re s > 1/2, k_s is in L2 because its norm square is (1+t)^2 exp(-2(Re s-1/2)t). Polynomial exponential moments are integrable. On a sufficiently small complex ball around s, one slower decaying such kernel dominates the whole family. The corpus L2 Cauchy holomorphy theorem therefore proves strong complex differentiability, with k'_s(t) = -t k_s(t). Iteration gives all analytic jets.
2. h is real. Change variables x = exp t in the absolutely convergent moment to obtain inner(h,k_s) = M(s). Hence Q(s) := inner(U,V(s)) = c s + s(s-1) M(s) = (s-1) Z_sq(s), including the continued value Q(1)=c. The spectral argument s is unchanged.
3. For s != 1, define W(s)=V(s)/(s-1). Then inner(U,W(s)) = Z_sq(s). Strong differentiation gives inner(U,W'(s)) = Z'_sq(s), with both vectors admitted to the same fixed Hilbert space.
4. At a safe real base sigma>1, divide W(sigma+u epsilon) by Z_sq(sigma). This equals the original overlap B(u) under the fixed source functional. The vector 2(epsilon W'(sigma+u epsilon) + epsilon A_sq(sigma) W(sigma+u epsilon))/Z_sq(sigma) reproduces the original division-free Fisher numerator. Thus the full divisor orders and the exact meromorphic conormal, including multiplicity residue 2m, are preserved. This is an identity of source and jet vectors, not an RH implication.
5. Arithmetic fidelity is before analytic evaluation: undo the positive weight in h and add c exp t to recover the squarefree counting staircase. Its values at integer cutoffs recover every coefficient by consecutive differences. An a.e. version can use interval averages; do not claim this strengthening until formalized.

## Scope and attack

- A new scalar continuation is not claimed: it is already in the corpus.
- The new object is one fixed arithmetic Hilbert source and explicit analytic value/jet vectors admitting every physical strict-right strip point without moving that point. It replaces raw coefficientwise admission, so the old Bessel theorem does not apply.
- Positivity of a new Sonin energy receiver, or source coercivity sufficient for RH, is not established by Hilbert admission. Do not hide that remaining question.
- No improved discrepancy estimate is used or sought.

## Verification

Pending. No new theorem claimed.
