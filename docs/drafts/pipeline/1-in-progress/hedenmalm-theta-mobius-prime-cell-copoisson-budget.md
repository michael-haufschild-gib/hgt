# Hedenmalm--theta Möbius prime-cell Gamma/co-Poisson budget

- **ID:** P-G48
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + LEAN FORMALIZATION IN PROGRESS
- **Source:** P-G47 boundary-layer conjugacy; existing primitive Gamma/co-Poisson prime-power current
- **Statement:** Existing primitive Gamma/co-Poisson current supplies exact negative P-G47 running principal symbol; finite prime cell plus that current leaves a strictly negative, globally summable midpoint-order complement.

## Goal

Test P-G46/P-G47 survivor: find independently source-created, label-faithful `-1/p` channel before
wall evaluation.  Reject mere counterterm if finite-temperature or neutral-fibre polarity remains
wrong.

## Gates

- [x] 0 → 1 in-progress: exact co-Poisson weld, positive complement, global summability
- [ ] 1 → 2 fully-proven: finalize after Lean source check
- [ ] 2 → 3 formalized: module, umbrella, build, lint, axiom audit green
- [ ] 3 → 4 publication-ready: standalone exposition and external novelty audit

## P-G48 coefficient weld `[PROVED HERE]`

The existing primitive Gamma/co-Poisson term satisfies at prime grade one

\[
 \mathcal C_p(s)=-p^{-s}.
\tag{1}
\]

P-G47 proves source running odds

\[
 a_p(x,\epsilon)
 =\mathcal R_{x\epsilon\log p}(p^{-1})
 =p^{-(1+x\epsilon)}.
\tag{2}
\]

Therefore

\[
 \boxed{\mathcal C_p(1+x\epsilon)=-a_p(x,\epsilon).}
\tag{P-G48a}
\]

This is not chosen diagonal subtraction.  `\mathcal C_p` was already constructed from the
Gamma/co-Poisson confluence jet, with divided von Mangoldt coefficient `1/k` at every prime power.
It is analytic in source grade and retains prime label before scalarization.

## Exact finite-temperature budget `[PROVED HERE]`

For running odds `a=qe^{-k}`, P-G47 turns the interior defect into

\[
 W=\frac{a(T-1)^2}{(T+a)^2}.
\tag{3}
\]

Define co-Poisson complement `H=a-W`.  Exact algebra gives

\[
 \boxed{
 H(a,T)=\frac{a(1+a)(2T+a-1)}{(T+a)^2}>0
 }
 \qquad(a>0,T>1).
\tag{P-G48b}
\]

Thus

\[
 \mathcal C_p(1+x\epsilon)+W_p=-H_p<0.
\tag{4}
\]

The independently created opposite principal symbol exists, but it over-cancels every finite
cell by exact positive amount `H`.  At fixed boundary coordinate, `H→0` as `T→∞`; only frozen
cold boundary attains complete principal cancellation.

## Global gain `[PROVED HERE]`

If `0<a≤1` and `T>1`,

\[
 0<H(a,T)\le \frac{4a}{T}.
\tag{5}
\]

For literal source parameters `T=p^{delta epsilon}` and
`a=p^{-(1+x epsilon)}`,

\[
 0<H_p\le4p^{-(1+(x+delta)\epsilon)}.
\tag{6}
\]

Hence `\sum_p H_p<\infty` for every `x≥0`, `delta>0`, `epsilon>0`.  P-G48 removes Route P's
non-summable harmonic principal class coefficientwise using an actual pre-existing source current.
Remaining obstruction is strictly smaller: positive trace-class midpoint-order complement.

## Conjecture loop verdict

### Conjecture P-G48.A

Primitive Gamma/co-Poisson principal symbol might annihilate whole Julia defect.

**Failed, with exact survivor.** `(P-G48b)` proves finite complement is strictly positive.  This is
not old fixed-principal polarity no-go: the source current has correct running grade and cancels
harmonic class.  Failure is finite-temperature, not principal-class.

### Higher universal principle

P-G45 peak cascade, P-G46 wall freezing, and co-Poisson primitive are one conservative charge
budget.  Running charge `a` splits into Julia defect `W` and positive complement `H`; thermal flow
redistributes charge but does not annihilate it.  Repeated source constructions stalled because
they discovered different coordinates of this same conserved positive budget.

Required new theorem is now narrower: identify `H`, not `1/p`, with an independently signed
archimedean/Gamma or prime-power boundary and prove its completed sum vanishes before positive
completion.  Since `H` is summable, weak-Hilbert and harmonic principal-class barriers no longer
apply.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  HedenmalmThetaMobiusPoleUnitPrimeCellCoPoissonBudget.lean
```

Key declarations:

- `eulerGammaCoPoissonPrimitiveTerm_prime_runningOdds`;
- `thermalBernoulliCoPoissonComplement_eq`;
- `thermalBernoulliCoPoissonComplement_pos`;
- `eulerGammaCoPoissonPrimitiveTerm_add_boundaryLayerDefect`;
- `thermalBernoulliCoPoissonComplement_le_four_mul_div`;
- `prime_thermalBernoulliCoPoissonComplement_le`;
- `summable_prime_thermalBernoulliCoPoissonComplement`.

## Next hard gate

Expand or transform `H_p` through the full divided-log prime-power current.  Test whether its exact
prime-power series is a Gamma/co-Poisson coboundary, an archimedean pole-unit derivative, or a new
positive obstruction.  No post hoc definition of `-H_p` counts.

## Log

- 2026-08-12 — found existing primitive co-Poisson term supplies exact negative running odds;
  derived positive complement factorization, thermal gain, and unconditional all-prime summability;
  Lean module started.
