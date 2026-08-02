# Route E depth-zero prime-clock phase-node no-go

- **ID:** ROUTE-E-DEPTH-ZERO-PHASE-NODE-NOGO
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), Lean proof pending final audit
- **Source:** `OPEN-SOURCE-001`; updated modular-superselection equations (6.61d)--(6.61e)
- **Statement:** Canonical all-prime depth-zero Route E current is nonzero modulo finite-prime
  Euler rays and cannot be a phase-node multiplier at any nonzero carrier frequency.

## Goal

Determine whether phase-node singular escape left by signed scalar screening can supply missing
Route E breadth orientation after positive valuation depths have been removed at critical cost.

## Gates

- [x] 0 → 1 in-progress: source-pure profile and exact prime-clock quotient identified
- [x] 1 → 2 fully-proven: dependency-closed paper proof below
- [ ] 2 → 3 formalized: targeted module build and axiom audit
- [ ] 3 → 4 publication-ready: external priority audit and integration in paper

## Theorem `[PROVED HERE]`

Let
\[
 d(p,e)=
 \begin{cases}
 p^{-1/2},&e=0,\\
 0,&e\geq1,
 \end{cases}
\]
on prime-power coordinates \((p,e)\).  Let \(\mathcal A_{\rm fin}\) be profiles active on only
finitely many prime rays and \(\mathcal Q=\mathcal A/\mathcal A_{\rm fin}\).

1. \([d]\ne0\) in \(\mathcal Q\).
2. For every \(u\ne0\), \(d\) is not supported on the phase-node locus
   \(\sin(u(e+1)\log p)=0\).
3. Consequently no scalar phase-node prime-power source, including an infinite one-prime tower,
   represents the canonical Route E depth-zero current in the global prime-clock quotient.

## Proof

The exact Route E/Gamma depth-zero reduction gives
\[
d(p,0)=p^{-1/2}>0
\]
for every rational prime \(p\).  Hence every prime ray is active.  The prime set is infinite, so
\(d\notin\mathcal A_{\rm fin}\), proving \([d]\ne0\).

Suppose \(u\ne0\) and every active coordinate of \(d\) were a phase node.  The arithmetic
phase-node theorem says active prime-base support is subsingleton: if distinct primes \(p,q\)
were active, then
\[
u\log p=m\pi,\qquad u\log q=n\pi
\]
would produce a nontrivial integer-linear relation between \(\log p\) and \(\log q\), contradicting
unique factorization.  But \(d(p,0)\ne0\) for every prime, contradiction.  Equivalently, the
updated prime-clock quotient theorem puts every phase-node prime-power profile in
\(\mathcal A_{\rm fin}\), whereas \(d\) is not local.

All inputs are exact algebraic/source-identification theorems.  No Möbius cancellation estimate,
zero-free hypothesis, RH implication, boundedness, finite valuation depth, or finite-Rees
assumption enters.

## New scientific knowledge

Route E’s active singularity is not merely “breadth rather than depth.”  Its canonical
depth-zero profile occupies a global prime-clock class disjoint from the entire scalar
prime-power phase-node escape.  Unbounded coefficients, infinite depth, and an infinite
one-prime tower do not repair this mismatch.

This is stronger than either ingredient separately:

- depth-zero reduction alone did not classify singular scalar screens;
- phase-node quotient closure alone did not identify whether Route E’s hard current survived the
  quotient.

Their intersection proves exact source-category separation.

## Survivor

`OPEN-SOURCE-001` remains possible only through a source defined across infinitely many prime
rays before scalarization and outside scalar phase-node prime-power screening.  Live categories
are:

- non-prime-power singular boundary support;
- relation-valued breadth correspondences;
- reflection-breaking pre-scalar transport;
- ordinary-lattice/co-Poisson structure coupling all prime rays coherently.

This theorem removes a proposed source category; it does not prove Möbius cancellation or RH.

## Lean status

Module:
`GaloisForLFunctions/RHTower/MobiusDepthZeroPrimeClockPhaseNodeNoGo.lean`.

Main unconditional theorems:

- `routeEDepthZeroPrimeClockProfile_rayActivity_eq_univ`
- `routeEDepthZeroPrimeClockProfile_not_local`
- `routeEDepthZeroPrimeClockClass_ne_zero`
- `routeEDepthZeroPrimeClockProfile_not_phaseNode`
- `routeEDepthZero_globalSource_phaseNode_separation`

Direct `lake env lean` check passes.  Umbrella is wired.  Targeted module build and axiom audit
remain before Stage 3.

## Novelty audit

Prime-logarithm independence and quotienting by finite ray support are classical ingredients.
Candidate new content is project-specific composition with exact Route E depth-zero divided-log
reduction, yielding disjointness of canonical Route E current from scalar phase-node source class.
External priority remains unverified; claim is limited to this synthesis.

## Log

- 2026-08-01 — extracted after updated modular-superselection paper closed infinite one-prime
  phase-node tower; proved paper theorem and direct Lean module.
