# Finite Liouvillian Hodge--Green law

- **ID:** `finite-liouvillian-hodge-green-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/static-local-complexity-law.md` · O4 fixed-observable audit
- **Statement:** Every finite spectral transition vector is its zero-gap stationary part plus one exact Liouvillian coboundary.

## Goal

Classify every fixed linear observable along autonomous finite-dimensional
Hamiltonian evolution.  This is a route-closing bridge, not a circuit
complexity lower bound.

## Gates

- [x] 0 → 1 in-progress: fixed-observable loophole isolated
- [x] 1 → 2 fully-proven: coordinatewise spectral proof
- [x] 2 → 3 formalized: `transitionGap_hodgeGreen_decomposition`
- [ ] 3 → 4 publication-ready: no standalone novelty claim

## Theorem

Let `E : alpha -> R` be a finite energy family and let `x` be an arbitrary
complex transition vector indexed by pairs `(a,b)`.  Define

\[
 (\Pi_E x)_{ab}=\mathbf 1_{E_a=E_b}x_{ab},\qquad
 (G_E x)_{ab}=\begin{cases}
 0,&E_a=E_b,\\
 x_{ab}/(E_a-E_b),&E_a\ne E_b,
 \end{cases}
\]

and `(L_E y)_(ab)=(E_a-E_b)y_(ab)`.  Then

\[
 L_E\Pi_E x=0,\qquad \Pi_E x+L_EG_E x=x. \tag{1}
\]

## Proof

For `E_a=E_b`, the Liouvillian multiplier vanishes and `(1)` reads
`x_(ab)+0=x_(ab)`.  For `E_a != E_b`, the stationary entry is zero and

\[
 (E_a-E_b){x_{ab}\over E_a-E_b}=x_{ab}.
\]

These two exhaustive cases prove both identities coordinatewise.

## Quantum interpretation

In an energy eigenbasis, `L_E` is the commutator with `H`.  For an observable
`W`, set `A=-iG_EW`.  Then

\[
 W=\Pi_HW+i[H,A].
\]

Thus every fixed linear signal is a conserved component plus an exact time
coboundary.  The formal theorem certifies the algebraic decomposition; the
Schrödinger derivative and integrated norm estimate require a separate
calculus formalization before use in a publication claim.

## Lean certificate

- **Module:** `GaloisForLFunctions.HTGeometry.FiniteLiouvillianHodgeGreenLaw`
- **Capstone:** `transitionGap_hodgeGreen_decomposition`
- **Kernel theorem:** `transitionGapLiouvillian_stationaryPart_eq_zero`
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Wiring:** imported by `GaloisForLFunctions.HTGeometry`
- **Audit:** `lake build GaloisForLFunctions.HTGeometry.FiniteLiouvillianHodgeGreenLaw` passed

## Hostile audit

- This does not bound `||G_EW||` uniformly in system size; small spectral gaps
  may make the primitive enormous.
- It excludes a persistent certificate based on one fixed linear observable,
  not a time-dependent support function, adaptive witness, or replica
  statistic.
- It supplies no anti-concentration, circuit-union estimate, shortcut-locus
  packing bound, or complexity growth law.
- No novelty is claimed for the finite spectral decomposition itself.  Its
  value is exact classification of a tempting but inert O4 witness class.

## Log

- 2026-08-04 — Extracted from Hellinger--Hodge--Green transfer audit; paper proof and Lean formalization completed, module built, axioms audited.
