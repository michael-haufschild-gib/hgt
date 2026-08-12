# Xi resolvent diagonal edge deflation no-go

- **ID:** xi-resolvent-diagonal-edge-deflation-no-go
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · diagonal resolvent edge opportunity
- **Statement:** Nonnegative diagonal resolvent moments are not preserved after subtracting a certified positive maximal-modulus atom, even for a strict-smaller reflection-conjugate remainder.

## Goal

Test whether `XiResolventDiagonalEdgeDetection` can be iterated: detect one critical-line edge
copy from diagonal moment signs, remove that atom, and reapply the theorem until every Xi divisor
copy is forced onto the line.  This would have converted a much thinner arithmetic producer than
full Hankel positivity into RH.

## Gates

- [x] 0 → 1  in-progress: source-pure induction mechanism isolated and hostile-tested
- [ ] 1 → 2  fully-proven: route falsified instead; exact no-go and positive survivor proved
- [x] 2 → 3  formalized: Lean module `XiResolventDiagonalDeflationNoGo`
- [ ] 3 → 4  publication-ready: not applicable to the false conjecture

## Approach

Use the smallest reflection-compatible spectral model with a positive real edge atom and a
strict-smaller off-axis conjugate pair.  The model

\[
  m_n=1+(i/4)^{n+1}+(-i/4)^{n+1}
\]

has `Re m_n > 0` for every `n`: the pair contributes real part of absolute value at most `1/2`,
so the edge atom masks it.  After deleting the certified edge atom `1`, however, the residual
degree-one moment is

\[
  \operatorname{Re}\bigl((i/4)^2+(-i/4)^2\bigr)=-1/8<0.
\]

The diagonal sign hypothesis is therefore non-hereditary under atom subtraction.

## No-go closure

- **Exact killing theorem/mechanism:** Positive edge atoms can mask all diagonal oscillation of a
  smaller reflection-conjugate off-axis pair.  `exists_reflectionConjugate_diagonalMomentPositive_not_deflationStable`
  gives an unconditional counterexample; ordinary edge subtraction destroys moment
  nonnegativity.
- **Strongest positive survivor:** Raw diagonal signs contain enough information for one edge
  detection but not for deflation.  Two exact repairs survive.  An iterative argument must prove
  positivity of the residual through an edge-annihilating Christoffel polynomial, whose first
  nontrivial producer has shape
  \[
    \operatorname{Re}(m_{n+2}-2r m_{n+1}+r^2m_n)\ge0,
  \]
  rather than another copy of `Re m_n ≥ 0`.  Better, a non-iterative repair is now proved: weight
  every divisor copy by bounded nonlinear Wold polar work `W/(1+W)`, which is positive exactly off
  line.  One weighted edge detection then kills the whole off-line carrier without subtraction.
- **New insight:** Diagonal resolvent positivity is a one-shot edge certificate, so successful
  Frankenstein use must alter the carrier before edge detection rather than alter moments after
  it.  `SourceHorizontalWoldResolventEdge.lean` implements the coefficient-faithful repair and
  reduces RH to signs of one full-divisor weighted diagonal sequence.  Missing transport is now a
  pre-zero Euler--Green/Wold functional-calculus trace identity, not edge deflation.
- **Status:** Countermodel proved on paper and in axiom-clean Lean in
  `formal/GaloisForLFunctions/RHTower/XiResolventDiagonalDeflationNoGo.lean`.  The one-shot weighted
  repair and its RH endpoint are proved in `SourceHorizontalWoldResolventEdge.lean`.  Its pre-zero
  trace/sign producer remains open; target-pulled Xi selection is not acceptable.

## Log

- 2026-08-11 — Iterated diagonal-edge conjecture attacked and falsified.
- 2026-08-11 — Exact reflection-compatible countermodel formalized; localized/Christoffel
  positivity extracted as initial positive survivor.
- 2026-08-11 — Positive survivor strengthened: bounded Wold-weighted one-shot edge collapse proved
  in Lean, eliminating need for deflation; source trace/sign producer remains open.
