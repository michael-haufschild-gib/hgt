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
- **Strongest positive survivor:** Any iterative edge argument must prove positivity of the
  residual through a localized moment functional—equivalently, signs after applying an
  edge-annihilating (Christoffel) polynomial.  Raw diagonal signs contain enough information for
  one edge detection but not for deflation.  For an edge value `r`, the first nontrivial producer
  has shape
  \[
    \operatorname{Re}(m_{n+2}-2r m_{n+1}+r^2m_n)\ge0,
  \]
  rather than another copy of `Re m_n ≥ 0`.
- **New insight:** Diagonal resolvent positivity is a one-shot edge certificate.  Frankenstein
  route must weld arithmetic/source geometry to a dynamically localized principal-ideal sign
  law.  This is narrower than assuming full Hankel PSD but strictly stronger than diagonal
  positivity; it identifies exact missing transport from a certified edge to its complement.
- **Status:** Countermodel proved on paper and in axiom-clean Lean in
  `formal/GaloisForLFunctions/RHTower/XiResolventDiagonalDeflationNoGo.lean`.  Localized-sign
  producer remains open and must be source-derived; target-pulled selection of an Xi zero is not
  acceptable.

## Log

- 2026-08-11 — Iterated diagonal-edge conjecture attacked and falsified.
- 2026-08-11 — Exact reflection-compatible countermodel formalized; localized/Christoffel
  positivity extracted as strongest positive survivor.
