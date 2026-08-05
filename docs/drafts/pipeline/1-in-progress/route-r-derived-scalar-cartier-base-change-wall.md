# Route R derived scalar Cartier base-change wall

- **ID:** `route-r-derived-scalar-cartier-base-change-wall`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); Lean verification pending
- **Source:** Route R rational Cartier prime-dilation landing
- **Statement:** Scalar specialization of the neutral Cartier atom is contractible at every
  nonneutral prime-dilation character, so ordinary derived scalar base change cannot produce the
  retained physical Xi lift.

## Goal

Hostile-test the proposed derived-support resolution of Route R's open Cartier comparison. The
test must distinguish a genuine singular producer from a derived reformulation of the already
known critical-line detector.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and exact scalar model frozen
- [x] 1 → 2 fully-proven: complete algebraic proof below
- [ ] 2 → 3 formalized: targeted Lean verification, axiom audit, lint, and umbrella build pending
- [ ] 3 → 4 publication-ready: not intended as standalone publication

## Frozen conjecture and attack

**[CONJECTURE DSC-1 — falsified as a producer].** Fixed physical Xi conormal at every Xi divisor
is a nonzero derived scalar fibre of the universal neutral Cartier atom

\[
  K(q-1)=[R\xrightarrow{q-1}R],\qquad R=\mathbb Q[q,q^{-1}],
\]

under specialization `q ↦ g_(p,rho)=p^(2 Re(rho)-1)`.

The conjecture was motivated by three exact shadows: pre-divisor variable-grade Bockstein is a
literal boundary, its fixed-Xi specialization is explicit central Bockstein, and retained cyclic
source atom has period one. It predicts that derived `Tor`, rather than an underived quotient,
retains the atom without postulating `K=0`.

**Hostile scalar test.** After scalar specialization, complete two-term complex is

\[
  K_g=[\mathbb C\xrightarrow{g-1}\mathbb C].
\]

If `g != 1`, multiplication by `g-1` is invertible and

\[
  h_g(z)=(g-1)^{-1}z
\]

is a two-sided contracting homotopy. Therefore every homology group vanishes. If `g=1`,
differential is zero, degree-zero unit class is nonzero, and degree-one unit is closed.
Consequently

\[
  H^\bullet(K_g)\ne0\iff g=1.
\]

For actual prime character,

\[
  g_{p,\rho}=1
  \iff \Re\rho=\tfrac12
  \iff K_{p,\rho}=0.
\]

Thus derived scalar non-erasure is already RH-bearing conclusion. Derived language alone does not
construct it.

## No-go closure

- **Exact killing theorem/mechanism:** whenever physical target makes `q-1` act by nonzero scalar
  `g_(p,rho)-1`, its inverse contracts entire derived Cartier fibre. Adding higher derived/Tor
  vocabulary cannot retain a class.
- **Strongest positive survivor:** successful producer must be genuinely singular and non-scalar
  before fixed-fibre specialization. It must transport retained class through a relation-kernel,
  compact-support, or non-exact realization in which central element is not yet a unit, and only
  afterward compare with fixed Xi conormal. Ordinary exact `R`-linear base change to scalar
  character is excluded.
- **New insight:** Route R does not merely need a derived version of its current comparison. It
  needs failure of scalar base-change exactness with a separately proved non-erasure theorem. This
  narrows singular Cartier comparison category.
- **Status:** paper proof dependency-closed. Lean module
  `RouteRDerivedScalarCartierBaseChangeWall.lean` added; final verification pending.

## Formal theorem surface

Module constructs scalar differential, explicit contracting homotopy, degree-zero quotient atom,
degree-one kernel atom, normalized atom landing, and actual Xi specialization. It proves:

- contractibility iff `g != 1`;
- two-sided atom survival iff `g=1`;
- normalized landing injectivity iff `g=1`;
- actual Xi contractibility iff Hodge-mate coefficient is nonzero;
- global scalar derived non-erasure iff RH.

## Literature discrimination

Central-element categorical Bockstein of arXiv:2605.02129 and explicit Tor cycle of
arXiv:2607.06279 justify universal two-term model, but neither changes scalar contraction after
`g-1` becomes a unit. Chern–Simons filtered two-sign obstruction of arXiv:2607.12768 is only an
analogy for retaining both orientations; it provides no arithmetic realization or Xi comparison.

## Log

- 2026-08-05 — `DSC-1` frozen, attacked, and falsified as independent producer; exact contraction
  and strongest singular/non-scalar survivor proved.
