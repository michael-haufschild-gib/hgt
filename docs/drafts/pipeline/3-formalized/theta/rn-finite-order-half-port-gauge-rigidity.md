# RN: finite-order rigidity of the exact theta half-port

- **ID:** RN-G-2
- **Stage:** 3-formalized
- **Type:** positive uniqueness classification
- **Route:** RN
- **Status:** PAPER PROVED; LEAN CHECKED; NOT AN RH PROOF
- **Date:** 2026-10-01
- **Source:** the literal theta half-port and current corpus; no numerical experiments.

## Statement

Let `K(w)=thetaHalfLaplace w` and `F#(w)=conj(F(-conj w))`.
Every zero-free entire function `g` of finite order satisfying

    g K + (g K)# = K + K#

is identically one. The previous corpus theorem required finite exponential
type. The new theorem permits arbitrary finite order and derives the stronger
growth restriction from the exact symmetrization identity.

This is a theorem about the stated gauge class. It assumes neither RH nor
simplicity or critical-line location of all Xi zeros. It does not construct a
positive spectral transport or exclude any off-axis Xi zero.

## Proof

Set `H=K#=K(-·)` and `X=K+H`. Source decay bounds `K` uniformly in the
closed left half-plane. In the right half-plane, `K=X-H`; the known `r log r`
envelope of `X(w)=xi(1/2-w)` therefore bounds `K` too.

Finite-order zero-free Hadamard factorization supplies polynomials `P,Q` with
`g=exp(P)` and `g#=exp(Q)`. Define

    U=P'K+K',  V=Q'H+H',
    W=UH-KV,   N=X'H-XV.

Differentiating `gK+g#H=X` gives `gU+g#V=X'`. Elimination yields the exact
entire identity `N=gW`. Polynomial multiplication, differentiation, products
and sums preserve the `exp(C(1+r)log(2+r))` envelope; hence `N,W` have it.

The corpus proves existence of a positive simple critical Xi zero. At its
point `w=i gamma`, `X=0`, `X'=-i Xi'(gamma)!=0`, and `H!=0` by causal
half-port nonvanishing. Thus `N(w)=X'(w)H(w)!=0` and `W` is not identically
zero. This uses one certified simple zero, not a universal simplicity premise.

The quotient proximity inequality bounds `m(r,g)` by `m(r,N)+m(r,W)+O(1)`.
The zero-free Poisson estimate gives
`log|g(z)| <= 3 m(2(1+|z|),g)`. Consequently `g` itself has an `r log r`
envelope. The corpus's subquadratic zero-free factorization gives
`g(z)=g(0)exp(bz)`. The existing finite-exponential-type theta gauge rigidity
then proves `g=1`.

## Lean certificate

- `HTGeometry/OrderOneEntireQuotient.lean`:
  `OrderOneEnvelope.of_entire_quotient`, with polynomial and derivative closure.
- `HTGeometry/OrderOneEntireUnitEquation.lean`:
  `orderOneEnvelope_of_finiteOrder_unit_equation` proves the elimination step
  for general entire order-one coefficients.
- `RHTower/ThetaHalfLineFiniteOrderGauge.lean`:
  `thetaHalfLaplace_finiteOrder_gauge_eq_one` specializes it to the literal
  theta half-port.

Each leaf passed `lake env lean <leaf>`. Necessary targeted `lake --old build
<module>` commands passed. All three leaves are wired into their area umbrellas;
no umbrella or full build was run. New leaves produced no Lean warnings.

The `/tmp` scratch axiom audit passed for all three main declarations:
`[propext, Classical.choice, Quot.sound]` only. No added axioms or `sorryAx`.

Repository lint ran and failed on ten other modules missing umbrella imports:
`CCMApertureChainProfile`, `CCMApertureTranslationChains`,
`CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
`CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
`MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`,
`ThetaMovingShellFirstOrderPhase`, `ZetaZeroDensityPowerSaving`.
No lint error named a new leaf. Concurrent work was preserved.

## Frontier consequence

Finite-order entire scalar normalization cannot repair RN's half-port phase.
The exact positive survivor is uniqueness of that normalization throughout
the finite-order class. Unrestricted-growth gauges remain unclassified here.
The RH-strength open problem remains arithmetic phase-level confinement or
divisor-faithful singular transport; the present theorem does not settle it.
