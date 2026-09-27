# All-prime equal-depth Gamma-to-Stokes pair bridge

- **ID:** `stc-all-prime-gamma-stokes-pair-bridge`
- **Stage:** 3-formalized
- **Type:** exact source transport and nonseparable calibration law
- **Routes:** STC, RHist, Gamma-six/Sonin
- **Status:** `[PROVED ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]`

## Source and target

For prime `p` and valuation depth `e≥0`, let

```text
i_p=(p,e),  n=e+1,
B_p=xiGammaEulerPrimitiveBoundaryAmplitude 0 i_p >0,
H_p=xiGammaEulerBoundaryHalfHeight p e = n log(p)/2.
```

The literal promoted Gamma source already defines an exterior for
arbitrary prime-power cells in
`CCMFirstClockPrimitivePromotedExteriorSource.lean`. Its modular rate
is `r_p=-2H_p=-n log(p)`. At one **common** local grade
`α=g/(2n)` for all equal-depth primes, its reflection-odd pair value is

```text
S_pq,e(g) = B_p B_q (H_p-H_q) sinh[α(r_p+r_q)]
          = -B_p B_q (H_p-H_q) sinh[g(log p+log q)/2].       (1)
```

The independently defined analytic Stokes scalar is

```text
c_pq(g)=-2 sinh[g(log p+log q)/2] G_pq(g),
G_pq(g)=R_pq(g)+R_pq(g)⁻¹>0.                              (2)
```

## Theorem: division-free all-prime pair calibration

For every `p,q,e,g`, equations (1) and (2) give

```text
2 G_pq(g) S_pq,e(g) = B_p B_q (H_p-H_q) c_pq(g).          (3)
```

For `p<q`, define the **source-only, grade-independent** calibration

```text
K_pq,e = B_p B_q (H_q-H_p)/2 > 0.
```

Then (3) becomes

```text
G_pq(g) S_pq,e(g) = -K_pq,e c_pq(g).                      (4)
```

This extends the fixed `(2,3)` positive scalar transport to every
ordered prime pair and every equal valuation depth. The proof uses
the actual source amplitudes and modular rates; it does not define
a fitted source from the target. It is formalized in
`DeningerGammaAllPrimeStokesPairBridge.lean`.

The same Lean leaf identifies the underlying symmetric kernel
`Q_pq=B_p B_q sinh[g(log p+log q)/2]` and proves
`S_pq,e=-(H_p-H_q)Q_pq`. Its hyperbolic addition formula gives a
two-channel one-prime factorization of `Q`. Thus the bridge is an
entrywise prime-height commutator equation. The separate paper theorem
in `stc-prime-height-commutator-calkin-ghost.md` shows why this
commutator has no general Calkin-faithful inverse.

## The calibration is intrinsically pairwise

For `p<q<r<s` at the same depth,

```text
K_pq,e K_rs,e < K_pr,e K_qs,e.                           (5)
```

The positive amplitudes and the common factor `n/4` cancel from the
comparison. For `x<y<z<w`, the remaining strict inequality is

```text
(y-x)(w-z) < (z-x)(w-y),
(z-x)(w-y)-(y-x)(w-z)=(z-y)(w-x)>0.
```

Consequently `K_pq,e` cannot equal `a_p a_q` on all pairs for any
one-prime weights `a_p`; the four primes `(3,5,7,11)` already refute
that rank-one form. The Lean leaf proves the corresponding prime-log
gap obstruction. Equation (4) requires an actual pair calibration,
not a diagonal rescaling of two one-prime sections.

For distinct close primes,

```text
K_pq,e/(B_p B_q) = n log(q/p)/4.
```

For each fixed `e` this normalized calibration has infimum zero over
`p<q`: the relative prime-gap consequence `prime_between` in
`GaloisForLFunctions/PNTPlus/Consequences.lean` gives arbitrarily
large `p<q<(1+ε)p` for every `ε>0`. Thus solving (4) for `c_pq`
entails an unbounded divided-difference factor
`1/(H_q-H_p)` after the critical amplitudes are removed. The exact
operator domain, continuity or singular price, and Calkin control
must be proved from the source; they do not follow from (4).

## Relation to the rank obstruction

At any common local grade the raw modular source exterior is a wedge
of two one-prime sections, hence has matrix rank at most two. Its
reflection-odd part is the difference of two such wedges, hence rank
at most four on every finite packet. One-prime diagonal rescaling
preserves that bound. By contrast, the direct ordered all-pair
analytic Stokes kernel has unbounded rank at every fixed nonzero grade,
as proved in `stc-ordered-curvature-unbounded-rank.md`. Therefore a
source-to-target identification on all pairs cannot be a global
scalar times independent one-prime rescalings of the literal
reflection-odd exterior. The pair calibration in (4) is exactly
where that finite-rank restriction is escaped.

This does **not** identify the cofinal Sonin operator or prove its
sub-root Calkin growth on actual Xi zeros. That source-to-operator
step remains the RH-producing obligation.

## Audit

- The all-prime source exterior and its rate-height identity are in
  `CCMFirstClockPrimitivePromotedExteriorSource.lean`.
- Exact reflected hyperbolic form is in
  `GammaCoorientedPositiveConeNoShorting.lean`; analytic target form
  is in `RouteRCrossPrimeStokesCalkinPolarHandoff.lean`.
- The known `(2,3)` instance is in
  `DeningerGammaSixCofinalFullGradeSoninTransport.lean`.
- Deep corpus searches found these ingredients but not equation (3)
  for arbitrary equal-depth prime pairs. Results were partial;
  external priority is not claimed.

## Log

- 2026-09-27: every displayed theorem formalized unconditionally; certificate `stc-all-prime-gamma-stokes-pair-bridge-formalized.md`; moved to stage 3.
