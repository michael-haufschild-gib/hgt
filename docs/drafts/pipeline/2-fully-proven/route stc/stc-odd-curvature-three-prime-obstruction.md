# Three-prime obstruction to direct all-pair Stokes-curvature gluing

- **ID:** `stc-odd-curvature-three-prime-obstruction`
- **Stage:** 2-fully-proven (paper)
- **Type:** FALSIFIED direct-gluing conjecture; positive triangle-charge theorem
- **Routes:** STC, cross-prime Gamma-six/Sonin source lift
- **Status:** `[PROVED HERE ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]`

## Exact question and scope

The canonical STC prime seam in `SoninPrimeSeamExteriorCalkin.lean`
uses two one-particle sections, one universal. Its ordered pair
coefficient is `a_p-a_q`. Therefore any proposed scalar coefficient
`C_pq` assigned to every ordered pair must obey

```text
C_pq + C_qr - C_pr = 0                 (p<q<r).       (1)
```

The corpus defines, for every `p,q>1`, the reflection-odd scalar
`c_pq(g)=routeRCrossPrimeStokesOddCurvature p q g`. The target-free
Gamma-six/Sonin **operator** lift is calibrated to the fixed pair
`(2,3)` in `DeningerGammaSixTargetFreeSoninExteriorLift.lean`. The
separate all-prime scalar source calibration in
`stc-all-prime-gamma-stokes-pair-bridge.md` does not supply such an
operator lift. Test the direct-gluing conjecture
that the same analytic formula `c_pq(g)` can be used as the canonical
seam coefficient for every `p<q`.

## Theorem: nonzero triangle charge

For the three primes `(3,5,7)`, set

```text
Ω(g) = c_35(g) + c_57(g) - c_37(g).
```

Then

```text
lim_(g→0) Ω(g)/g < -(log 3)/2 < 0.                (2)
```

Hence `Ω(g)≠0` for all sufficiently small nonzero real `g`, with
sign opposite to `g`. The direct-gluing conjecture is false near the
neutral grade. In particular, no prime potential `a_p(g)` can satisfy
`c_pq(g)=a_p(g)-a_q(g)` simultaneously for these three pairs there.

## Proof

Write `x=log p`, `y=log q`. The exact corpus definitions are

```text
S(t)=sinh(t)/t, with S(0)=1,
R_pq(g)=(y/x) S(gy/2)/S(gx/2),
c_pq(g)=-2 sinh(g(x+y)/2) [R_pq(g)+R_pq(g)^(-1)].
```

Since `S(t)→1` at zero, `R_pq(g)→y/x`. Since
`sinh(gt)/g→t`, one obtains the exact neutral-grade slope

```text
lim_(g→0) c_pq(g)/g = -f(x,y),
f(x,y)=(x+y)(y/x+x/y).                        (3)
```

Put `x=log 3`, `y=log 5`, `z=log 7`. Elementary order gives
`0<x<y<z<2x`, the last inequality being `7<3²`.
For positive `u,v`, the arithmetic-geometric mean inequality gives
`f(u,v)≥2(u+v)`. Thus `f(x,y)>4x` and `f(y,z)>4x`.
On the other hand, `1<z/x<2`, and for `1≤t≤2`,

```text
t+1/t≤5/2,
```

because `2t²-5t+2=(2t-1)(t-2)≤0`. Therefore
`f(x,z)<(3x)(5/2)=15x/2`. Combining these inequalities yields

```text
f(x,y)+f(y,z)-f(x,z) > x/2.
```

Equation (3) now proves (2). The potential identity (1) would force
`Ω(g)=0`, contrary to (2).

## Positive survivor and route consequence

The **triangle charge** `Ω` is a gauge-invariant obstruction under
one-particle potential changes: replacing each pair coefficient by
`C_pq+(b_p-b_q)` leaves `C_35+C_57-C_37` unchanged. Any all-pair
source calibration that starts with the analytic `c_pq` and lands in
the canonical STC seam therefore needs an additional pair correction
`B_pq` satisfying the exact three-prime compensation law

```text
B_35(g)+B_57(g)-B_37(g) = -Ω(g).                  (4)
```

The correction cannot itself be a potential difference. It must
come from new joint source data, a genuinely changed pair calibration,
or a different exterior architecture. This identifies a
specific missing *three-prime* compatibility condition before any
cofinal Calkin estimate can close STC.

This theorem does **not** say an all-prime Gamma/Sonin operator seam
has coefficients `c_pq`. The source has an all-pair **scalar** bridge,
but its nonseparable height-gap calibration still has to be lifted to
an operator and controlled in the Calkin quotient. This kills direct
copying into the current canonical seam, not STC or RH.

## Audit and formalization

- Exact definitions and polar identity:
  `RouteRCrossPrimeStokesCalkinPolarHandoff.lean`.
- Canonical coboundary form:
  `SoninPrimeSeamExteriorCalkin.lean`.
- Fixed-pair source calibration:
  `DeningerGammaSixTargetFreeSoninExteriorLift.lean`.
- The current deep corpus search was partial and found the endpoint
  ingredients, but no theorem asserting or refuting this exact
  three-prime direct gluing. External priority is not claimed.
- [x] Dependency-closed paper proof of (2) and the invariant (4).
- [x] Formalized the neutral-grade slope, strict triangle sign,
  punctured-neighborhood nonvanishing, and impossibility of a
  three-prime potential in
  `RouteRCrossPrimeStokesFourChannelObstruction.lean`; wired into
  `GaloisForLFunctions/RHTower.lean` without an umbrella build.
