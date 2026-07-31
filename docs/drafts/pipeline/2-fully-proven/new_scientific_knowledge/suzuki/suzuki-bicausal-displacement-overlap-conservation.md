# Displacement--overlap conservation for bicausal tilted-tent transport

- **ID:** suzuki-bicausal-displacement-overlap-conservation
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL LAW / SHARP TRANSPORT FRONTIER
- **Status:** `[PAPER PROVED] [LEAN PENDING]`

## Theorem A: displacement--overlap conservation

Let `h>0` and `a<=s`, `s+h<=b`. Put

```text
L=(a,s+h],   R=(s,b],   U=(a,b],   O=(s,s+h].
```

Then

```text
L union R = U,   L intersection R = O.                         (1)
```

For every function `Phi` interval-integrable on `(a,b]`,

```text
integral_a^(s+h) Phi + integral_s^b Phi
  = integral_a^b Phi + integral_s^(s+h) Phi.                   (2)
```

In particular the overlap has Lebesgue measure exactly `h`.

### Proof

For the intersection, `x` belongs to both targets exactly when

```text
a<x<=s+h  and  s<x<=b.
```

Since `a<=s` and `s+h<=b`, this is equivalent to `s<x<=s+h`. For the union, let
`a<x<=b`. If `x<=s+h`, then `x` lies in `L`; otherwise `s+h<x`, hence `s<x`, and
`x` lies in `R`. Reverse inclusions are immediate. This proves `(1)`.

Split both interval integrals at `s` and `s+h`:

```text
integral_a^(s+h) Phi + integral_s^b Phi
= (integral_a^s Phi + integral_s^(s+h) Phi)
  + (integral_s^(s+h) Phi + integral_(s+h)^b Phi)
= integral_a^b Phi + integral_s^(s+h) Phi.
```

The last assertion follows from `volume((s,s+h])=(s+h)-s=h`. No limiting or
arithmetic input occurs. QED.

### Transport consequence

A cumulative-mass partition translated by `h` on the increasing side and left unshifted on the
decreasing side therefore has target multiplicity two on an interval of width exactly `h`.
The same displacement that makes each one-sided monotonicity comparison valid is conserved as
duplicate target capacity at the reversal. A capacity-one splice exists only if accumulated
one-sided slack pays the extra integral in `(2)`.

For the sharp Suzuki--Mangoldt cells, `h=2`. For the repository's unconditional cells, past
coordinates are shifted by `-R` and future coordinates by `R+2`; their relative displacement and
therefore their aggregate overlap width are both `2R+2`, exactly
`mangoldtLogHaarTransportWidth`.

## Theorem B: bilateral tilted-tent surplus transform

Let `beta`, `L` be positive. On `[-L,L]` define

```text
r_(beta,L)(x)=exp(beta*x)*(1-|x|/L).
```

Then

```text
integral_(-L)^L r_(beta,L)(x) dx
  = 2*(cosh(beta*L)-1)/(L*beta^2),                              (3)
```

and the Suzuki-lag two-flank deficit is

```text
D(beta,L)
 := 2*integral_(-L)^L (1-r_(beta,L)(x)) dx
  = 4L - 4*(cosh(beta*L)-1)/(L*beta^2).                        (4)
```

### Proof

On the left half, `|x|=-x`; on the right half, `|x|=x`. Antiderivatives are

```text
A_-(x)=exp(beta*x)*((1+x/L)/beta - 1/(L*beta^2)),
A_+(x)=exp(beta*x)*((1-x/L)/beta + 1/(L*beta^2)).
```

Direct differentiation gives

```text
A_-'(x)=exp(beta*x)*(1+x/L),
A_+'(x)=exp(beta*x)*(1-x/L).
```

Endpoint evaluation yields

```text
integral_(-L)^0 exp(beta*x)*(1+x/L) dx
  = (beta*L-1+exp(-beta*L))/(L*beta^2),

integral_0^L exp(beta*x)*(1-x/L) dx
  = (exp(beta*L)-beta*L-1)/(L*beta^2).
```

Adding cancels the two linear terms. Since
`exp(z)+exp(-z)=2*cosh(z)`, `(3)` follows. Also
`integral_(-L)^L 1 dx=2L`; multiplying the difference by the lag Jacobian `dt=2dx`
gives `(4)`. QED.

## Theorem C: strict critical seam excess

At the Suzuki critical tilt and width,

```text
D(1/2,2)=16-8*cosh(1)>2.                                      (5)
```

### Proof

Substitution in `(4)` gives the identity. The toolchain's unconditional bounds

```text
exp(1)  < 2.7182818286,
exp(-1) < 0.3678794412
```

imply

```text
2*cosh(1)=exp(1)+exp(-1)<3.0861612698<7/2.
```

Thus `cosh(1)<7/4`, so `16-8*cosh(1)>16-14=2`. QED.

## Sharp interpretation and non-overclaim

Theorem A proves that common-shift bicausal transport always pays its displacement back as seam
overlap. Theorem C proves that the complete *continuum* critical tilted tent has enough total
two-flank surplus to pay the sharp width-two seam. Therefore geometry alone does not kill the
Suzuki positive-transport program.

Capacity-band data alone still cannot force that surplus for an arbitrary atomic source: an
admissible partition can concentrate a full width-two atom at the strict apex and have no flank
mass. This is an information no-go for capacity-only arguments, not an actual-von-Mangoldt upper
obstruction and not a no-go theorem for all Suzuki methods.

The exact source frontier is now the actual-Mangoldt realization and disjoint assignment of the
critical surplus. Under weighted Mangoldt weak convergence its normalized value tends to `(5)`;
that asymptotic is classical rather than novel and is not counted as proved here until its full
dependency is present in Lean.

## 2026-07-22 hostile correction: total apex deficit is not splice slack

The final interpretation above is insufficient and its proposed payment inference is retired.
The exact no-free-splice theorem proves

```text
mixed target - source quadrature - duplicate seam
  = capacity-one target - source quadrature.
```

For the continuum source, one-sided transport slack equals duplicate seam mass exactly, leaving
zero net margin for every profile.  Therefore `(5)` does not pay the seam: it is total deficit
from the apex, not transport slack.  Actual-Mangoldt weak convergence approaches this critical
continuum equality and supplies no positive sign by itself.

Correction and positive survivor:
`suzuki-bicausal-no-free-splice-classification.md`.  Failed inference:
`../../5-failed/suzuki-continuum-two-flank-surplus-pays-bicausal-seam.md`.

## Lean status (verified 2026-07-24)

All three proven theorems are formalized unconditionally and committed (axiom-clean, in the built umbrella):
- **Theorem A** (eq. 1–2): `GaloisForLFunctions.HTGeometry.BicausalDisplacementOverlap` —
  `bicausalLeftTarget_inter_rightTarget`, `bicausalLeftTarget_union_rightTarget`,
  `volume_bicausalSeam`, `bicausal_intervalIntegral_conservation`.
- **Theorem B** (eq. 3–4): `GaloisForLFunctions.HTGeometry.TiltedTentTwoFlankSurplus` —
  `integral_tiltedTentFullProfile`, `tiltedTentTwoFlankSurplus_eq`.
- **Theorem C** (eq. 5): same module — `tiltedTentTwoFlankSurplus_critical_eq`,
  `cosh_one_lt_seven_div_four`, `tiltedTentTwoFlankSurplus_critical_gt_two`.

The `[LEAN PENDING]` header tag is superseded. The only open item (actual-Mangoldt weak-convergence
realization) is classical, explicitly not counted as a proved-here obligation.
