# Riccati correlation-angle transport

- **ID:** `riccati-correlation-angle-transport`
- **Stage:** 3-formalized
- **Type:** THEOREM / HILBERT CORRELATION GEOMETRY
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [LOCAL-RESEARCH] [NOVELTY UNVERIFIED]`
- **Parent:** `three-point-correlation-angle-subadditivity.md`

## Statement

Let `q:[0,T]->R` be `C^3`, with

```text
q(0)=q'(0)=0,
q(t)>=0,
q(t)>0 for t>0,
2 q'(t)q''(t)-q'''(t)>=0.                               (1)
```

Put

```text
rho(t)=exp(-q(t)),
alpha(t)=arccos(rho(t)).
```

Then `alpha` is concave on `[0,T]`.  In particular, for `x,y>=0` with `x+y<=T`,

```text
alpha(x+y)<=alpha(x)+alpha(y).                           (2)
```

Consequently the normalized ordered three-point correlation matrix with entries

```text
rho(x), rho(y), rho(x+y)
```

is positive semidefinite whenever the correlations are radially ordered.

## Exact transport identity

Define the angle-curvature certificate

```text
C(t)=q'(t)^2-q''(t)(1-exp(-2q(t))).
```

Direct differentiation gives

```text
C'(t)
 =(2q'(t)q''(t)-q'''(t))(1-exp(-2q(t))).                (3)
```

Since `q>=0`, both factors on the right of `(3)` are nonnegative.  The seam data give
`C(0)=0`, hence `C(t)>=0`.

For `t>0`, `0<rho(t)<1`, and two differentiations yield

```text
alpha''(t)
 =-exp(-q(t))*C(t)/(1-exp(-2q(t)))^(3/2)<=0.             (4)
```

Continuity at zero and `(4)` prove concavity on the closed interval.

Because `alpha(0)=0`, concavity gives

```text
alpha(x)>=(x/(x+y))*alpha(x+y),
alpha(y)>=(y/(x+y))*alpha(x+y)
```

when `x+y>0`; adding proves `(2)`.  The zero case is immediate.

## Source interpretation

If `f(t)=exp(-q(t))`, then

```text
f''(t)/f(t)=q'(t)^2-q''(t),
d/dt (f''(t)/f(t))=2q'(t)q''(t)-q'''(t).
```

Thus `(1)` says normalized correlation curvature is nondecreasing.  Identity `(3)` transports
that Riccati/Sturm monotonicity into spherical correlation-angle concavity.  This is the missing
connector between the theta reflected Riccati margin and the existing Castano--Paksoy--Zhang
three-point matrix theorem.

## Hostile checks

1. Merely assuming `q>=0`, increasing, or convex is insufficient; `(3)` uses the third-order
   margin.
2. Positivity of the margin without `q(0)=q'(0)=0` does not fix the sign of `C`.
3. The strict condition `q(t)>0` for `t>0` is needed only to differentiate `arccos(exp(-q))`;
   continuity handles the seam.
4. The theorem proves order-three positivity, not an all-order positive-definite kernel.
5. Applied to a completed theta fibre, it still requires the exact full-source Riccati margin.
   The likelihood cumulant obstruction theorem identifies that remaining source inequality.

## Literature boundary

The parent correlation-angle triangle criterion is the three-by-three specialization of standard
correlation-matrix geometry and the Castano--Paksoy--Zhang metric framework.  Targeted searches
found no source stating the exact transport identity `(3)` or the implication from monotonicity of
`f''/f` to concavity of `arccos f`.  Novelty remains unverified.

## Formalization targets

- `formal/GaloisForLFunctions/HilbertMetric/RiccatiCorrelationAngle.lean`
- theta-cusp specialization in
  `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspReflectedRiccatiAngle.lean`

- [x] certificate derivative identity;
- [x] certificate nonnegativity from Riccati margin;
- [x] angle second-derivative identity;
- [x] closed-interval concavity;
- [x] angle subadditivity;
- [x] three-point PSD via the existing correlation-angle theorem;
- [x] theta single-atom unconditional specialization;
- [x] completed-source correction interface;
- [x] modular-evenness split reducing the global source wall to same-half-line cumulants plus
      seam-crossing angles.
