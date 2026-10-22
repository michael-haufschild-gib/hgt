# Xi-shift tangent stationary-kernel no-go

- **ID:** `xi-shift-tangent-stationary-kernel-no-go`
- **Stage:** 1-in-progress
- **Type:** NO-GO / POSITIVE ROOTED SURVIVOR / RH FRONTIER ROUTING
- **Parents:**
  - `gamma-julia-endpoint-correction-hilbert-schmidt-dressing`
  - `xi-shift-tangent-exterior-cube`
  - `gamma-sewn-xi-shift-tangent-hilbert-kernel`
- **RH used:** no
- **Computation used:** no

## Candidate killed

Let

```text
C(p,q) = gammaSewnXiShiftEndpointUnitTangentKernel p q.
```

This is the normalized all-depth Gram correlation of the completed `+2` Xi-shift tangents.  The
completed physical endpoint kernel is stationary on prime logarithms:

```text
K(p,q) = k(log p - log q).
```

The simplest proposed exterior intertwiner would identify `C(p,q)` with a continuous stationary
kernel `k(log p-log q)`, possibly after one fixed nonzero scalar normalization.

## No-go theorem

There is no continuous `k : Real -> Real` satisfying

```text
k(log p - log q) = C(p,q)
```

for every pair of ordinary primes.

## Dependency-closed paper proof

Write `a=p^-1`, `b=q^-1`.  The closed source formula is

```text
C(p,q)
 = sqrt((1-a^2)(1-b^2))
   * ((1+ab)^2 - 2(a^2+b^2)) / (1-ab)^3.             (ST1)
```

Hence `C(p_j,q_j) -> 1` whenever `p_j,q_j -> infinity`.

Fix any real lag `t`.  Put `eta_j=1/(j+1)`.  The unconditional multiplicative prime-window
theorem supplies arbitrarily large primes with

```text
log q_j in [Y_j,       Y_j+eta_j],
log p_j in [Y_j+t,     Y_j+t+eta_j],
```

after choosing `Y_j` beyond both window thresholds.  Therefore

```text
log p_j-log q_j -> t,
p_j,q_j -> infinity.
```

Continuity and `(ST1)` force `k(t)=1`.  Since `t` was arbitrary, `k` is constant one.

For distinct primes, the normalized tangent features are distinct.  Their squared Hilbert
distance is

```text
2(1-C(p,q)) > 0,
```

so `C(p,q)<1`, contradiction.

## Positive survivor

The source tangent cannot reach the completed response by a pointwise stationary ratio-kernel
identification.  This obstruction is sharp: the exact symmetric rooted quotient is developed in
`xi-shift-rooted-polar-normal-cone.md`.  It proves

```text
pq(1-C(p,q)) -> 10 sinh(t/2)^2
```

at fixed lag `t=log p-log q`, exactly `5/2` times the diagonal-subtracted critical polar kernel at
doubled log nodes.  Its next normal coefficient is `A(40-7A)/8`.

A surviving intertwiner must therefore retain at least one of:

1. an absolute/rooted prime coordinate before stationary completion;
2. a genuinely nonlocal operator mixing prime scales;
3. a connected father/detail or Gamma boundary channel whose removal occurs only after response
   assembly.

This is compatible with the existing rooted-second plus tangent-third decomposition and explains
why projective division or ratio-only sewing loses the required exterior information.

## Relation to positive off-line Euler quartet

`PositivePrimeDensityMobiusInversion.lean` independently proves that positive Euler density,
reflection, entire completion, hypertranscendence, Ward charge, and positive unsquared Cauchy
orientation coexist with an off-line zero.  The present no-go prevents repairing that failure by
equating the positive source tangent Gram directly with the stationary completed response.

## Gates

- [x] exact candidate and falsifier identified
- [x] dependency-closed paper proof
- [x] positive rooted/nonlocal survivor extracted
- [x] internal collision audit
- [x] targeted external literature audit
- [ ] unconditional Lean formalization
- [x] compose exact rooted survivor with source tangent normal expansion
- [ ] formalize the full stationary-kernel impossibility theorem
- [ ] identify the continuation-compatible global Xi coupling
