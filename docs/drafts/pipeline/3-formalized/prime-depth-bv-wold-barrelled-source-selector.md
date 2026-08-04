# Prime-depth BV--Wold barrelled-source selector

- **ID:** prime-depth-bv-wold-barrelled-source-selector
- **Stage:** 3-formalized pending consolidated audit
- **Type:** CROSS-ROUTE COMPLETION / UNIFORM-BOUNDEDNESS BRIDGE
- **Routes merged:** HT barrelled Banach--Steinhaus, J cofinal Gamma depth, R Wold compacting orbit
- **Formal module:** `GaloisForLFunctions/RHTower/PrimeDepthBVWoldBarrelledSourceSelector.lean`

## Statement

Let `E` be a barrelled normed source space, `F_n:E->R` continuous linear readouts, and `x_n->0`
in `E`.  If `{F_n(x)}` is bounded for every completed source vector `x`, then

```text
F_n(x_n)=constant a  for every n  ==>  a=0.
```

For the Frankenstein atlas, require exact matrix coefficient

```text
F_n(x_n)
 = d(2,s,n+1)^2 a c_(n+2)(2)
 = a c_1(2).
```

Any completed-source certificate with these fields forces `a=0`.  Certificates for every actual
Xi divisor prove RH.

## Proof

HTGeometry's barrelled-space Banach--Steinhaus theorem converts pointwise boundedness of `F_n`
into one finite seminorm bound.  For norm topology this yields one `C` with

```text
|F_n(x)| <= C ||x||  for every n,x.
```

Applying at `x_n` and using `x_n->0` forces `F_n(x_n)->0`.  Exact source-normal Gamma/Wold
conversion says the same scalar is fixed at `a c_1(2)`.  Local coefficient is strictly positive,
so `a=0`.

## New knowledge

Uniform estimate need not be attacked by explicit all-depth norm calculation.  Correct producer
is a complete-source theorem with two qualitative inputs:

1. deep physical source orbit converges to zero;
2. every vector in completed source has bounded cofinal readout orbit.

Banach--Steinhaus supplies quantitative uniformity automatically.  This explains why all finite,
algebraic, or merely dense source constructions stall: pointwise boundedness on a non-barrelled
dense core gives no uniform bound.  Route-J linear gain theorem is not just negative; by the
uniform boundedness contrapositive it predicts an escaping vector in any honest completion unless
off-diagonal source relations remove singular codiagonal.

Recent publication-ready CCM Schatten-1 continuity is relevant infrastructure but not the missing
theorem: it proves continuity in each class-space coordinate.  Needed new input is pointwise
boundedness across cofinal depth on literal closed source quotient.  Route-L completed Hellinger
graph and real-corona/CCM closed relative source are now the two concrete completion candidates.

## Anti-theatre boundary

- Boundedness only on finite-support source is insufficient.
- A separate constant for each depth is insufficient.
- Defining source completion by bounded readout orbit inserts conclusion.
- Certificate must be built from an independently defined physical source topology and exact
  source matrix coefficient before Xi-divisor selection.

## Lean surface

- `eq_zero_of_barrelled_pointwiseBounded_cofinalReadout`
- `PrimeDepthBVWoldBarrelledSourceCertificate`
- `PrimeDepthBVWoldBarrelledSourceCertificate.centeredRate_eq_zero`
- `re_eq_half_of_barrelledSourceCertificate`
- `riemannHypothesis_of_globalBarrelledSourceProducer`
