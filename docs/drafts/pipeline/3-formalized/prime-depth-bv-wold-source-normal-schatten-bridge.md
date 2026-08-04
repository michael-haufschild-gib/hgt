# Prime-depth BV--Wold source-normal Schatten bridge

- **ID:** prime-depth-bv-wold-source-normal-schatten-bridge
- **Stage:** 3-formalized pending consolidated audit
- **Type:** CROSS-ROUTE CONVERSION THEOREM
- **Routes merged:** J primitive-promoted Gamma depth, R BV--Wold depth, physical/unit-double seam
- **Formal module:** `GaloisForLFunctions/RHTower/PrimeDepthBVWoldSourceNormalSchattenBridge.lean`

## Statement

Route J's physical critical depth deattenuation obeys

```text
d(p,e,r)^2 = p^r.
```

At one depth step, two polarized legs therefore contribute `d(p,e,1)^2=p`.  This is exactly the
unbounded multiplier which inverts one Route-R Wold depth step.  With physical trace-class
basepoint `r(p)=2 log(p)/p^2`, define

```text
B_src,e(f)(p) = d(p,e,1)^2 (f(p)-r(p)) + r(p).
```

Then

```text
B_src,e = B_r,
B_src,e(L_(k+1)(rho)) = L_k(rho),
L_2(rho) in Dom(B_src,e : l1 --> l1) iff Re(rho)=1/2.
```

The global graph-domain statement is equivalent to RH.

## Proof

Physical critical boundary amplitude has squared depth law

```text
J_0(p,e)^2 = log(p) / p^(e+1).
```

Hence squared ratio between recorded depth `e` and realized depth `e+1` is `p`.  On Wold side,
direct cancellation in

```text
c_e(p)=(1-p^-1)^3 p^-e log(p)
```

gives `p c_(e+1)(p)=c_e(p)`.  Subtracting fixed remainder `r`, applying squared deattenuation,
and restoring `r` proves `B_src,e(L_(k+1))=L_k`.  `L_2` is summable by comparison with
`log(p)/p^2`; `L_1` is summable only when its centered scalar vanishes, since otherwise it carries
a nonzero multiple of divergent prime harmonic tail.  Globalizing over `XiDivisorSupport` gives
the stated RH classifier.

## New knowledge

Singular inverse-Wold transport is not an arbitrary analytic trick.  It is already encoded by
physical source-normal Gamma deattenuation.  Squaring arises because the retained carrier is
polarized/two-legged.  Recent Route-J cofinal carrier thus supplies exact singular operator;
Route-R supplies ideal wall; physical seam supplies affine origin.  Missing theorem is only
all-prime source admission into this graph domain.

## Anti-theatre boundary

Existing Route-J theorem gives uniform capacity only on moving finite five-prime blocks and proves
scalar readout gain diverges.  It does not imply global `l1` graph-domain admission.  Claiming it
does would be the RH assumption in another type.  Needed producer must be an adjacent-grade,
off-diagonal, all-prime source graph limit with coefficient identity before divisor selection.

## Lean surface

- `criticalDepthDeattenuation_sq_one`
- `primeDepthBVWoldSourceNormalDepthLowering_eq`
- `primeDepthBVWoldSourceNormalDepthLowering_relativeLogCoefficient`
- `sourceNormalDepthLoweringTraceDomain_iff`
- `relativeLogCoefficient_two_mem_sourceNormalDepthLoweringTraceDomain_iff`
- `primeDepthBVWoldXiSourceNormalDepthLoweringLanding_iff_riemannHypothesis`
