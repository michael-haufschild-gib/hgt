# Prime-depth BV--Wold cofinal equicontinuity selector

- **ID:** prime-depth-bv-wold-cofinal-equicontinuity
- **Stage:** 3-formalized pending consolidated audit
- **Type:** CROSS-ROUTE QUANTITATIVE SELECTOR
- **Routes merged:** J physical Gamma depth, R BV--Wold wall, Xi source atlas
- **Formal module:** `GaloisForLFunctions/RHTower/PrimeDepthBVWoldCofinalEquicontinuity.lean`

## Statement

Let

```text
c_e(p) = (1-p^-1)^3 log(p)/p^e,
M_e(a) = sum_p |a| c_e(p).
```

For `e=n+2`, `M_e(a)` is finite and tends to zero as `n -> infinity`.  Route J's physical
source-normal Gamma deattenuation satisfies `d(p,s,r)^2=p^r`, so the two-polarization transport
obeys

```text
d(p,s,n+1)^2 a c_(n+2)(p) = a c_1(p).
```

Define cofinal source-normal equicontinuity to mean that one constant `C` bounds every returned
coordinate by deep input mass:

```text
|d(p,s,n+1)^2 a c_(n+2)(p)| <= C M_(n+2)(a)    for all n,p.
```

Then this condition holds iff `a=0`.  For `a` equal to actual Xi centered rate, pointwise
condition is equivalent to `Re(rho)=1/2`; global condition is equivalent to RH.

## Proof

Exact algebra gives

```text
p^r c_(e+r)(p)=c_e(p),
c_(e+r)(p)=p^-r c_e(p).
```

Since every prime is at least two, `p^-n -> 0` pointwise and `p^-n c_2(p) <= c_2(p)`.
`sum_p c_2(p)<infinity`; Tannery therefore gives `M_(n+2)(a)->0`.  If uniform `C` exists, fix
prime `2`.  Exact source transport and bound give

```text
|a c_1(2)| <= C M_(n+2)(a) -> 0.
```

Strict positivity of local coefficient `c_1(2)` forces `a=0`.  Converse uses `C=0`.  Exact
actual-atlas conversion follows after subtracting physical/unit-double remainder.

## New knowledge

Remaining source problem is not primarily construction of one depth-one trace-class object.  It
is a Banach--Steinhaus-type failure at cofinal depth: deep anomalies disappear in `l1`, while
source-normal inverse transport returns a fixed nonzero depth-one coordinate.  Off critical line,
inverse-depth maps must lose equicontinuity.  Thus RH becomes assertion that polarized source
geometry supplies uniform transport after off-diagonal cancellation, before divisor selection.

This explains existing Route-J result `scalarReadoutGain_linear_lower`: bounded carrier capacity
coexists with at least linear scalar-readout gain because current finite carrier retains singular
codiagonal.  Algebraic transport is already complete; missing bridge is cancellation strong enough
to replace growing gain by one depth-independent bound on all-prime centered orbit.

## Anti-theatre boundary

Global equicontinuity is a classifier, not yet a producer and not an RH proof.  Existing finite
five-prime/moving-block capacity cannot imply it: its scalar gain provably diverges.  Required new
producer must come from off-diagonal polarized source cancellation and prove a uniform bound in the
all-prime `l1` topology.  Assuming this bound for each Xi divisor would assume RH in a sharper type.

## Lean surface

- `primePow_mul_woldCoeff_add`
- `woldCoeff_add_eq_inv_pow_mul`
- `sourceNormalCofinalCenteredTransport_relativeLogCoefficient`
- `primeDepthBVWoldCenteredL1Mass_tendsto_zero`
- `cofinalSourceNormalEquicontinuity_iff_zero`
- `xiCofinalSourceNormalEquicontinuity_iff_re_eq_half`
- `xiGlobalCofinalSourceNormalEquicontinuity_iff_riemannHypothesis`
