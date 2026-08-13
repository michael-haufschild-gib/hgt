# Hedenmalm exterior Cayley--Abel Green landing

- **Stage:** `1-in-progress`
- **Type:** `[HEAVY CONJECTURE -> PAPER PROOF -> LEAN TARGET]`
- **Route:** Frankenstein seam (horizontal source Cayley × Ward Green × Hedenmalm exterior)

## Failed conjecture

Multiplying the five-shift Euler separator by the exterior detector does not itself produce a
source sign law.  The scalar inequality at `lambda=log n` is valid, but the corresponding
critical-evaluation theorem requires `|Im z|<1/2` and `-Im z=log n`, impossible for `n>=2`.
Moreover the legal holomorphic windowed five-shift pairing is already proved identically zero in
`XiWardFiveShiftWindowedKreinCharge.lean`.  Treating either statement as a prime-side exterior
estimate would be a false handoff.

## Surviving conjecture

Let

```text
x = 2 Re(rho)-1,
y = Im(xiSpectralPointSupport(rho)) = -x/2,
u = realCayley(x) = (x-i)/(x+i).
```

Then, off the critical line,

```text
1/y = 2 i (1-u)/(1+u).
```

For `|R|<1`, the denominator has a coefficient-faithful finite source-orbit approximation

```text
2 i (1-u) sum_(k<K) (-R u)^k
    -> 2 i (1-u)/(1+R u)                  (K -> infinity).
```

Sending `R -> 1` yields the exact Ward Green normalization.  At `x=0`, every adjacent exterior
determinant is already zero, so multiplication by every finite polynomial is zero and the apparent
boundary pole is removable after exteriorization.

## Paper proof

`norm(u)=1`, hence `norm(-R u)=|R|<1`; the first limit is the ordinary geometric series.  The
displayed Cayley identity follows by substituting `(x-i)/(x+i)` and using `y=-x/2`.  Off line,
continuity at `R=1` gives the Abel limit.  On line, the exact determinant factorization contains
the factor `Im z=y=0`, so both the finite orbit and Abel carrier vanish identically.  Therefore the
totalized limit agrees pointwise with the existing coefficient

```text
(Im z)^(-1) * adjacentCriticalFeatureEvaluationDet(t,z).
```

No zero-fitted reciprocal is inserted: every prelimit is a finite polynomial in the retained
source-horizontal Cayley phase.

## Lean target

- [ ] finite Cayley polynomial has the Abel-resolvent limit for `|R|<1`;
- [ ] Cayley boundary multiplier equals inverse transverse coordinate off line;
- [ ] exterior product has removable critical-line kernel;
- [ ] forward and backward normalized exterior coefficients are exact Abel boundary values;
- [ ] direct Lean check, exact leaf build, axiom audit, umbrella wiring.

## Remaining producer after this card

Combine this legal Cayley--Abel normalization with a source-level reflection projector for the
four-leg prime--Gamma determinant, then prove an absolute arithmetic bound below the existing
exterior quantum `4*(96/145)^2`.  This card closes normalization provenance only; it does not claim
that arithmetic bound or RH.
