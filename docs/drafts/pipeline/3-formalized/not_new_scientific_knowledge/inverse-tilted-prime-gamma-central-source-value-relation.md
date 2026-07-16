# Inverse-tilted prime--Gamma central source value relation

- **ID:** `inverse-tilted-prime-gamma-central-source-value-relation`
- **Stage:** 3-formalized
- **Type:** `[VALUE RELATION]`, `[TOP-DOWN INTERFACE DISCHARGE]`, `[BRIDGE]`
- **Scientific status:** `[PROVED LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/InverseTiltedPrimeGammaCentralSource.lean`
- **Parents:**
  `CCMInverseTiltedCriticalMellinFactorization.lean`;
  `XiCriticalMellinSourceFactorization.lean`;
  `PrimeArchCentralMomentGerm.lean`.
- **Statement:** One explicit inverse-tilted finite-prime source, its explicit quadrature
  correction, and the fixed Gamma connection reconstruct the canonical centered prime--Gamma
  relative trace as an analytic germ.  Consequently they reconstruct every normalized
  prime--Gamma moment exactly.

## Exact source

Put

```text
u(z) = -1/2 + i z,
s(z) = 1 + i z,
M(s) = inverseTiltedDyadicMellin(s),
F(s) = inverseTiltedDyadicContinuedSource(s),
C(s) = inverseTiltedCriticalMellinCorrection(s).
```

The inverse-tilted source factorization already proved

```text
F(s)=2 M(s) D_reg(s-3/2)+C(s),                          (1)
```

where `D_reg` is the regularized critical-Mellin defect.  The multiplier `M` is nonzero whenever
`Re s>0`.  Away from the filled zeta pole and the zeta divisor, Lean now proves the sharpened
identity

```text
D_reg(u)=D_cont(u),                                      (2)
```

without the former `Re u>0` restriction.  Hence the explicit reconstructed source

```text
T_inv(z)
 =i*((F(s(z))-C(s(z)))/(2M(s(z)))
       +GammaConnection(1/2+i z))                       (3)
```

satisfies

```text
T_inv(z)=continuedPrimeArchSourceRelativeTrace(z)        (4)
```

at every regular centered source point.  Since the central point is regular, `(4)` holds as a
germ at zero.

## Moment consequence

Normalized central division preserves the germ identity, so for every `n>=0`,

```text
analyticTraceMoments(normalizedTraceMomentGerm(T_inv),n)
  =normalizedPrimeArchMoment(n).                         (5)
```

Thus the complete RH-bearing moment tower is read from an explicit source assembled from:

1. a real finite prime-polar coefficient sequence whose L-series equals `F` on its initial
   half-plane;
2. an explicit holomorphic quadrature correction;
3. the fixed archimedean Gamma connection.

No Xi zero, divisor enumeration, zero location, representing measure, or positivity hypothesis
occurs in the definition of `T_inv`.

## What this closes and what it does not

This closes the previously missing value interface between the finite inverse-tilted prime source
and the canonical central prime--Gamma Taylor moments.  It does not make the continued source
positive.  Analytic continuation of a real Dirichlet coefficient source across its convergence
wall does not preserve a coefficient Gram or reflection-positive cone.

The next source problem is therefore not another value comparison.  It is to construct a positive
finite Hodge--Green or channel-resolved Gram whose ordinary positive trace equals the Taylor jets
of `(3)`.  Merely assuming positivity of the divided-difference kernel of `(3)` is already an
RH-equivalent consumer and is not a valid producer.

## Lean certificate

The module proves:

- `regularizedCriticalMellinDefect_eq_continued_of_ne_zero`;
- `inverseTiltedPrimeGammaSourceTrace_eq_continuedPrimeArchSourceRelativeTrace`;
- `inverseTiltedPrimeGammaSourceTrace_eventuallyEq_continuedPrimeArchSourceRelativeTrace`;
- `analyticAt_inverseTiltedPrimeGammaSourceTrace`;
- `normalizedTraceMomentGerm_inverseTiltedPrimeGammaSource_eventuallyEq`;
- `analyticTraceMoments_inverseTiltedPrimeGammaSource`.

It is wired through `formal/GaloisForLFunctions/RHTower.lean`.  The exact module build and direct
file check pass.  The displayed declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

## Gates

- [x] inverse-tilted critical-Mellin factorization reused
- [x] regularized/continued defect equality extended to the central regular domain
- [x] completed inverse-tilted/Gamma source defined without divisor data
- [x] pointwise prime--Gamma trace equality proved
- [x] central germ equality proved
- [x] every normalized moment coefficient transferred
- [x] exact module build and direct check pass
- [x] axiom audit passes
- [ ] construct a positive source Gram for these exact values
- [ ] RH
