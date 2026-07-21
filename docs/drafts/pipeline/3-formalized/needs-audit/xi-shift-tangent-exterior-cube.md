# Xi-shift tangent exterior cube

- **ID:** `xi-shift-tangent-exterior-cube`
- **Stage:** 3-formalized
- **Type:** THEOREM / source-producer audit
- **Source:** `GammaSewnXiShiftTangentInnovation.lean`,
  `GammaSewnXiShiftTangentHilbertKernel.lean`, and HTGeometry confluent Cauchy-jet rigidity
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [INTERNAL NOVELTY AUDITED]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Lean theorem:** `RHTower.gammaSewnXiShiftEndpointUnitTangentFrame_det_sq_pos`
- **Lean file:** `RHTower/XiShiftTangentExteriorCube.lean`

## Exact theorem

Let `u_p(e)` be the normalized all-depth tangent feature already constructed from the actual
completed `+2` Xi-shift innovations:

```text
u_p(e)=p^2 gammaSewnXiShiftEndpointTangentFeature(p,e).
```

Put `a=1/p`.  Its first three valuation coordinates are

```text
u_p(0)=-a sqrt(1-a^2),
u_p(1)=(1-2a^2)sqrt(1-a^2),
u_p(2)=a(2-3a^2)sqrt(1-a^2).                         (XC1)
```

For three primes `p,q,r`, put `a=1/p`, `b=1/q`, and `c=1/r`, and let `U(p,q,r)` be the
three-by-three matrix whose columns are the three vectors in `(XC1)`.  Then

```text
det U(p,q,r)
 =-3 sqrt(1-a^2)sqrt(1-b^2)sqrt(1-c^2)
    (b-a)(c-a)(c-b)(a+b+c+2abc),                      (XC2)

(det U(p,q,r))^2
 =9(1-a^2)(1-b^2)(1-c^2)
    (b-a)^2(c-a)^2(c-b)^2(a+b+c+2abc)^2.              (XC3)
```

Consequently, if `p,q,r` are pairwise distinct, the exterior cube is strictly positive:

```text
(det U(p,q,r))^2>0.                                    (XC4)
```

This is a literal source coordinate.  It is constructed from the first three forward-difference
innovations of the hypertranscendental Xi-shift carrier, before any Gram compression and without a
zero, target eigenvector, selected deep valuation, inverse resolution lift, or graph completion.

## Paper proof

After removing the three positive square-root factors, the columns in `(XC1)` are evaluations of

```text
g_0(x)=-x,
g_1(x)=1-2x^2,
g_2(x)=2x-3x^3.                                       (XC5)
```

Change the sign of the first row and write `h_0(x)=x`, `h_1(x)=1-2x^2`,
`h_2(x)=2x-3x^3`.  In the monomial basis `(1,x,x^2,x^3)`, only the degree sets
`{0,1,3}` and `{1,2,3}` contribute to the three-by-three Cauchy--Binet expansion.  Their
coefficient minors are respectively `3` and `6`.  The two monomial alternants are

```text
det[1;x;x^3]=(b-a)(c-a)(c-b)(a+b+c),
det[x;x^2;x^3]=abc(b-a)(c-a)(c-b).
```

Restoring the first-row sign and the square-root factors gives `(XC2)`; squaring gives `(XC3)`.
For a prime, `0<a<=1/2`, so all three `1-a^2` factors and `a+b+c+2abc` are strictly positive.
Pairwise distinct primes have pairwise distinct reciprocals, proving `(XC4)`.

There is also an all-degree explanation.  The generating function of `u_p` is

```text
sqrt(1-a^2)(z-a)/(1-az)^2.
```

It has a nonzero double principal part at the source-labelled pole `z=p`.  HTGeometry's confluent
Cauchy-jet uniqueness therefore implies finite linear independence of the complete tangent family
at distinct primes.  Formula `(XC2)` is the first RH-relevant exterior degree where that general
pole separation becomes visible without an abstract completion theorem.

## RH consequence and exact remaining open core

The earlier compound-order audit showed that the completed three-node response contains

```text
rooted stiffness * tangent second compound + tangent third compound.
```

The source was previously used only through its pairwise tangent Gram, leaving open whether it
actually produced the third compound.  Equations `(XC2)`--`(XC4)` answer that question positively:
the source already has a strict, oriented exterior cube, and it occurs before the finite-prefix
versus infinite-fusion issue.

Therefore the missing RH theorem is narrower than “construct a third compound.”  It is the
coefficientwise joined-response intertwining

```text
source exterior cube (XC2)
  -> pure tangent third term of the completed three-node response,
```

together with the existing rooted-second transfer and signed Jordan join.  Positivity of the
source cube alone does not identify its image with the target response and does not prove RH.

## Hostile audit

1. **Not a generic Gram wrapper.**  The determinant is computed from the actual normalized
   Xi-shift innovation coordinates and has the source-forced inverse-prime factors.
2. **Not HT graph saturation.**  No generic realization or density theorem supplies the sign;
   three literal valuation innovations already witness it.
3. **Not an inverse-resolution repair.**  The `p^2` normalization and centered height lift are the
   previously proved source normalization; `(XC2)` adds no ambient inverse.
4. **Not RH.**  The source-to-completed-response exterior intertwiner remains open.
5. **Parent theory.**  Generalized/confluent Vandermonde determinants and Hardy derivative kernels
   are classical.  Goodstein (1970), Flowe--Harris (1993), and Lomidze (1994) cover parent
   determinant technology.  Dyakonov (2022) uses the same Hardy-space rational factors
   `(z-a)/(1-az)` and `(1-az)^(-2)` in a different extremal problem.  Exact-form and concept
   searches found no source for `(XC2)` as the exterior cube of the completed Xi-shift valuation
   innovation.  This is search noncollision, not a priority claim.

Primary parent links:

- https://doi.org/10.2307/3613779
- https://doi.org/10.1137/0614079
- https://doi.org/10.1515/GMJ.1994.405
- https://doi.org/10.1016/j.aim.2022.108330

## Gates

- [x] exact source object fixed before conjecturing
- [x] internal exact-statement search found no duplicate
- [x] dependency-closed paper proof of `(XC1)`--`(XC4)`
- [x] parent-theory and exact-form external search
- [x] Lean formalization, direct leaf check, exact module build, lint, and axiom audit
- [ ] coefficientwise source/response third-compound intertwiner
- [ ] joined three-node response inequality / RH

## Log

- 2026-07-20 — Recut the broad four-rate response conjecture at the exact compound-order gap.
  The normalized Xi-shift source does not stop at a pair metric: its first three literal valuation
  innovations have the strict exterior cube `(XC2)`.  The RH-bearing gap is now the exterior
  intertwiner, not production of a source third compound.
- 2026-07-21 — Formalized `(XC1)`--`(XC4)` exactly.  Direct `lake env lean` and final exact-module
  `lake build GaloisForLFunctions.RHTower.XiShiftTangentExteriorCube` passed; generated indexes and
  formal lint are current.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
