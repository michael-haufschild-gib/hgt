# Hedenmalm center-mixed raywise coalesced cone

- **ID:** `hedenmalm-center-mixed-raywise-coalesced-cone`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM / SOURCE-SPECIFIC ORDER-THREE POSITIVITY
- **Date:** 2026-07-20
- **Scientific status:** `[FORMALIZED] [SOURCE-PURE] [NO COMPUTATION] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `hedenmalm-center-mixed-fourth-jet-coalesced-cusp.md`

## Exact claim

Let `f(t)=thetaCuspCenterMixedDensity a t` for `0<a<1/2`, and let

```text
D_lambda(t)=det [f(t_i-t_j)]_(t_0,t_1,t_2)=(0,t,(1+lambda)t),
```

where `lambda>0`.  Then there is `delta(a,lambda)>0` such that

```text
0<t<delta(a,lambda) -> D_lambda(t)>0
```

and hence the actual three-point matrix is positive definite.  Equivalently, every fixed positive
aspect-ratio ray through the coalesced corner eventually lies in the order-three positive chamber.
The radius may depend on the ray; no uniform square or full bounded-core theorem is claimed.

## Exact frontier

- `[CORPUS]` `thetaCuspCenterMixedDensity_secondJet_zero_neg` proves `f''(0)<0`.
- `[CORPUS]` `thetaCuspCenterMixedDensity_fourthHankel_pos` proves
  `f(0)f''''(0)-f''(0)^2>0` from the actual theta source.
- `[CORPUS]` `exists_thetaCuspCenterMixed_coalescedCusp_posDef` proves
  `forall y small, exists epsilon(y), forall x<epsilon(y)`, but supplies no lower control on
  `epsilon(y)/y`; it therefore does not reach a prescribed ray `x=y/lambda`.
- `[CORPUS]` the cofinal chamber handles a sufficiently large adjacent gap, leaving a bounded
  two-gap core.
- `[LITERATURE]` Castano--Paksoy--Zhang, arXiv:1407.2800, Corollary 2(ii), identifies positivity of
  a nonnegative `3x3` correlation matrix with the triangle inequalities for the three arccosine
  angles.  This is parent matrix geometry, not a theta-source producer.
- `[LITERATURE]` Gneiting's 1999 derivative theorem gives fourth-derivative inequalities forced by
  an already positive-definite radial function.  It cannot be used to assume the target.
- `[LITERATURE]` Hedenmalm, arXiv:2606.17494, supplies the theta boundary-value route but no local
  three-node ray chamber.  The audited 2026 theta log-concavity preprints stop at order two.

No source located in the internal corpus or primary literature states the raywise theorem for
Hedenmalm's center-mixed theta density.

## Paper proof

Put

```text
d=f(0),  u=f''(0),  v=f''''(0),  z=1+lambda.
```

The density is even and `C^6`, so its odd jets through order five vanish at zero.  Along a fixed
positive ray,

```text
f(c t)=d+(u/2)c^2 t^2+(v/24)c^4 t^4+O(t^6).
```

Write the three off-diagonal deficits as

```text
P=d-f(t),  Q=d-f(lambda t),  R=d-f(z t).
```

The cubic determinant has the exact deficit identity

```text
D_lambda(t)
 =d(2(PQ+PR+QR)-P^2-Q^2-R^2)-2PQR.                   (1)
```

Set `alpha=-u/2` and `beta=-v/24`.  Then

```text
(P,Q,R)
 =alpha(1,lambda^2,z^2)t^2+beta(1,lambda^4,z^4)t^4+O(t^6).
```

For the quadratic form

```text
H(P,Q,R)=2(PQ+PR+QR)-P^2-Q^2-R^2,
```

the degree-four term vanishes because `z=1+lambda`:

```text
H(1,lambda^2,z^2)=0.                                  (2)
```

The cross term is the exact polynomial identity

```text
sum_(i!=j) U_i V_j-sum_i U_i V_i
 =-6 lambda^2 z^2,                                    (3)
```

for `U=(1,lambda^2,z^2)` and `V=(1,lambda^4,z^4)`.  Substituting (2)--(3) into (1) gives

```text
D_lambda(t)
 =[-u/4 * (d v-u^2) * lambda^2(1+lambda)^2] t^6+o(t^6).
```

Equivalently, the first six jets are

```text
D_lambda^(j)(0)=0                    for 0<=j<6,
D_lambda^(6)(0)
 =-180 u(d v-u^2)lambda^2(1+lambda)^2.                (4)
```

The theta-source theorems give `u<0` and `d v-u^2>0`; `lambda>0` makes the remaining factors
strictly positive.  Hence the sixth jet in (4) is positive.  Continuity of the sixth jet and six
successive applications of the one-sided derivative sign theorem produce `D_lambda(t)>0` for all
sufficiently small `t>0`.

For the actual density, `f(t)>0` and `f(t)<f(0)` for every `t>0`.  The already formalized strict
`3x3` determinant criterion therefore upgrades `D_lambda(t)>0` to positive definiteness.

## Hostile attack

1. **Not implied by the nested cusp.**  The cusp only gives an unspecified `epsilon(y)>0`; it is
   consistent with `epsilon(y)/y -> 0`, which misses every fixed ray.
2. **Not a uniform neighbourhood.**  `delta(a,lambda)` may degenerate as `lambda->0` or
   `lambda->infinity`.  The theorem identifies the complete positive tangent cone, not a square.
3. **No hidden positive-definiteness premise.**  The sign in (4) comes from the independently
   proved theta-source fourth Hankel gap.  Gneiting's converse-direction necessity is not used.
4. **No sixth-source inequality.**  The sixth derivative of `f` cancels from the first nonzero
   determinant jet.  `C^6` regularity is only needed to control the remainder/jet continuity.
5. **Parent-theory verdict.**  The generic sixth-jet calculation is a calculus bridge.  Its
   source-specific discharge for Hedenmalm's density is the research content.

Verdict: `SURVIVES PRELIMINARY ATTACK`.  The proof is dependency-closed and uses no computation,
RH hypothesis, zero data, or positivity assumption on the target matrix.

## Lean realization

1. `HilbertMetric/SixthJetRaywiseCoalescedCone.lean` defines the ray determinant and proves its
   exact deficit expansion, vanishing jets below six, and universal sixth-jet identity.
2. `exists_threePointCorrelationDeterminantRay_pos_right` converts the strict sixth jet into a
   one-sided positive determinant interval for every fixed positive aspect ratio.
3. `RHTower/Hedenmalm/HedenmalmCenterMixedRaywiseCoalescedCone.lean` extracts the sixth source jet, proves
   the complete `C^6` derivative chain, and identifies the iterated derivatives with the existing
   theta jets.
4. `exists_thetaCuspCenterMixed_raywiseCoalescedCone_posDef` discharges the generic theorem with
   `thetaCuspCenterMixedDensity_fourthHankel_pos` and upgrades the determinant to actual matrix
   positive definiteness.

## Gates

- [x] internal corpus and failed-route audit
- [x] primary parent-literature audit
- [x] exact falsifiable claim
- [x] hostile non-circularity and parent-theory attack
- [x] dependency-closed paper proof
- [x] exact Lean theorem
- [x] axiom audit: the generic sixth-jet identity, generic positivity theorem, source `C^6`
  theorem, and source PosDef capstone use only `propext`, `Classical.choice`, and `Quot.sound`
- [x] generated theorem indexes and repository wiring lint
- [x] final SOTA module audit: 8979/8979 jobs
