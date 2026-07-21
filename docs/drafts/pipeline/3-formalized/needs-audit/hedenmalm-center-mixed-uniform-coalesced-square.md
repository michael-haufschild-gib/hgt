# Hedenmalm center-mixed uniform coalesced square

- **ID:** `hedenmalm-center-mixed-uniform-coalesced-square`
- **Stage:** 3-formalized / needs-audit
- **Type:** CANDIDATE / SOURCE-SPECIFIC ORDER-THREE POSITIVITY
- **Date:** 2026-07-20
- **Scientific status:** `[PROVED HERE] [SOURCE-PURE] [NO COMPUTATION] [UNCONDITIONAL]
  [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `hedenmalm-center-mixed-raywise-coalesced-cone.md`

## Exact claim

For `f(t)=thetaCuspCenterMixedDensity a t` and `0<a<1/2`, there is `delta(a)>0` such that

```text
0<x<delta(a), 0<y<delta(a)
  -> Matrix.PosDef [f(t_i-t_j)]_(t_0,t_1,t_2)=(0,x,x+y).
```

This is a genuine two-dimensional neighbourhood of the coalesced corner.  Unlike the raywise
theorem, its radius is independent of the aspect ratio `y/x`; unlike the earlier nested cusp, it
uses one common bound for both gaps.

## Frontier and literature audit

- `[CORPUS]` the nested fourth-jet cusp proves `forall y small, exists epsilon(y)` and the raywise
  sixth-jet theorem proves `forall lambda>0, exists delta(lambda)`.  Neither quantifier order
  supplies a common coalesced square.
- `[CORPUS]` the source already proves `f''(0)<0`,
  `f(0)f''''(0)-f''(0)^2>0`, positivity, strict center decrease, and a complete `C^6` source
  derivative chain.
- `[LITERATURE]` Castano--Paksoy--Zhang, arXiv:1407.2800, gives the parent `3x3` correlation-matrix
  geometry, not a local theta-source square.
- `[LITERATURE]` Gneiting, JMAA 1999, gives derivative inequalities necessary for a function that
  is already positive definite; using it here would be circular.
- `[LITERATURE]` Hedenmalm, arXiv:2606.17494, supplies the live theta boundary-value route but no
  finite three-node coalesced-square theorem.
- `[LITERATURE]` Salazar, arXiv:2607.02778, develops strict total positivity from spectral Darboux
  and Toeplitz smoothing mechanisms, but does not cover this theta density or the local square.

No exact source-specific statement was located in the live corpus or primary literature.  The
generic calculus mechanism belongs to local total-positivity/extended-Chebyshev parent theory;
only its unconditional theta-source discharge is a novelty candidate.

## Paper proof

Write

```text
D(y,x)=det [f(t_i-t_j)]_(t_0,t_1,t_2)=(0,x,x+y),
u=f''(0),  H=f(0)f''''(0)-u^2.
```

Let `K=partial_x^2 D` and `C=partial_y^2 K`.  Direct differentiation gives a continuous `C^2`
function `C` when `f` is `C^6`.  The identities `D(y,0)=partial_x D(y,0)=0` hold for every `y`,
while `K(0,x)=partial_y K(0,x)=0` follows from the coalesced configuration and `f'(0)=0`.

At the double-coalesced point, cancellation of the diagonal jets gives

```text
C(0,0)=partial_x C(0,0)=partial_y C(0,0)=0,
partial_x^2 C(0,0) = -12 u H,
partial_x partial_y C(0,0) = -18 u H,
partial_y^2 C(0,0) = -12 u H.                         (1)
```

These are exactly the `(4,2)`, `(3,3)`, and `(2,4)` mixed sixth jets of `D`.  They may also be
read from the universal leading form

```text
D(y,x)=(-u H/4) x^2 y^2 (x+y)^2 + o((|x|+|y|)^6).
```

The theta source has `u<0` and `H>0`, so all three numbers in (1) are strictly positive.
Continuity gives one square around `(0,0)` on which `C_xx`, `C_xy`, and `C_yy` remain positive.

The conclusion follows without dividing by either gap.  First, `C(y,0)>0` for `y>0` by twice
integrating `C_yy>0`.  Also `C_x(y,0)>0` by integrating `C_xy>0` along the `y`-axis.  Integrating
`C_xx>0` in `x` and then `C_x>0` shows `C(y,x)>0` throughout the positive square.  For each fixed
`x`, twice integrating `K_yy=C` from `K(0,x)=K_y(0,x)=0` yields `K(y,x)>0`.  Finally, for each
fixed `y`, twice integrating `D_xx=K` from `D(y,0)=D_x(y,0)=0` yields `D(y,x)>0`.

For the actual theta density, `f(x)>0` and `f(x)<f(0)` for `x>0`; the strict determinant criterion
therefore upgrades `D(y,x)>0` to positive definiteness.

## Hostile attack

1. **Ray quantifiers do not suffice.**  A radius for each aspect ratio can collapse at the axes;
   the proof above controls the axes through exact double-zero factorizations and mixed jets.
2. **No target positivity is assumed.**  The only signs are the independently proved source laws
   `u<0` and `H>0`.
3. **No hidden sixth-moment sign.**  Every occurrence of `f^(6)(0)` cancels in (1); `C^6` is used
   only for continuity of the controlling mixed jets.
4. **Not an RH closure.**  This removes the complete small--small corner of the order-three wall.
   It says nothing about all finite node sets or the remaining bounded noncoalesced core.
5. **Parent-theory verdict.**  The mixed-derivative integration lemma is a bridge.  The
   Hedenmalm-theta instantiation is the source-specific result.

Verdict: `SURVIVES PRELIMINARY ATTACK`.  The proof is dependency-closed, unconditional, and uses
no numerical or symbolic experiment.

## Lean realization

1. `HilbertMetric/PositiveHessianSquare.lean` proves
   `exists_pos_square_of_coordinateHessian_pos`, the reusable two-variable integration lemma.
2. `HilbertMetric/UniformCoalescedThreePointSquare.lean` defines the literal mixed fourth jet and
   its derivatives, and exposes the exact mixed sixth-jet identities
   `threePointCorrelationDeterminantPathMixedFourthJetXX_zero` and
   `threePointCorrelationDeterminantPathMixedFourthJetYX_zero`.
3. `exists_threePointCorrelationDeterminantPath_pos_uniform_square` converts the negative second
   jet and strict fourth Hankel gap into one common positive determinant square.
4. `RHTower/HedenmalmCenterMixedUniformCoalescedSquare.lean` discharges every hypothesis from the
   actual theta source.  Its capstone
   `exists_thetaCuspCenterMixed_uniformCoalescedSquare_posDef` is the exact claim above.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure claim and corpus/literature audit
- [x] hostile non-circularity and parent-theory attack
- [x] dependency-closed paper proof `[PROVED HERE]`
- [x] 1 -> 2 fully-proven: dependency-closed proof and hostile audit
- [x] 2 -> 3 formalized: exact Lean theorem and source discharge
- [x] axiom audit: the positive-Hessian lemma, both exact mixed-jet identities, the generic
  determinant theorem, and the theta PosDef capstone use only `propext`, `Classical.choice`, and
  `Quot.sound`
- [ ] generated theorem indexes, repository wiring lint, and final narrow SOTA build
