# Nonlinear constraint horizon rigidity

- **ID:** `nonlinear-constraint-horizon-rigidity`
- **Stage:** 3-formalized
- **Type:** STATIC DIFFERENTIAL-FIELD RECONSTRUCTION
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [NEW CORE INSTANCE]`
- **Parent:** `jet-horizon-translation-gauge-classification`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/NonlinearConstraintHorizon.lean`

## Theorem

Let `K` be a differential field and let `x,y in K`. Regard

```text
(x,y,z)=(x,y,xy)
```

as a point on the nonlinear observation surface `z=xy`. Define the derivative-frame determinant

```text
W=x' y''-x'' y'.                                          (1)
```

If `W != 0`, then

```text
x = [x'(z''-2x'y')-x''z'] / W,                            (2)
y = [y''z'-y'(z''-2x'y')] / W.                            (3)
```

Consequently, if `L` is any derivation-closed intermediate field containing

```text
x', y', z',                                               (4)
```

then `x,y in L`. Thus the first derivative horizon of the nonlinear surface reconstructs the
hidden base coordinates on the open set `W != 0`.

## Proof

Differentiating the static constraint twice gives

```text
z'  = x'y+xy',
z'' = x''y+2x'y'+xy''.                                    (5)
```

After subtracting the known middle term from the second equation, `(5)` is a two-by-two linear
system for `x,y`. Its determinant is `W`; Cramer's rule gives `(2)--(3)`. Derivation closure of
`L` supplies `x'',y'',z''`, so every term on the right belongs to `L`.

## Geometric meaning

The affine observation channel retains an additive integration ambiguity. The nonlinear product
constraint couples two tangent directions; when `W` is nonzero, the first two differentiated
constraint rows form a frame and eliminate that ambiguity. This is the explicit local model for
the general translation-gauge classification: nonlinear geometry fixes the clock origin without
supplying a flow.

## Lean declarations

```text
bilinearHorizonWronskian
secondDeriv_mul_eq
bilinearConstraint_reconstruct_left
bilinearConstraint_reconstruct_right
bilinearConstraint_left_mem_of_firstJets_mem
bilinearConstraint_right_mem_of_firstJets_mem
bilinearConstraint_pair_mem_of_firstJets_mem
```

## Verification

- isolated leaf elaboration: passed
- targeted build `GaloisForLFunctions.HTGeometry.NonlinearConstraintHorizon`: passed
- formal lint: passed
- axiom audit of both identities and the paired field theorem: only `propext`,
  `Classical.choice`, and `Quot.sound`
- no full build was run

## Novelty and significance gate

The formulas themselves are elementary Cramer's-rule identities. Their scientific role is as a
formally certified, non-affine local model of the new arbitrary-variety horizon classification;
they are not independently claimed as major new mathematics. Novelty and significance attach to
the parent classification, not to algebraic manipulation in `(2)--(3)`.

## RH impact audit

`[NO DIRECT RH IMPACT]` The theorem would reconstruct a source coordinate from a bilinear
multichannel zeta observation if such a source-pure constraint and a nonvanishing frame were
established. Neither is presently available.

## Gates

- [x] 0 -> 1: nonlinear surface selected as the first higher-dimensional test
- [x] 1 -> 2: reconstruction identities and field-membership consequence proved
- [x] 2 -> 3: formalized without placeholders and passed targeted verification
- [ ] 3 -> 4: publication relevance depends on the parent general theorem
