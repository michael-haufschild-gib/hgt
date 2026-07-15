# Projective horizon building: two-chart core

- **ID:** `projective-horizon-building-two-chart-core`
- **Stage:** 3-formalized
- **Type:** PROJECTIVE DIFFERENTIAL-FIELD RECONSTRUCTION
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED]`
- **Parent:** `projective-horizon-tits-building`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonBuilding.lean`

## Theorem

Let `K` be a differential field of characteristic zero, let `x,y in K`, and assume

```text
x != 0,   x' != 0.                                        (1)
```

The two standard projective charts use coordinates

```text
(x,y),               (u,v)=(1/x,y/x).                    (2)
```

The positive jets in the two charts reconstruct first the denominator and then the transverse
coordinate:

```text
x = 2x' / [x''/x' - u''/u'],                              (3)
y = [y'x-v'x^2]/x'.                                       (4)
```

Consequently, if `L` is a derivation-closed intermediate field containing

```text
x', y', u', v',                                           (5)
```

then `x,y in L`.

More generally, for an arbitrary family `(y_i)`, membership of every `y_i'` and
`(y_i/x)'` reconstructs `x` and every `y_i`. This is the coordinatewise two-chart theorem in
arbitrary projective dimension.

## Proof

Equation `(3)` is the exact projective inversion reconstruction law. The quotient rule gives

```text
v'=(y'x-yx')/x^2,
```

which rearranges to `(4)`. Derivation closure supplies the second derivatives required by `(3)`.
All denominators are nonzero by `(1)` and the derivative-of-inverse identity.

## Lean declarations

```text
projectiveRatio_reconstruct_transverse
projectiveTwoChart_denominator_mem
projectiveTwoChart_transverse_mem
projectiveTwoChart_pair_mem
projectiveTwoChart_family_mem
```

## Verification

- isolated leaf elaboration: passed
- targeted build `GaloisForLFunctions.HTGeometry.ProjectiveHorizonBuilding`: passed
- formal lint: passed
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- no full build was run

## Scientific boundary

The formulas formally certify the local complementarity mechanism for two distinct projective
horizons. The parent paper theorem uses the same reconstruction coordinatewise in arbitrary
projective dimension and adds the unipotent fixed-field and Tits-building intersection laws. Those
group-action laws are not hidden behind Lean assumptions.

## RH impact audit

`[NO DIRECT RH IMPACT]` The theorem is available if two natural projective zeta observation charts
are later identified. At present it has no zero-location consequence.

## Gates

- [x] 0 -> 1: higher-rank two-chart mechanism isolated
- [x] 1 -> 2: denominator and transverse reconstruction proved
- [x] 2 -> 3: formalized and targeted verification passed
- [ ] 3 -> 4: depends on publication audit of the parent building theorem
