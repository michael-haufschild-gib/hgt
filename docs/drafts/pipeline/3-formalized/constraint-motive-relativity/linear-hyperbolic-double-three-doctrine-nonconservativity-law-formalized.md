# Linear hyperbolic double: three-doctrine nonconservativity law — Lean certificate

- **ID:** `cmr-linear-hyperbolic-three-doctrine-nonconservativity-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `linear-hyperbolic-double-three-doctrine-nonconservativity-law.md`
  (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean module

`formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/HyperbolicDoubleNonconservativity.lean`,
imported by the area umbrella `GaloisForLFunctions.HTGeometry`.
Namespace: `HTGeometry.ConstraintMotiveRelativity`.

It reuses the corpus differential layer: `GaloisForLFunctions.HTGeometry.JetField` and
`exists_differentialIndependent_fin` from `FiniteShadowCapacitySpectrum.lean`, and
`differentialTranscendenceDegree_fusionField` from
`ConstraintRelativity/NeutralFusionCotangent.lean`.

## Formal statement chain

### §3 — the affine moment-extension countermodel

1. `momentHankel` — `(NC.4)`, the size-two Hankel matrix of `s₀ = 1, s₁ = 10, s₂ = 100`.
2. `momentHankel_quadratic` — its quadratic form is `(x₀ + 10 x₁)²`, hence
   **`momentHankel_posSemidef`**; `momentHankel_det = 0`.
3. **`momentHankel_null`** and **`momentHankel_ker_eq`** — `(NC.5)`: the null line is
   `ℝ(-10, 1)`, and the kernel is exactly `x₀ + 10 x₁ = 0`.
4. `momentRemainder`, `momentRemainder_eq` — `(NC.6)`, `R(s₃) = s₃ - 1000`.
5. **`momentRemainder_opposite`** and **`momentRemainder_ne`** — `(NC.7)`–`(NC.8)`: the two
   successors `1004` and `984` give `R = 4 > 0 > -16 = R`, opposite outgoing affine orientation,
   although the whole current face, its determinant, its null line and its null polynomial agree.

### §4 — the integral recurrence countermodel

6. `detune α` and **`detune_ker`** — `(NC.9)`–`(NC.10)`: the real kernel is the line through
   `(-α, 1)` for every `α`, so the bare double is the same.
7. `intRelation α` — `(NC.12)`, the integral relation lattice.
8. **`intRelation_two`**, `mem_intRelation_two` and **`intRelation_sqrtTwo`** — `(NC.13)`:
   `Λ₂ = ℤ(-2,1)` and `Λ_{√2} = 0`, the latter from `irrational_sqrt_two`.
9. **`detune_nonconservative`** — the two systems have the same real kernel and different
   integral relation lattices.
10. `phaseOrbit`, **`phaseOrbit_periodic_two`** and **`phaseOrbit_not_periodic_sqrtTwo`** —
    `(NC.14)`: the two-frequency phase orbit is `2π`-periodic for `α = 2` and has no period at all
    for `α = √2`.

### §5 — the differential-hypertranscendence countermodel

11. `jetField_zero_differentialAlgebra` — the free differential field `JetField C ℕ` is a
    differential algebra over its constants.
12. **`jetField_algebraMap_injective`** and **`jetField_ker_eq_bot`** — `(NC.17)`: the killed-law
    kernel of the structure map is zero, hence so is the bare hyperbolic double.
13. **`exists_differentialExtension_rank`** — `(NC.18)`: for every `r` there is a differentially
    independent family of size `r` in `JetField C ℕ` whose generated differential subfield has
    differential transcendence degree exactly `r`.

### §6 — the theorem

14. **`three_doctrine_nonconservativity`** — Theorem 2.1: the affine pair reverses orientation, the
    two detunings differ in their integral relation lattice, and the differential extensions differ
    in differential transcendence degree, while in each pair the bare kernel and its hyperbolic
    double are the same.  Any invariant factoring through the unmarked double takes equal values on
    each pair, so it is not jointly conservative.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/HyperbolicDoubleNonconservativity.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.HyperbolicDoubleNonconservativity
```

Green with no warnings.  `#print axioms` on `momentHankel_posSemidef`, `momentHankel_det`,
`momentHankel_null`, `momentHankel_ker_eq`, `momentRemainder_opposite`, `momentRemainder_ne`,
`detune_ker`, `intRelation_two`, `intRelation_sqrtTwo`, `detune_nonconservative`,
`jetField_ker_eq_bot`, `exists_differentialExtension_rank`, `three_doctrine_nonconservativity`,
`phaseOrbit_periodic_two` and `phaseOrbit_not_periodic_sqrtTwo` reports only `propext`,
`Classical.choice`, `Quot.sound`.

## Scope notes

`(NC.14)` also records the classical strengthening that the `α = √2` orbit is *dense* in `𝕋²`
(two-dimensional Kronecker).  The datum the card identifies as lost is the integral relation
lattice `(NC.12)`–`(NC.13)`, which is formalized exactly, together with the periodic/aperiodic
dichotomy that separates the two orbits; the density strengthening is classical background and is
not used by Theorem 2.1.

The differential countermodel is realized inside the corpus free differential field
`JetField C ℕ` rather than by rebuilding `k⟨y₁,…,y_r⟩`; the two are the same object — the fraction
field of the jet polynomial ring with the jet-shift derivation — and the corpus already owns its
differential independence and the differential transcendence degree of the generated subfield.
