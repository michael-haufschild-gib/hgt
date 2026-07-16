# Gamma finite effectivity and completed nonsplitting

- **ID:** `gamma-cofinal-reconstruction-defect`
- **Stage:** 3-formalized
- **Type:** NATURAL STRICTNESS-JUMP MODEL / FORMAL BRIDGE
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [PARENT OPERATOR THEORY]`
  `[NOT STANDALONE NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH RESULT]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/GammaCofinalReconstructionDefect.lean`

## Theorem

For every finite resolution `N`, define

```text
(A_N x)_n=x_n/(n+1)!,       n<N.
```

Then `A_N` is bijective and its inverse is

```text
(A_N^(-1)y)_n=(n+1)! y_n.
```

The inverse amplification diverges factorially.  On the completed square-summable clock, the
diagonal operator

```text
(A x)_n=x_n/(n+1)!
```

is injective with dense proper nonclosed range and has no continuous left inverse.

The pointwise diagonal is not an artificial second map.  Lean identifies it with the restriction
of `gammaFactorialStreamEquiv`, the existing algebraic factorial equivalence on all raw streams.
Lean now also identifies each diagonal coefficient with the oriented rank-one curvature of two
adjacent finite Gamma translation shadows.  Thus the coefficient sequence is source-forced, while
the loss of invertibility occurs on passage to the square-summable rigging/completion.

Equivalently, every finite source-normalized observation problem is exactly reconstructible, but
finite reconstruction does not survive the cofinal Hilbert completion as a bounded operation.

## Lean declarations

- `gammaFactorialFiniteObservation`
- `gammaFactorialFiniteReconstruction`
- `gammaFactorialFiniteReconstruction_leftInverse`
- `gammaFactorialFiniteReconstruction_rightInverse`
- `gammaFactorialFiniteObservation_bijective`
- `gammaFactorialFiniteReconstruction_apply`
- `gammaFactorialFiniteReconstruction_amplification_tendsto_atTop`
- `gammaFactorialObservabilityOperator_eq_streamEquiv_apply`
- `gammaFactorialObservabilityOperator_apply_eq_clockCurvature`
- `gammaFactorialObservabilityOperator_denseRange`
- `gammaFactorialObservabilityOperator_not_surjective`
- `gammaFactorialObservabilityOperator_no_continuousLeftInverse`
- `gammaFactorial_rawEquiv_completed_nonsplit`
- `gammaFactorial_finite_effective_completed_nonsplit`

The formal axiom basis is only `propext`, `Classical.choice`, and `Quot.sound`.

## Scientific classification

Diagonal compact operators with nonclosed range, unbounded inverse amplification, strict
morphisms in Banach categories, and uniform stability of finite sections are established parent
functional analysis.  The theorem is therefore not promoted as new scientific knowledge.

Its value is structural.  It is a source-natural exact model in which every finite proof stage
succeeds while the completed reconstruction fails.  It supplies the vertical seed for the
conjectural polarized strict-descent field in
`../../1-in-progress/hypertranscendental-polarized-strict-descent-field.md`.

The parent operator theorem remains downgraded.  The separate candidate-new claim is the exact
source-curvature comparison that constructs its diagonal from the finite Gamma tower; see
`../new_scientific_knowledge/gamma-source-curvature-forced-strictness.md`.

## Gates

- [x] every finite stage exactly inverted
- [x] inverse coefficient identified
- [x] factorial divergence proved
- [x] completed injectivity inherited
- [x] completed dense range proved
- [x] completed nonsurjectivity and nonclosed range proved
- [x] absence of a continuous left inverse proved
- [x] Lean verification passed
- [x] parent-theory downgrade recorded
