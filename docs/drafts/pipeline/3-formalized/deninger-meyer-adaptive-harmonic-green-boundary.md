# Deninger--Meyer adaptive harmonic Green boundary

- **ID:** `deninger-meyer-adaptive-harmonic-green-boundary`
- **Stage:** `3-formalized`
- **Type:** SOURCE COMPARISON / GREEN FRACTURE BOUNDARY
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED]`
- **Lean:**
  `../../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerAdaptiveHarmonicGreenBoundary.lean`
- **Parents:**
  `deninger-meyer-reflected-gaussian-harmonic-source-primitive.md`,
  `../1-in-progress/mobius-theta-adaptive-infinite-depth-gaussian-boundary.md`

## Result

Let `B_x` be the literal two-exterior-line prime--Gamma Cauchy boundary, `W = i sign(D)` the
physical harmonic Hodge operator, `Ghat` completed source Green reflection, `H_K(p)` the honest
cofinal adaptive prime-normal horizon column, and `D_G` completed Green provenance.

The following source identities are proved without RH:

```text
B_x(R q) = B_{-x}(q),
Ghat(i W B_x) = B_{-x},
-i W H_K(p) -> e_ref,
Ghat(-i W H_K(p))(q) = -H_K(p)(R q),

D_G = -M_kappa o Ghat,
integral_R D_G(B_x) dx = g_G,
-D_G(H_K(p)) -> g_G.
```

Consequently the literal prime--Gamma Cauchy source and every retained-prime adaptive source have
the same completed boundary not only at the Gaussian horizon `h_ref` and its unique Green primitive
`e_ref`, but at the actual global RH detector `g_G`.  The source comparison commutes with completed
Green transport at every finite adaptive depth; Green compatibility is not introduced only after
taking a Hilbert limit.

## Formal theorem surface

- `deningerArithmeticCompletedSourceGreen_harmonicOrientation_apply`
- `reflectedGaussianPrimeGammaCauchyBoundary_reflect`
- `deningerArithmeticCompletedSourceGreen_orientedCauchyBoundary_eq_reversed`
- `tendsto_reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn`
- `deningerArithmeticCompletedSourceGreen_adaptiveHarmonicColumn_apply`
- `deningerArithmeticCompletedGreenProvenanceCLM_apply`
- `integral_reflectedGaussianPrimeGammaGreenFractureBoundary_eq_greenProvenance`
- `tendsto_adaptivePrimeNormalInfiniteDepthGreenFractureColumn`
- `tendsto_adaptivePrimeNormalInfiniteDepthGreenFractureColumn_eq_cauchyBoundary`

## Scientific consequence

Route L no longer lacks a source construction of the completed Green defect itself.  `g_G` is a
common boundary value of two explicit arithmetic source systems, with retained prime provenance on
the adaptive side and a Bochner-integrable two-line Gamma/Cauchy field on the Deninger side.

This narrows the open theorem from “construct or compare the Green vector” to a boundary-reader
statement: prove that this already common source value has a jointly conservative common-test
record whose route observations vanish and whose full record reflects zero.

## Anti-theatre audit

- The theorem does **not** claim fixed-sector adaptive codiagonal-kernel membership.  That clause is
  RH-bearing and remains open.
- The scalar line comparison `c |-> c R(e_p)` does not solve the frontier: its codiagonal vanishes
  exactly when `c = 0`.  The missing arithmetic theorem is what forces that observation to vanish.
- Symmetric Cauchy integration alone has no selection power.  The pointwise identity
  `Ghat(i W B_x) = B_{-x}` shows that full-line Green covariance is automatic parameter reversal;
  it cannot be miscounted as purity.
- No divisor-selected damping, target Cholesky factor, positivity premise, or RH premise occurs.

## Verification

- Direct foreground check:
  `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerMeyerAdaptiveHarmonicGreenBoundary.lean`
  passed.
- Targeted module build:
  `lake build GaloisForLFunctions.RHTower.Deninger.DeningerMeyerAdaptiveHarmonicGreenBoundary`
  passed.
- Axiom audit of the Green/Hodge transport, Cauchy reflection, bounded provenance factorization,
  Bochner integral, and adaptive-limit comparison reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- `git diff --check` and the forbidden-declaration scan pass for this module and its documentation.
- Repository-wide formal lint reaches this module through `GaloisForLFunctions.RHTower`; the audit
  found only concurrently owned, unrelated umbrella omissions.  The RHTower omission was wired by
  its owner during this audit; `HTGeometry.ShiftTranslateFiltration` remains outside this task's
  write scope.
