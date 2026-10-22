# Polynomial-Gaussian torsion-phase threshold universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/PolynomialTorsionLanguageEntireSeries.lean`
  - `polynomialTorsionLanguageFunction_eq_tsum`
  - `hypertranscendental_polynomialTorsionLanguageFunction`
- `HTGeometry/GaussianTorsionLanguageTailLock.lean`
  - `gaussianPhaseFunction_eq_tsum`
  - `hypertranscendental_gaussianPhaseFunction`

## Universal law

The explicit polynomial-magnitude carrier at real exponent `β = 2` equals the independently
constructed Gaussian carrier. Gaussian tail lock supplies the critical face excluded by strict
polynomial confinement. Therefore every unit-norm torsion-language-universal phase makes
`Σ exp(-B n^β) u_n z^n` hypertranscendental for every `B > 0` and every real `β ≥ 2`; one explicit
universal torsion phase realizes the whole closed exponent range.

## Lean status

Formalized in
`formal/GaloisForLFunctions/HTGeometry/PolynomialGaussianTorsionPhaseThresholdUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/HTGeometry/PolynomialGaussianTorsionPhaseThresholdUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
