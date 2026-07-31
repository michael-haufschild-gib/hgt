# Finite quantum survival-history law

- **Status:** formalized
- **Lean module:** `GaloisForLFunctions.RHTower.FiniteQuantumSurvivalHistoryLaw`
- **Scientific role:** physical observable bridge

## Result

For real spectral weights \(p_i\) and arbitrary vertex phases \(z_i\), put
\[
  A_p(z)=\sum_i p_i z_i,
  \qquad
  S_p(z)=|A_p(z)|^2.
\]
The scalar expectation-history coefficient packet
\[
  c_{ij}=p_i p_j
\]
obeys the exact identity
\[
  \sum_{i,j}p_ip_j(z_i\overline{z_j}-1)
  =
  S_p(z)-\left(\sum_i p_i\right)^2.
\]
For normalized weights, the right-hand side is \(S_p(z)-1\).
Moreover, the one-history scalar rate--distortion metric is exactly
\[
  |S_p(z)-1|.
\]
For nonnegative normalized weights and unit phases, \(0\le S_p(z)\le1\),
so this deviation is exactly \(1-S_p(z)\).

Thus the observer-graph scalar recurrence law applies directly to a local
survival probability once its spectral weights are supplied. Equal gaps may
cancel freely; no noncancellation premise appears.

## Formal declarations

- `finiteSpectralSurvivalAmplitude`
- `finiteSpectralSurvivalProbability`
- `finiteSpectralSurvivalProbability_nonneg`
- `finiteSpectralSurvivalProbability_le_one`
- `finiteSpectralSurvivalCoefficient`
- `finiteQuantumExpectationDisplacement_survivalCoefficient`
- `finiteQuantumExpectationDisplacement_survivalCoefficient_normalized`
- `finiteSpectralSurvivalDeviation`
- `finiteSpectralSurvivalDeviation_eq_one_sub`
- `finiteQuantumExpectationTotalDeviation_survivalCoefficient_normalized`

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/FiniteQuantumSurvivalHistoryLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/FiniteQuantumSurvivalHistoryLaw.olean
```

passed. Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Boundary

This identity does not itself prove that an Anderson Hamiltonian has
localized eigenfunctions, that the weights have an exponential spatial
tail, or that a chosen localization ball contains few spectral modes.
Those are separate transfer theorems.
