# Finite Anderson survival non-exit law

- **Status:** formalized
- **Lean module:** `GaloisForLFunctions.HTGeometry.FiniteAndersonSurvivalNonExitLaw`
- **Claim class:** `[LEAN-PROVED] [SHARP BOUNDARY]`

## Result

Hermitian finite Anderson evolution is unitary, and site-survival loss has
the exact leakage identity
\[
 1-|U_{ii}(t)|^2=\sum_{j\ne i}|U_{ji}(t)|^2.
\]
If every off-diagonal transition amplitude is below \(\epsilon\) on a
finite horizon, then every site-survival deviation is at most
\[
 (n-1)\epsilon^2.
\]

For every nonempty finite site set, Hermitian hopping matrix, reference
onsite potential, finite horizon \(H\), and target \(\delta>0\), there are a
positive coupling and onsite potential whose canonical spectrum has maximal
projective rational rank while every site-survival deviation stays below
\(\delta\) throughout \([-H,H]\).

Thus global projective rank and finite-horizon locality cannot give a
universal upper bound on first exit. A post-exit recurrence theorem is the
strongest universal form available from those data.

## Formal declarations

- `finiteAndersonEvolution_conjTranspose_mul_self`
- `finiteAndersonEvolution_column_normSq_sum_eq_one`
- `finiteAndersonSiteSurvivalLoss_eq_offDiagonal_sum`
- `finiteAndersonSiteSurvivalLoss_le`
- `finiteAndersonSiteSurvivalDeviation_le`
- `exists_finiteAnderson_maximalProjective_finiteHorizon_survivalNonExit`
- `exists_finiteAnderson_maximalProjective_finiteHorizon_survivalTarget`

## Verification

Direct foreground compilation passed. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Boundary

Hamiltonian parameters may depend on \(H\) and \(\delta\). The result is
finite-horizon and does not prove infinite-time Anderson dynamical
localization for one fixed Hamiltonian.
