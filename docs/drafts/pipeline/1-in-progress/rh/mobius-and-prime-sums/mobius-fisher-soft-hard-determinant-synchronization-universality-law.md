# Möbius Fisher soft--hard/determinant synchronization universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL PATH-INDEPENDENT BOUNDARY LAW; LITERATURE AUDITED]`

## Lean-derived law

The corpus contains two independently regularized critical objects:

- the ratio between hard squarefree-Möbius cutoff Ward energy and the soft damped Fisher
  coefficient, tending to `4` as clock aperture tends to zero from above;
- the determinant of the completed infinite pointed-Fisher compression, tending to `-8` as the
  Euler parameter tends to `1` from above.

Applying the exact negative half-square determinant transform to the first signal gives the same
`-8` boundary value. More strongly, for every type `α`, every filter `l` on `α`, and every pair of
paths `sigma, u : α → ℝ` satisfying

`sigma → 1⁺` and `u → 0⁺`,

the difference between the completed pointed-Fisher determinant at `sigma` and the transformed
hard/soft ratio at `u` tends to zero.

Lean declarations:

- `RHTower.mobiusCriticalPointedFisherDeterminantBoundarySignal`
- `RHTower.mobiusCriticalSoftHardDeterminantBoundarySignal`
- `RHTower.tendsto_mobiusCriticalSoftHardDeterminantBoundarySignal`
- `RHTower.mobiusFisherQFIDeterminant_softHardBoundarySynchronization`

## Corpus inputs

- `RHTower.tendsto_squarefreeMobiusCriticalFisherCutoffWardLimit_div_softFisherCoefficientLimit`
- `RHTower.squarefreeMobiusCritical_fisherQFIDeterminantUniversality`
- `RHTower.det_squarefreeMobiusCritical_pointedFisherConnectionCompression`

## New mathematical connector

The terminal laws treated hard/soft aperture regularization and Euler-boundary determinant
regularization separately. The determinant theorem supplies the nonlinear coordinate change
`x ↦ -x²/2`; applying it to the hard/soft ratio and then quantifying over arbitrary coupled paths
shows the two boundaries define one universal asymptotic scalar. This arbitrary-filter
synchronization did not occur in the corpus.

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof searches covered Möbius and squarefree carriers, Fisher and quantum Fisher
information, projective/Fubini--Study geometry, QFI determinants, critical regularization, and
Hilbert-space reformulations of RH.

Nearest sources:

- Facchi--Kulkarni--Man'ko--Marmo--Sudarshan--Ventriglia, *Classical and Quantum Fisher
  Information in the Geometrical Formulation of Quantum Mechanics*, arXiv:1009.5219, relates
  Fisher information to the Hermitian geometry of pure-state space:
  <https://arxiv.org/abs/1009.5219>
- Mondal, *Generalized Fubini-Study Metric and Fisher Information Metric*, arXiv:1503.04146,
  develops gauge-invariant projective metrics and their Fisher-information reductions:
  <https://arxiv.org/abs/1503.04146>
- Zhou--Jiang, *An exact correspondence between the quantum Fisher information and the Bures
  metric*, arXiv:1910.08473, treats the QFI/Bures correspondence:
  <https://arxiv.org/abs/1910.08473>
- Xue, *On a Hilbert Space Reformulation of Riemann Hypothesis*, arXiv:1911.04029, studies a
  Nyman--Beurling--Báez-Duarte Hilbert-space criterion:
  <https://arxiv.org/abs/1911.04029>
- Liu, *Multiplicative functions resembling the Möbius function*, arXiv:2205.00972, studies
  squarefree-supported Möbius-like functions and their cancellation:
  <https://arxiv.org/abs/2205.00972>

No source found combines a squarefree-Möbius hard/soft Fisher boundary ratio with a completed
pointed-Fisher/QFI determinant, or proves their negative-half-square synchronization along every
coupled filter path. Novelty claim is restricted to this exact boundary law.

## Lean target

`formal/GaloisForLFunctions/RHTower/MobiusFisherSoftHardDeterminantSynchronizationUniversalityLaw.lean`

## Verification

- source proof exact and warning-free:
  `lake env lean GaloisForLFunctions/RHTower/MobiusFisherSoftHardDeterminantSynchronizationUniversalityLaw.lean`
- imported by `formal/GaloisForLFunctions/RHTower.lean`
- final module and umbrella builds deferred to terminal audit
