# Route E / Matomaki--Teravainen brick 149 (2026-09-02)

Added `formal/GaloisForLFunctions/RHTower/Sieve/KloostermanGlobalCollisionCentered.lean`.

New exact results:

- `sum_kloostermanGlobalCollisionTimeTransform_eq_zero`: global collision transform has zero
  common-period mean because its zero-frequency coefficient vanishes.
- `kloostermanGlobalFrequencyCollisionEnergy_le_centered`: writing the transform as total response
  mass minus diagonal response mass, centering plus finite Cauchy yields
  `E_global <= 2*(#Q+1)*PointwiseDiagonalBudget*AverageDiagonalBudget`.
- `kloostermanGlobalFrequencyCollisionEnergy_Icc_le_centered`: literal `Finset.Icc 1 N` source
  specialization with exact residue multiplicities.

This replaces direct `#Q*(#Q-1)` finite-Cauchy aggregation by one `#Q+1` collective factor and
two aggregate diagonal budgets. At comparable modulus/source weights this saves one full family
cardinality. It is not the full paper-scale Kuznetsov saving.

Verification:

- direct `lake env lean` source check passed;
- targeted leaf build passed: `13508/13508`;
- all three new theorems audit with only `[propext, Classical.choice, Quot.sound]`;
- module wired into `formal/GaloisForLFunctions/RHTower.lean`; umbrella not built.

Remaining exact core for the two E3 cards: stronger cross-modulus fourth-moment/Kuznetsov saving,
then Lemma 3.5(ii), amplification, and Matomaki--Teravainen Theorem 1.2.
