# Coherent Gamma payment on mean-zero intervals

- **ID:** acs-coherent-mean-zero-gamma-payment
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** ACS: source sections → Riemann–Roch and ampleness → Hodge index → RH.
- **Parent:** [balanced complete-cell effectivity](../1-in-progress/acs-complete-cell-haar-effectivity.md)
- **Statement:** The original Gamma Lévy form pays the full reciprocal-width logarithm times local square mass on a finite disjoint mean-zero interval family.

## Exact theorem

For intervals `I_i = (a_i,b_i)` with `0 < b_i-a_i ≤ 1`, pairwise ordered with disjoint interiors, and compact BV `f` satisfying `∫ I_i f = 0`,

`Σ_i log(1/(b_i-a_i)) * ∫ I_i f² ≤ levyEnergy f`.

Lean declaration: `GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals.levyEnergy_ge_sum_log_width` in `GammaMeanZeroCoercivity.lean`.

Intervals may touch, and `f` may be nonzero outside them. The energy retains the actual Gamma kernel.

For the actual adjacent balanced whole-cell profiles, `haarPairWidth` identifies the interval width as `logCellWidth a`. The unconditional specialization `haarSectionProfile_levyEnergy_ge` in `HaarCellGammaPayment.lean` gives

`Σ a∈[1,X], log a * haarMass a * c a² ≤ levyEnergy (haarSectionProfile c X)`

for every finite horizon and arbitrary real signed coefficients.

## Formalized argument

1. `GammaMeanZeroCoupling.lean` expands the actual Gamma density into its positive exponential series. The rank-one mean-zero inequality pays both far-end mass charges of every interval pair. Monotonicity and the zero-mean square identity pay each exterior-point charge.
2. `GammaMeanZeroCapacity.lean` partitions the whole-line symmetric integral into interval pairs and complement blocks. Summing the checked local inequalities yields `gamma_coherent_farCharge`; symmetry supplies both orientations.
3. `GammaMeanZeroEnergy.lean` proves `gammaDifference_eq_two_levyEnergy` for the actual compact BV source, using translation, Tonelli, and integrability from its Lévy square root. Two disjoint exterior windows give `log_width_le_gammaFarCharge`, with coefficient one.
4. `GammaMeanZeroCoercivity.lean` sums those logarithmic charges, cancels the common factor two in ENNReal, and converts back to the finite real energy.

## Verification

All five exact project files passed `lake --old env lean` from `formal/`. Eight transitive `#print axioms` audits contain only `propext`, `Classical.choice`, and `Quot.sound`. Imports are wired into the ACS umbrella; the umbrella was not built. Dependency artifacts were generated only for importing modules.

This discharges both the general Gamma estimate and its concrete balanced whole-cell specialization. The pole estimate and full Gamma–prime–pole floor remain on the parent card until their own Lean audits pass. Full-source ACS effectivity remains open.

## Log

- 2026-10-28 — Formalized and audited directly into stage 3; no stage-2 parking.
