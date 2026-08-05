# Static Choi complexity plateau: Pauli ensemble closed in Lean (2026-08-05)

Card moved `2-fully-proven` → `3-formalized`:
`docs/drafts/pipeline/3-formalized/universal-static-choi-complexity-plateau.md`.

## What was actually missing

Everything abstract was already built (`StaticChoi*`, `SyndeticDenseOrbitLaw`,
`FiniteSpectralRecurrenceFrequencyLaw`), and the finite Anderson family was transferred
(`FiniteAndersonChoiComplexityAlternationLaw`).  The card's *own* headline ensemble — the
full-density fixed-`q` traceless Pauli ensemble, `q ≥ 2` — had no transfer module, even though
its projective-genericity input had been formalized on the
`generic-two-local-spectral-monodromy` card (already stage 3).  Two new modules closed it.

## New modules

`GaloisForLFunctions/HTGeometry/PiMeasureAbsoluteContinuity.lean`
- `pi_absolutelyContinuous_pi` — coordinatewise `≪` for σ-finite families passes to `Measure.pi`
  over `Fin n`.  **Not in mathlib.**  Proof: induct on `n`, split one coordinate with
  `measurePreserving_piFinSuccAbove`, apply `Measure.AbsolutelyContinuous.prod`, transport back
  with `MeasurableEquiv.map_symm_map`.  Base case is `Measure.pi_of_empty` on both sides.
- `productGaussian_absolutelyContinuous` — a nondegenerate product Gaussian on `Fin N → ℝ` is
  `≪ volume` (`volume_pi` + `ProbabilityTheory.gaussianReal_absolutelyContinuous`).

`GaloisForLFunctions/RHTower/PauliTracelessChoiComplexityPlateauLaw.lean`
- `pauliRegisterEquiv (hd : d + 1 = 2 ^ n) : Fin (d+1) ≃ FiniteQubitConfiguration (Fin n)`;
- `pauliTracelessChoiEnergy`, `maximallyProjective_pauliTracelessChoiEnergy` (via
  `MaximallyProjectiveEnergy.comp_equiv`, which already existed in
  `PauliBoundedHamiltonianLocalityLaw`);
- `pauliTraceless_completedTime_paddedCircuitTargets` (eq. 4),
  `pauliTraceless_pureChoiTraceHardTimes_syndetic` (eq. 5),
  `pauliTraceless_pureChoiComplexity_alternates_syndetically` (ordered alternation);
- `*_ae` variants for every `μ ≪ volume` coefficient law;
- `pauliTracelessGaussian_*_ae` — the literal Gaussian-ensemble instances.

All axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
`lake build GaloisForLFunctions.RHTower` and `... .HTGeometry` both green.

## Reusable facts

1. The generic-two-local monodromy card exposes exactly the two hooks a downstream card needs:
   `pauliTraceless_simple_and_projectivelyIndependent_generically` (dense/residual/full-measure +
   `MaximallyProjectiveEnergy`) and `pauliTraceless_projectivelyIndependent_ae` (for `μ ≪ volume`).
   The traceless family `pauliTracelessFinPolynomialMatrix n q` is the card's `V_(n,q)`; the
   identity-included family is `pauliBoundedFinPolynomialMatrix n q`.
2. The corpus convention for "full-density ensemble" is `μ ≪ volume`.  A literal Gaussian
   instance now exists and costs one line given `productGaussian_absolutelyContinuous`.
3. Every `StaticChoi*` capstone takes `energy : Fin (d+1) → ℝ` plus
   `MaximallyProjectiveEnergy energy`.  Transferring a new physical family therefore only needs
   an index relabelling and that one hypothesis — no re-proof of the plateau machinery.
4. `Fintype.card (FiniteQubitConfiguration (Fin n)) = 2 ^ n` is closed by `simp`
   (`FiniteQubitConfiguration σ = σ → Bool`).

## Open on this card

Only gate 3 → 4.  Quantitative claims about the alternation gap `L`, first hard time, linear cut
time, or first low-complexity recurrence stay outside the theorem and need new
Diophantine/no-shortcut input.  A fixed-`q` nearest-neighbour qudit chain is a *different*
ensemble, is not claimed by this card, and its genericity proof is not manuscript-authorized.
