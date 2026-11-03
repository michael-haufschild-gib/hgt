# Receiving charge in the complete form at critical overlap

- **ID:** Q6-CHARGE
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0311/fable.md`, §7
- **Statement:** Classify the exact complete Weil energy and its mixed pairing with the complement on harmonic-pole-neutral coherent prime-charge families and their coprime conductor fibres at `c = 2K(log N)^(1/8)`.

## Required conclusion

Determine whether affine successor energy pays the prescribed receiving charge, shell–pole terms cancel it, or a signed residual remains. Retain every Gamma, pole, shell, overlap and finite-horizon term. Formalize the classification and its consequences without unproved analytic premises.

## Established inputs

- `exists_harmonic_neutral_physical_vanishing_charge`: prescribed constant generator charge survives arbitrarily small adjunction energy and normalized physical input, uniformly for `N ≥ Q`.
- `normalizedPrimeModeSource_mul_of_coprime`: generator derivation across coprime conductors.
- `completeWeilEnergy_packetVector_at_every_overlap`: exact complete-form decomposition into dilation and affine energies, diagonal, shell degree, centre, far-cross, pole-error and overlap terms.

## Open proof

Evaluate the decomposition on the explicit normalized coefficients, including harmonic projection and coprime fibres; compute the polarized complement pairing. Neither the vanishing-input theorem nor the general decomposition supplies this evaluation.

## Exact dilation calculation

For `F_b(n) = Σ_(p∈P) b_p(1_(p|n) − 1/p)` and `H_M = Σ_(n≤M) 1/n`,

`J_N(F_b) = Σ_(p∈P) b_p² (log p/p) H_(⌊N/p⌋)`.

Proof: a Mangoldt-supported dilation changes only one prime incidence coordinate, so its squared jump linearizes to the jump with coefficients `b_p²`. For a single integer divisibility indicator `I_d`, the binary increment satisfies `(I_d(kn)−I_d(n))² = I_d(kn)−I_d(n)`. The target divisor sum is `Σ_(d|n≤N) log n/n`; the source sum is `Σ_(d|n≤N) ψ₁(⌊N/n⌋)/n`. Reindex both by `n=dr`. The identity `Σ_(r≤M) ψ₁(⌊M/r⌋)/r = Σ_(r≤M) log r/r` cancels the cofactor terms, leaving `(log d/d)H_(⌊N/d⌋)`.

Constant subtraction preserves every jump. Thus the normalized coherent coefficients, including harmonic centering, give

`J_N = (t/B_Q)² Σ_(p≤Q) (log p/p)H_(⌊N/p⌋)`.

This is the unnormalized dilation term. The physical input in the cited theorem is normalized by `log N`; these quantities cannot be interchanged.

Lean: `jumpEnergy_divisibilityIndicator`, `jumpEnergy_incidencePacket_diagonal` in `ArithmeticCouplingTheory/ReceivingCharges/PrimeIncidenceDilationEnergy.lean`; `harmonicPrimeCharge_jumpEnergy`, `harmonicPrimeCharge_charge_and_adjunction` in `CriticalScaleArithmeticRigidity/ReceivingCharges/FiniteHorizonPrimeCharge.lean`. Individual checks passed, transitive axioms exactly `propext`, `Classical.choice`, `Quot.sound`; both modules integrated. This calculation does not settle cancellation in the complete form.

## Gates

- [x] Explicit families, overlap scale and complete-form receiver identified.
- [ ] Dependency-closed paper classification.
- [ ] Lean classification and consequences; individual `lake --old env lean` checks and standard-only axiom audit.
