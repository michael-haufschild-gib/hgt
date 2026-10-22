# Sonin coupled relative-determinant sector-confined phase universality law

## Status

In progress — paper proof and generic transfer core exact-checked; full Lean source check deferred
until the final dependency audit; literature novelty audit pending.

## Theorem-first provenance

- `RHTower/PrimeArchBernsteinSectorConfinedPhase.lean`
  - `tendsto_primeArchEndpointBernsteinPurity_div_pow_of_sectorBase_sq_lt`
  - `exists_strict_sectorConfined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis`
  - `xiSectorConfinedBernsteinAmplitudeBase_sq_eq`
- `RHTower/SoninCoupledNormalizedDeterminantCollar.lean`
  - `primeArchEndpointBernsteinPurity_le_two_add_two_relativeDeterminantPurity`
  - `soninCoupledEndpointBernsteinMismatch_eq_relativeDeterminantPurity`
- `RHTower/SoninCoupledBernsteinCollarQuantumDischarge.lean`
  - `soninCoupledEndpointBernsteinMismatch_le_two_add_two_primeArchEndpointPurity_quantum`

## Universal law

Every nondegenerate coupled-Sonin aperture inherits the exact endpoint phase ceiling
`(501/500)^2 = 251001/250000`.  Its concrete relative determinant logarithmic-derivative Bernstein
energy decays after normalization by every exponential base above that ceiling.  If RH fails, the
same determinant energy has a nondecaying base strictly between one and the ceiling.

Thus every aperture—not merely the endpoint source—occupies the same sharp five-per-mille phase
chamber, despite defining a different concrete normalized relative spectral determinant.

## Paper proof

For nonnegative sequences, an estimate `E_n ≤ 2 + 2D_n` transports decay of `D_n/r^n` to decay of
`E_n/r^n`, since the additive constant divided by `r^n` vanishes for `r>1`.  The contrapositive
transports nondecay in the reverse direction.  Apply this twice to the exact two-sided endpoint/
Sonin Bernstein comparison, replace Sonin mismatch by the exact relative-determinant purity, then
insert the endpoint source's unconditional decay above `251001/250000` and its false-RH surviving
phase below that ceiling.

## Lean status

Source complete in
`formal/GaloisForLFunctions/RHTower/SoninCoupledRelativeDeterminantSectorConfinedPhaseUniversalityLaw.lean`.

The generic affine energy-transfer lemma exact-checks in `/tmp/check_law194_transfer.lean`.  Full
source check is deferred because the current cache lacks
`GaloisForLFunctions/RHTower/SoninCoupledPrimeResidual.olean`; no dependency build was run before
the final audit.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only. Corpus search found
the endpoint chamber, two-sided coupled-Sonin comparison, and determinant-defect identity, but no
theorem transported the exact phase ceiling and false-RH surviving exponent to every aperture.
