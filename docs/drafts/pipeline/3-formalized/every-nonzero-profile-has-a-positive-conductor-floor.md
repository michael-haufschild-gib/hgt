# Every nonzero compact profile has a positive conductor floor

- **ID:** every-nonzero-profile-has-a-positive-conductor-floor
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Σ1d, the profile floor needed for growing conductor spans.
- **Statement:** If `φ` is real, `C²`, supported on `[0,1]`, and `M=∫φ²>0`, then `∫_(t>c)|φ̂(2πt)|²dt>0` for every real `c`. Hence all completed conductor energies have a common positive floor on every bounded positive-overlap interval.

## Proof

If the Fourier transform vanished on a real half-line, its entire extension
would vanish identically by the identity theorem. Compact-support Fourier
uniqueness would force `φ=0` almost everywhere, contradicting `M>0`.
Thus every tail contains a point with strictly positive squared Fourier modulus.
Continuity gives a positive lower bound on a small interval around that point;
integrability and nonnegativity give a strictly positive tail integral.

The existing `completedConductorEnergy_ge_shellTail` bounds every conductor
energy below by `(2/M)∫_(t>c)|φ̂(2πt)|²dt`. For `0<c≤K`, monotonicity of
the tail integral gives the common positive floor at `K`.

The required Fourier uniqueness is
`HTGeometry.ae_eq_zero_of_compactFourier_vanishing`; shell integrability and
the conductor comparison are in `MacroscopicOverlapConductorFloor.lean`.
The no-real-Fourier-zero assumption in the existing floor theorem is unnecessary.

## Lean

`CriticalArithmeticCorrelationTheory/EveryNonzeroProfileHasAPositiveConductorFloor.lean`:

- `exists_shellSpectrum_pos_gt`;
- `integral_shellSpectrum_pos`;
- `exists_uniform_completedConductor_floor`.

Direct Lean check passed. All three dependency audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. This floor alone does not prove whole-span coercivity.
