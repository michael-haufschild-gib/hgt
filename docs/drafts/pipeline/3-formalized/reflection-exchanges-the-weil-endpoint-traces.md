# Reflection exchanges the Weil endpoint traces

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Physical reflection and conjugate reflection act pointwise on the actual continuous precontact Riesz sources. Their normalized traces satisfy `τ₊(z)=τ₋(−z)` and `τ₋(conj z)=conj(τ₊(z))`; `τ₊(0)=τ₋(0)` is real.

## Proof

The complete archimedean reflection preserves the unshifted Weil quadratic
form, hence defines an isometry of the actual precontact Hilbert space.
Physical Fourier reflection reverses the parameter. Riesz uniqueness gives
`R v_z=v_{−z}`. Conjugate reflection agrees with the completed sharp
involution on the dense smooth core; continuity extends the physical identity.

Uniqueness of continuous representatives turns both almost-everywhere source
identities into pointwise identities. Applying the established normalized
endpoint limits and uniqueness of limits gives both trace relations. At zero,
reflection identifies the traces and conjugation makes their common value real.

## Lean

`CanonicalSystemOfTheWindowTower/ReflectionExchangesTheWeilEndpointTraces.lean`:

- `reflection`, `physical_reflection`, `evalVector_reflection`.
- `physical_sharp` and both continuous-representative symmetries.
- `evalVectorRightTrace_eq_leftTrace_neg`, `evalVectorLeftTrace_conj`.
- `evalVectorRightTrace_zero`, `evalVectorLeftTrace_zero_im`.

Plain Lean audit passes. All eight printed declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. The module is wired into its umbrella.
Nonvanishing of the common zero trace and aperture evolution remain open.
