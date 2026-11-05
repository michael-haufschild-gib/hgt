# The Weil Riesz equation is a logarithmic Dirichlet equation

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every precontact Fourier-evaluation Riesz source belongs to the restricted operator domain of `1+(1/2)log(1-D²)` and has essentially bounded forcing, with every prime translation and both polar terms retained.

## Proof

Let `r` be the integrable even remainder in the exact Gamma decomposition,
`c=2∫₀∞r`, and `J` the physical embedding of the complete archimedean form domain.
Plancherel identifies the literal logarithmic form as

`q_log(u,v)=⟨u,v⟩-c⟨Ju,Jv⟩+⟨r*Ju,Jv⟩`.

Thus its bounded correction is `B_log=-cI+P_a(r*)P_a`.
For the actual Riesz source `u`, the completed Weil equation gives

`q_log(u,v)=⟨e_z+(B_log-B_Weil)Ju,Jv⟩`.

The Friedrichs representation theorem yields the exact operator-domain
membership and image. The source `Ju` is already essentially bounded.
Each translation preserves that bound, the complete prime sum is finite,
and both convolution kernels are integrable. Aperture compression and scalar
terms also preserve boundedness. Hence the displayed forcing is bounded.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheWeilRieszEquationIsALogarithmicDirichletEquation.lean`:

- `logarithmicDirichletForm_eq`
- `WeilHilbertBeforeContact.evalVector_logarithmic_operator_domain_and_apply`
- `WeilHilbertBeforeContact.evalVector_logarithmicForcing_bounded`

Production `lake --old env lean` and all three transitive axiom checks pass
with exactly `[propext, Classical.choice, Quot.sound]`. The umbrella imports it.
The half-line Green representation and normalized endpoint traces remain open.
