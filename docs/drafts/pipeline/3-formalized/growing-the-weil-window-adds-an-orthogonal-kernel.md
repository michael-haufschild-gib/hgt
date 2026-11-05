# Growing the Weil window adds an orthogonal kernel

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For precontact apertures `a≤b`, let `J:Hₐ→Hᵦ` be the actual Weil inclusion and `δ_z=vᵦ,z−Jvₐ,z`. Then `J* vᵦ,z=vₐ,z`, `δ_z⊥JHₐ`, and `Kᵦ(w,z)−Kₐ(w,z)=⟨δ_z,δ_w⟩`.

## Proof

Inclusion preserves every entire Fourier coordinate. Riesz uniqueness gives
the adjoint identity and orthogonality. Expanding both evaluation vectors
into their old and orthogonal components gives the exact Gram difference.
On the diagonal its real part is `‖δ_z‖²`.

## Lean

`CanonicalSystemOfTheWindowTower/GrowingTheWeilWindowAddsAnOrthogonalKernel.lean`:
`inclusion_adjoint_evalVector`, `inner_evalVectorIncrement_inclusion`,
`kernel_sub_eq_inner_increment`, `kernel_diagonal_sub_eq_norm_increment_sq`.

Plain Lean audit passes. All four printed declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. The module is wired into its umbrella.
The aperture derivative still requires the shrinking-collar limit.
