# Cusp-supported profiles and global radial rigidity

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Height profiles supported above `1` form an exact pointwise functional calculus after pseudo-Eisenstein periodization. Their modular extensions are globally height-dependent only for the zero profile.

## Paper proof

Use the corpus normalization `Pψ(z)=Σ_(c,d) ψ(Im(M_(c,d)z))`, counting both signs. If `ψ` vanishes below `a>1`, the existing fundamental-domain theorem gives `Pψ(z)=2ψ(Im z)` on `𝒟`. The corpus invariant height `Y(z)=sup_γ Im(γz)` equals the height of a representative in `𝒟`. Modular invariance therefore gives `Pψ(z)=2ψ(Y(z))` globally and `support(Pψ)=Y⁻¹(support ψ)`.

For any map `H:ℂ→ℂ` with `H(0)=0`, reduction to `𝒟` proves
`P(H∘ψ)(z)=2H(Pψ(z)/2)` everywhere. In particular,
`Pψ(z)Pφ(z)=2P(ψφ)(z)` when both profiles vanish below `a>1`.

Any function on `ℍ` invariant under `S:z↦−1/z` and constant along every horizontal line is constant. For `0<y≤1`, the point `sqrt(y−y²)+iy` has norm squared `y`, so its `S`-image has height `1`. Hence its value equals the value at `i`. For `y>1`, inversion first replaces `iy` by `i/y`.

Consequently, global height dependence of `Pψ` forces constancy. Its value at `i` is zero, so its value everywhere is zero. Evaluating at `iy` for `y≥a` recovers `2ψ(y)`; the remaining profile values already vanish. Thus global height dependence is equivalent to `ψ=0`. Also, for every `y>1`, modular inversion gives `Pψ(i/y)=2ψ(y)`: a nonzero cusp-band profile has nonzero modular copies below height `1`.

## Scope

The fundamental-domain identity and cusp-form orthogonality already exist as `pseudoEisenstein_of_mem_fd` and `inner_incEisL2_eq_zero_of_mem`. The new statements identify the exact global support through invariant height, distinguish radiality on `𝒟` from radiality on `ℍ`, and record the resulting nonlinear profile algebra. They do not remove the Eisenstein scattering contribution or decide AAL.

## Lean

`BlackHoleRingdown/TheAlgebraOfCuspSupportedProfiles.lean`:

- `pseudoEisenstein_eq_profile_invHeight`, `support_pseudoEisenstein`: exact global representation and support.
- `pseudoEisenstein_comp`, `pseudoEisenstein_mul`, `pseudoEisenstein_conj_mul`: nonlinear functional calculus and product laws.
- `pseudoEisenstein_injective_on_profiles`: injectivity.
- `eq_at_I_of_height_dependent_of_inversion_invariant`, `pseudoEisenstein_height_dependent_iff`: global radial rigidity.
- `pseudoEisenstein_inverted_vertical`: modular copies of vertical profile values.

Direct check passed without warnings:
`lake --old env lean GaloisForLFunctions/BlackHoleRingdown/TheAlgebraOfCuspSupportedProfiles.lean`.
All nine public declarations have transitive axioms exactly
`propext`, `Classical.choice`, `Quot.sound`. Wired into `BlackHoleRingdown.lean`.
