# The unshifted Weil Hilbert space before contact

- **ID:** R0411-PRECONTACT-HILBERT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.5.1
- **Statement:** Every positive aperture strictly below `a*(ζ)` carries the complete literal Weil inner product, with dense smooth core and compatible isometric aperture inclusions.

## Proof

Write `V_a` for the archimedean form domain, `J_a` for its physical embedding,
`B_a` for the bounded prime-polar remainder, and `μ_a` for the actual ground energy.
Strict decrease and the unique-contact law imply `μ_a>0` for `0<a<a*(ζ)`.
The parameter interval is nonempty: it contains `181/500`.

The exact identities

`Q_a(u)=‖u‖²+Re⟨B_aJ_au,J_au⟩`, `μ_a‖J_au‖²≤Q_a(u)`

give `‖u‖²≤(1+‖B_a‖/μ_a)Q_a(u)`. The bounded form operator gives the reverse
norm bound. Thus `Q_a` is positive definite, its norm is equivalent to the complete
form norm, and its smooth compact core remains dense. Polarized compatibility of
the literal form makes extension to every larger pre-contact aperture isometric;
the inclusions compose exactly.

## Lean certificate

Module: `GaloisForLFunctions/CanonicalSystemOfTheWindowTower/TheWeilFormIsCompleteBeforeContact.lean`.

- `precontact_groundEnergy_pos`, `basePrecontactAperture`
- `WeilHilbertBeforeContact.inner_eq_weil`, `instCompleteSpace`, `denseRange_smoothCore`
- `WeilHilbertBeforeContact.groundEnergy_mul_mass_le`
- `WeilHilbertBeforeContact.inclusion`, `inclusion_self`, `inclusion_trans`

Final `lake --old env lean` check passed. Six transitive audits report only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import added.

The continuum canonical equation, its prime-power singularities, and its contact
endpoint are not supplied by this Hilbert-space construction.
