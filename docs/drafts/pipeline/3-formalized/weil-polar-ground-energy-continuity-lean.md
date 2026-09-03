# Continuity of the pole-vanishing ground energy of the restricted Weil form — Lean certificate

- **ID:** `WEIL-ENTRY-001-L2`
- **Stage:** 3-formalized
- **Parent card:** `1-in-progress/weil-positivity-soft-prime-entry.md` (Theorem D)
- **Modules (all wired after `CCMRestrictedWeilPolarConstrainedRightContinuity` in `RHTower.lean`):**
  `CCMRestrictedWeilPolarBumpSources`, `CCMRestrictedWeilPolarConstrainedSmoothCore`,
  `CCMRestrictedWeilPolarGroundEnergy`
- **Axioms:** `[propext, Classical.choice, Quot.sound]`; lint clean; no hypotheses.

## Statements

`μ₀(a) := sInf { Q_a(u)/‖J_a u‖² : u pole-vanishing, J_a u ≠ 0 }` (`ccmRestrictedWeilPolarGroundEnergy`).

- `exists_polarConstrained_smooth_ne_zero`: at every aperture there is a nonzero smooth
  strict-interior source with both pole coefficients zero (centre bump corrected by two side
  bumps by Cramer's rule; `polarSideDet_pos` is the positivity of the side-bump moment
  determinant, from the moment bounds `m e^{sc − |s|r} ≤ ∫ e^{sx} φ ≤ m e^{sc + |s|r}`).
- `exists_polarConstrained_smooth_close`: pole-vanishing smooth strict-interior sources are dense
  in the pole-vanishing subspace of the form domain (form norm); the Cramer correction of a
  smooth approximant is bounded by `polarCorrectionConstant a` times the approximation distance.
- `ccmRestrictedWeilGroundEnergy_le_polar`: the unconstrained ground energy is below `μ₀`.
- `ccmRestrictedWeilPolarGroundEnergy_mul_le`: the constrained Rayleigh floor.
- `ccmRestrictedWeilPolarGroundEnergy_antitone`.
- `tendsto_ccmRestrictedWeilPolarGroundEnergy_suzukiRightAperture`: right continuity (from the
  constrained floor theorem of `WEIL-ENTRY-001-L1`).
- `exists_left_aperture_polarGroundEnergy_upper`: left continuity (constrained smooth
  near-minimizer with compact support strictly inside, restricted to smaller apertures; the
  pole coefficients of a smooth source are its exponential moments and do not depend on the
  aperture).
- `continuousAt_ccmRestrictedWeilPolarGroundEnergy`: `μ₀` is continuous at every aperture.
- `eventually_ccmRestrictedWeilPolarGroundEnergy_pos`: strict positivity of `μ₀` is open.

## Relation to the literature

Suzuki 2026 (arXiv:2606.09096) Theorem 1.3 is the continuity of the full-form lowest eigenvalue
(corpus: `continuousAt_ccmRestrictedWeilGroundEnergy`). The pole-vanishing version is new; it is
the one that matches Connes–Consani's and Yoshida's positivity statements at `√2`, which carry
the two pole-vanishing conditions. With it, Theorem D of the parent card reads: if
`μ₀(√2) > 0` then `μ₀ > 0` on an open interval around `√2`, so Weil positivity with the prime 2
holds on the pole-vanishing subspace beyond `√2`. The only input outside Lean is `μ₀(√2) > 0`,
which follows from Connes–Consani's Sonin inequality by `SoninStrictPositivityTransfer`.

## Lean notes

- Subscript characters `₊`, `₋` are not identifier characters; `c₊` fails to parse.
- `inner_smul_right` does not rewrite on the aperture subtype; go through `Submodule.coe_inner`,
  `Submodule.coe_smul` (`inner_smul_right_aperture`).
- `integral_ofReal` matches only up to instance paths; state the real integrand and use it as a
  `calc` step term, not with `rw`.
- `add_le_add_right h c` adds on the left in this toolchain; use `add_le_add h le_rfl`.
- `le_or_lt` is `le_or_gt`; `push_neg` is deprecated (`push Not at h`).
- A `have h := norm_nonneg x.toCCMFormVector` without a type ascription leaves a metavariable.
