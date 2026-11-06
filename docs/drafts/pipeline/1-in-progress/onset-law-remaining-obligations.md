# Remaining onset-law obligations

- **ID:** onset-law-remaining-obligations
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0411, §2.1, A36; original `window-visibility-onset-law` paper card.

## Exact outstanding statements

1. **Distinct ordinates.** The proved `k·pairEnergy(δ,a)≤L` equivalence concerns one
   site of multiplicity `k`. The exact distinct-cluster statement quantifies over every
   cluster in any prescribed neighbourhood of the ordinate: universal positivity holds
   iff `k·pairEnergy(δ,a)≤L`. A negative coincident test survives a small splitting.
   [Paper proof and Lean theorem](../3-formalized/distinct-coherent-clusters-have-the-multiplicity-threshold.md)
   are complete; direct source check and both transitive axiom audits passed.
   No fixed distinct cluster's Gram norm is equated
   with the sum of individual norms.
2. **Shallow necessity.** Under window positivity and general RvM bounds, prove the
   sub-depth coherent mass bound. Existing lattice-background hiding estimates and
   coincident-site exclusions do not supply this implication. The original displayed
   bound is `C A₀(a+1)log(|γ₀|+R+4)/a³`. For `a≥1`, depths `δ≤1/a` and
   `|γ−γ₀|≤δ/2`, plain unit-window counting already gives
   `Σmδ²≤2A₀log(|γ₀|+4)/a²`, without positivity. Thus the displayed order does
   not establish the claimed improvement; a nontrivial visibility gain requires a
   stronger statement or additional structure proved from the configuration.
3. **Logarithmic-height crystals: complete.** The lattice is cut below height `e^L`;
   a localizer with a high-order zero at height zero pays the removed points.
   [Paper proof and Lean theorem](../3-formalized/cut-crystal-hides-fixed-depth-at-logarithmic-aperture.md).
4. **Interferometer: complete.** The [formalized correction and audit](../3-formalized/two-bump-interferometer-retains-complex-amplitudes.md)
   prove `‖S(v)‖≤Re S(0)` and the reflected-pair identity
   `2 exp(iγv)(Re(c) cosh(δv)+i Im(c) sinh(δv))`.
   The cosh-only description omits the imaginary term. Final source check and
   six transitive axiom audits passed, including the existing two-bump identity,
   minor bound and reflection symmetry.
5. **Synthesis.** Incorporate the exact completed statements above.

## Existing inputs

- `WindowVisibilityLaw.windowPositiveAt_biquadraticCrystal_of_le`:
  `38aLδ² cosh(2δa)≤M`, `4a≤L` imply positivity.
- `WindowVisibilityLaw.exists_hidden_inv_aperture_zero_above_single_exp`:
  depth `1/a`, arbitrary centre index, no quantitative height-location conclusion.
- `WindowVisibilityLaw.dci_admissible_coherent_cluster_visible_at_sub_depth`:
  multiplicity model, not the general shallow necessity theorem.

No outstanding statement is certified by the renamed formalized card alone.
