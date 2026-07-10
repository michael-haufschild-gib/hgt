# Eventual symmetric-EM splits on one fixed isolating annulus

- **ID:** sem-eventual-fixed-annulus-splits
- **Stage:** 3-formalized
- **Type:** BRIDGE (Lean; standard compactness and uniform-convergence argument)
- **Lean:** `formal/GaloisForLFunctions/RHTower/SEMEventualSplit.lean`

## Statement

For every point `ρ` in the open critical strip there are fixed radii `0 < r₀ < R` such that:

- `ball ρ R` stays in the strip and contains no `xi` zero other than possibly `ρ`;
- for every sufficiently large truncation `N`, `completedSEM N` dominates `xi` on both slit
  annulus charts; and
- for every such `N`, there are `zs,u` with `SEMSplitData ρ r₀ R N zs u`.
- every two sufficiently large truncations are mutually joined on the charts by the explicit
  straight-line family `completedSEMLinearTransition`, which is nonvanishing for every
  `t ∈ [0,1]`.

The capstone is `semSplitData_eventually_exists_with_zeroFree_transitions`.  The supporting generic theorem
`eventually_domination_of_uniform_decay` upgrades a compact uniform error bound tending to zero
against a continuous nonvanishing target from one dominating member to eventual domination.
The pairwise version gives relative domination between every two large members.

## Significance and boundary

The earlier API selected one SEM truncation.  The strengthened theorem gives an honest discrete
family `N -> completedSEM N` on one common geometric domain, so transitions such as `N -> 2N` can
now be defined without changing annuli or reselecting split geometry.

This does not constrain the common hole count.  Every large split still has count
`(analyticOrderAt xi ρ).toNat`; count rigidity alone supplies no transition charge and does not
identify the attached `semHoleDefectZ` matrix with an analytic seam.

In fact the ordinary finite-to-finite annulus transition is zero-free.  Any boundary invariant
that is constant under such a homotopy sees no `N -> 2N` flux.  A realization of the local hole
model must therefore use a singular finite-to-limit boundary or a genuinely presentation-level
invariant; it cannot be the net winding of the large finite truncations against one another.

## Verification

- Focused compilation passes.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is introduced.
