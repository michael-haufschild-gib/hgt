# Theta center-mixed Ptolemy transport (2026-08-28)

New Lean module: `formal/GaloisForLFunctions/RHTower/ThetaCuspCenterMixedPtolemyTransport.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean`.

For fibre `P_u(s)=thetaCuspFullSource(u+s)*thetaCuspFullSource(u-s)`, define drops `A_u=P_u(0)-P_u(t)`, `B_u=P_u(t)-P_u(2t)`, `T_u=P_u(0)-P_u(3t)`, wall `W_u=A_u*T_u-B_u^2`. For `t>0`, `A_u>0`. Exact polarization identity:
`A_u*T_v + A_v*T_u - 2*B_u*B_v = (A_v/A_u)*W_u + (A_u/A_v)*W_v + A_u*A_v*(B_u/A_u-B_v/A_v)^2`.
Thus fibrewise nonnegative walls imply cross-fibre polarization nonnegative.

Weighted product-space integral of the polarization kernel equals exactly `2 * thetaCuspCenterMixedOddParityWall a t`. Consequently nonnegative walls only for positive centres `u>0` suffice for physical center-mixed odd-wall nonnegativity. Contrapositive is sharp: any negative physical wall yields `u>0` with a negative literal completed-source fibre wall.

Public theorem names:
- `thetaCuspReflectedSourcePtolemyPolarization_eq_defects_add_ratioSq`
- `thetaCuspReflectedSourcePtolemyPolarization_nonneg`
- `integral_thetaCuspCenterMixedPtolemyPolarizationKernel`
- `thetaCuspCenterMixedOddParityWall_nonneg_of_sourceFibres`
- `exists_thetaCuspReflectedSourceOddParityWall_neg_of_centerMixed_neg`

Verification: `lake env lean` passes; exact targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspCenterMixedPtolemyTransport` passes; axiom audit only `[propext, Classical.choice, Quot.sound]`; targeted forbidden-token search and `git diff --check` pass. Full `formal_tools.py lint` currently fails only on unrelated externally-created unreachable modules, not this module. Frontier map remained read-only.

Failed stronger conjectures: generic correlation-angle concavity/convex log action is insufficient; monotone ordinary curvature `P''/P` leaves a signed integral balance; atomwise PSD is ruled out by existing first-second cross signed-second obstruction. Exact remaining rank-four core: prove `thetaCuspReflectedSourceOddParityWall u t >= 0` for every `u>0,t>0` using coupled completed-source likelihood structure.

Card updated: `docs/drafts/pipeline/1-in-progress/theta-center-mixed-odd-four-point-cusp.md`. Related memories: `mem:research/theta_center_mixed_global_coalesced_ptolemy_2026_08_28`, `mem:research/theta_center_mixed_rank_four_even_global_2026_08_28`, `mem:research/theta_center_mixed_strict_first_jet_2026_08_28`.