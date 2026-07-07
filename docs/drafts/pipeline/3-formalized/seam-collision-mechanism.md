# The signature-collision mechanism: an off-line zero is a resolved Krein collision

- **ID:** seam-collision-mechanism
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]` + formalized, axiom-clean
- **Source:** ../../door/bucket-the-seam-archimedean-obstruction.md · G5 seam line; transposes Krein–Gelfand–Lidskii stability theory to the ξ functional equation
- **Statement (delivered):** `[PROVED HERE]` In the factored FE seam Krein form `Σ w w* − Σ u u*` (`w = e+a`, `u = e−a`, `a_j=(t−z_j)⁻¹`, `e_j=(t̄−z_j)⁻¹`), the negative carrier `u` is the collision **order parameter**:
  - `seamU_eq_zero_iff_online` — `u = 0` iff the FE pair is on the critical line (`Im t = 0`, where `t=t̄` so `e=a`). The negative carrier vanishes exactly at the collision point.
  - `carrier_merge_online` — on the line, `w = 2a` and `u = 0`: the 2D hyperbolic plane `span{w,u}` of opposite Krein signatures collapses onto the single positive line `ℂ·a`. The collision made literal (the negative eigendirection becoming parallel to the positive and annihilating).
  - `kreinNonneg_of_online` — all pairs on the line ⟹ the seam form is `Σ w w*`, positive semidefinite, with the positive polarization given **explicitly** by the `w` carriers. Collision unresolved ⟹ no negative direction.
  - `offLine_opposite_signature` — off the line the carrier is indefinite: a strictly positive AND a strictly negative Krein direction (opposite signatures separated). Collision resolved ⟹ off-line zero.
  - `collision_at_critical_line` — via `t=(ρ−½)(−i)`, the order parameter vanishes iff `Re ρ = ½`.
  - `collision_mechanism` — packaged.
- **Lean:** `RHTower.{seamU_eq_zero_iff_online, carrier_merge_online, kreinNonneg_of_online, offLine_opposite_signature, collision_at_critical_line, collision_mechanism}` in `formal/GaloisForLFunctions/RHTower/SeamCollisionMechanism.lean`. `#print axioms` = {propext, Classical.choice, Quot.sound}. `lake build` green.

## Novelty and honest scope
The genuinely new content — a bridge, not a repackaging — is the identification of `u = e−a = (t̄−z)⁻¹−(t−z)⁻¹` as the **explicit signature-collision order parameter**, its vanishing characterization (`u=0 ⟺` on the line), the mode-merge (2D→1D plane collapse), and the **constructive** positive polarization (`Σ w w*`). This transposes Krein–Gelfand–Lidskii stability theory (a mode leaves the axis only through an opposite-signature collision, at which the form degenerates) to the ξ functional equation, giving the *mechanism* of zero-birth rather than only the count. A literature search of RH work would not produce "u=e−a is the collision order parameter"; the source is Hamiltonian stability theory.
- **Reused (not new):** the opposite-signature-off-line fact is `CarrierPickKernel.conj_pair_carrier_indefinite`, re-exposed in the collision language.
- **Scope:** this is the finite-carrier / Pick-Gram model (the same setting as the existing seam Krein program), not a statement about the full infinite ξ operator. It is the mechanism made explicit within that finite-shadow program.

## Log
- 2026-07-07 — created directly in 3-formalized (wide/deep research → order parameter + merge + explicit polarization + Lean).
