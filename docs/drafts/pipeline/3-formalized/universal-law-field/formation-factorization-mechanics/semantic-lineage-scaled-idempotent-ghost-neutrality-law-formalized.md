# Semantic--lineage scaled-idempotent and ghost-neutrality law — Lean certificate

- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/formation-factorization-mechanics/semantic-lineage-scaled-idempotent-ghost-neutrality-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/ConstitutiveSemanticLineageWittFusion.lean`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Stage:** 3 — formalized
- **Date:** 2026-08-12

## Certified declarations

1. `certificateSemanticPacket` and `certificateLineagePacket` construct the two factorization legs
   for an arbitrary finite family of linear equivalences.
2. `certificateSemantic_comp_lineage` proves exact common recovery
   `B_A Q_A = |ι| I`.
3. `certificateFormedCarrier_comp_self` proves scaled idempotence
   `P_A^2 = |ι| P_A`.
4. `certificateFormedCarrier_pow` proves the complete positive-power law.
5. `certificatePointwiseGauge_formedCarrier` proves every certificate carrier is conjugate to the
   identity-certificate carrier.
6. `certificateRecoveryGhost_eq` proves every recovery ghost equals
   `|ι|^(n+1) I`.
7. `certificateRecoveryGhost_succ` proves the exact first-order ghost recurrence.
8. `certificateRecoveryGhost_certificate_independent` proves complete certificate blindness of the
   ghost packet.
9. `certificateRecoveryGhost_eq_oneModeWitt` identifies the operator ghost with the one-mode Witt
   ghost.
10. `semanticLineageWittFusion_unconditional` packages recovery, scaled idempotence, conjugacy, and
    ghost neutrality in one theorem.

## Exact meaning

Lean certifies that formed-carrier polynomial and ghost data cannot recover certificate history.
The constitutive information lives in the factorization fibre `(B_A,Q_A)`, not in the formed
operator `Q_A B_A` or its recovery ghosts. This is an exact no-go for carrier-only selection, not an
RH theorem and not a claim that factorization work is already source-normalized.

## Audit

- Direct check:
  `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveSemanticLineageWittFusion.lean`
- Leaf build:
  `lake build GaloisForLFunctions.HTGeometry.ConstitutiveSemanticLineageWittFusion`
- Umbrella build:
  `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`
- Direct check passed without warnings.
- Leaf build passed.
- Umbrella build passed with 11,838 jobs.
- Scratch axiom audit: core capstones use only `propext` and `Quot.sound`; the one-mode Witt bridge
  additionally uses `Classical.choice`.
- Repository lint found no issue in this module; the global nonzero status at audit time came only
  from unrelated shared-worktree umbrella-reachability debt.

No theorem uses an RH premise, Xi specialization, added axiom, `sorry`, `admit`, `unsafe`, or opaque
proof.
