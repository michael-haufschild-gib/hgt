# Ticket: lee-yang-localization split formalized — door updates + deferred maintenance

Date: 2026-07-16. Agent: Fable.

## Door index/status updates (00-index.md / 00-status.md)
- Row #96 / G7 (`lee-yang-localization`): structural half now **3-formalized** via split ticket
  `pipeline/3-formalized/not_new_scientific_knowledge/lee-yang-marginal-forcing-structure.md`
  (four unconditional Lean modules: `HTGeometry/LeeYangForcingThreshold`,
  `HTGeometry/LeeYangTwoSpinCircle`, `HTGeometry/PencilPositivityRay`,
  `RHTower/LeeYangMarginalCarrier`; standard axioms only; zero warnings).
  Apex (marginal real-rootedness = RH) unchanged, open, quarantined as unasserted `↔`.
- New §4b on the parent card: invariant decomposition (margin sign ⊕ boundary bit); boundary bit
  free for closed loci; apex = threshold-location equality; underdetermination theorems make the
  §4 hardness mechanism formal.
- `dewitt-supermetric-no-margin` gate 2→3: partially advanced — the pencil cone/threshold
  structure (`pencilPositivityLocus` up-set + closed + no-margin corollary
  `pencil_posSemidef_iff_csInf_eq_one`) is now in-tree; still open there: the operator-norm
  identification `λ_c = ‖A^{-1/2} P A^{-1/2}‖`, the finite-to-infinite Hankel limit, the
  dBN transport, the RH equivalence.

## Deferred maintenance (user directive 2026-07-16: no further builds/scripts this session)
1. Physically relocate `pipeline/0-backlog/lee-yang-localization.md` →
   `pipeline/2-fully-proven/not_new_scientific_knowledge/` (Leaner's split condition is met).
2. Run `scripts/formal_tools.py index` (four new modules added; LEAN_OVERVIEW/LEAN_API stale).
3. Run the lint gate `scripts/formal_tools.py lint --check-generated`.
4. Umbrella-target builds (`+GaloisForLFunctions.HTGeometry`, `+GaloisForLFunctions.RHTower`) —
   leaf modules all build green individually; umbrella imports appended and inspected, but the
   umbrella elaboration itself has not been re-run.
