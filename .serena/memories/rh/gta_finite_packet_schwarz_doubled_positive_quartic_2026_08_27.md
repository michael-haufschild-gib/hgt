# GTA finite-packet Schwarz-doubled positive quartic realification (2026-08-27)

## Result
For any finite type ι and packet z : ι → ℂ, define total real-even, real-odd, and Schwarz-doubled source moments by applying the local (7,5) source-pair lift to (Re z_i, Im z_i) and summing.

Lean proves:
- total graded anomalies in degrees 1 and 2 vanish;
- degree-4 anomaly equals the real charge
  Σ_i 100 (Im z_i)^2 (6 (Re z_i)^2 + 23 (Im z_i)^2);
- charge is nonnegative;
- charge = 0 iff every z_i is real;
- charge > 0 iff some z_i is nonreal;
- charge and every all-degree anomaly are invariant under pointwise Schwarz conjugation;
- charge and every anomaly are invariant under arbitrary finite reindexing.

No conjugation-closure or choice of one representative per conjugate pair is required, because source packet is Schwarz-doubled canonically.

## Files
- formal/GaloisForLFunctions/HTGeometry/FinitePacketSchwarzDoubledPositiveQuarticRealification.lean
- docs/drafts/pipeline/3-formalized/finite-packet-schwarz-doubled-positive-quartic-realification.md
- umbrella import in formal/GaloisForLFunctions/HTGeometry.lean

## Verification
- /tmp scratch and direct tree lake env lean passed
- targeted lake build of exact module passed
- scripts/formal_tools.py lint passed
- #print axioms: propext, Classical.choice, Quot.sound only

## Route impact
This closes finite spectral assembly and avoids the entrywise no-go: positive quartic orientation now works for arbitrary finite Schur/root packets, is relabel invariant, and does not require pair selection. Remaining GTA core:
1. exact Schur packet transport for actual theta stage (if not already reducible from existing Schur theorems);
2. source-side law forcing packet quartic charge to vanish. That law is RH-strength once tied to all actual stages.

See `mem:rh/gta_positive_quartic_realification_and_entrywise_nogo_2026_08_27` and `mem:rh/gta_symmetric_graded_quartic_classification_2026_08_27`.

Novelty remains [NOVELTY UNVERIFIED].