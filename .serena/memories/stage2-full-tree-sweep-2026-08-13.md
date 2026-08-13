# Full Stage-2 sweep — 2026-08-13

Scope correction: user intends all of `docs/drafts/pipeline/2-fully-proven`, not only NHG. Initial count was 905 Markdown files, 861 carrying Stage-2 headers. Many Stage-2 files are intentionally retained paper-proof sources with separate Stage-3 certificates, so basename search across all of `3-formalized` is required before treating a card as open.

## Promoted this leg

1. `source-zero-to-horizontal-carrier.md` moved from Stage 2 root to Stage 3 root. Existing module `RHTower/SourceZeroHorizontalCarrier.lean` exactly covers nine principal declarations. Direct Lean passed; nine axiom prints only `propext`, `Classical.choice`, `Quot.sound`; targeted Lake build passed. Already imported by `RHTower.lean` in HEAD.
2. `not_new_scientific_knowledge/lean-claim-review-row-026-satake-lambda-ring-algebra.md` moved to matching Stage-3 subfolder. Exact six theorem bundle audited across `AdamsOperations.lean`, `SymPowerPlethysm.lean`, `EHKoszulDuality.lean`; combined build passed; axioms clean. Updated `docs/drafts/door/00-status.md` link/status.
3. `not_new_scientific_knowledge/ten-proofs-universal-permanent-specialization.md` moved to matching Stage-3 subfolder. Existing `HTGeometry/UniversalPermanentSpecialization.lean` exactly proves polynomial specialization, evaluation, and fiber-weight bridge. Direct Lean/build/axioms passed; imported in HEAD.
4. `not_new_scientific_knowledge/no-finite-boundary-audit-under-amplification.md` moved to matching Stage-3 subfolder. Added minimal `HTGeometry/FiniteBoundaryAmplificationNoGo.lean` and umbrella import. Capstone proves explicit one-dimensional rank-one witness: positive throughout `[0,T]`, zero at `T+1`, negative after every positive delta. Direct Lean and targeted build passed; six declarations axiom-clean. Repaired inbound link in `finite-rank-boundary-schur-index.md`.

## Important audits

- `gate-walk-green-bellman-tropicalization-law.md` is not ready: existing `HTGeometry/GateWalkGreenBellmanTropicalization.lean` proves only Theorem A Green sandwich core. Paper Theorems B tropical exponent, C soft Bellman/Harnack/Lipschitz, D probability bound, E entropy-temperature price are absent.
- `finite-carrier-spacelike-compression-defect.md` is already Stage 3 under `docs/drafts/pipeline/3-formalized/finite-carrier-spacelike-compression-defect.md`; Stage-2 copy is retained paper proof. Current module verification still passes.
- Top-level SourceZero was genuine missing promotion. Many `[LEAN-PROVED]` markers are partial and must not be trusted without exact theorem audit.

## Concurrency / validation

Only one owned Lean/build process was run at a time. Shared tree has concurrent edits. `formal/GaloisForLFunctions/HTGeometry.lean` already contained another agent's `FiniteAmplifierFrame` and duplicated tail imports; our only new line is `FiniteBoundaryAmplificationNoGo` near line 2127. `RHTower.lean` has another agent's tail import. Do not rewrite either umbrella wholesale.

Repo-wide `python3 scripts/formal_tools.py lint` currently fails only because another agent's untracked `HTGeometry/ConstraintRelativity/FactorFramedTensorJacobian.lean` is not wired into an umbrella. No promoted-card or new-module finding. Scoped forbidden-token scans passed.

No commit or push performed.