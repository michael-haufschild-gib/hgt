# Gelfond--Schneider Prop discharge in RHTower

- **ID:** rhtower-gelfond-schneider-discharge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[SEARCH]` / `[BRIDGE]`
- **Source:** arXiv:2603.24823 and the linked Apache-2.0 Mathlib branch at commit `9710b82b966813f7664819bc5d25b82d209a05e7`
- **Statement:** Prove `GaloisForLFunctions.RHTower.GelfondSchneider` inside the pinned RHTower toolchain, then remove that Prop premise from `log_ratio_transcendental` and its real-form bridge.

## Goal

Replace the explicit unproved `GelfondSchneider` Prop interface in
`formal/GaloisForLFunctions/RHTower/GelfondSchneider.lean` by a trusted Lean theorem.  This is
known mathematics and an existing external formalization, not new scientific knowledge.  It is the
first algebraic-transcendence foundation below the harder Baker and Schanuel interfaces.

## Gates

- [x] 0 -> 1 in-progress: exact consumer identified; published formal proof and source commit found;
  no failed in-tree attempt exists.
- [x] 1 -> 2 fully-proven: complete proof chain available under the repository's pinned Mathlib
  version, with the exact RHTower statement derived on paper and in Lean.
- [x] 2 -> 3 formalized: theorem `gelfondSchneider_holds : GelfondSchneider`; conditional premise
  removed from the concrete log-ratio consumer; target modules build; axiom audit and formal lint pass.
- [ ] 3 -> 4 publication-ready: not applicable as new science; retain provenance and license notice.

## Approach

1. Reuse the published Gelfond--Schneider Lean proof rather than rebuild a known theorem by
   zero-shot reconstruction.
2. Port only its real proof dependencies into a project-local theorem path; do not add aliases or
   merely restate `GelfondSchneider`.
3. Restore the explicit Siegel-lemma constant hidden by Mathlib 4.30 as a proved local bridge.  The
   upstream proof needs a named constant uniform in the auxiliary parameter, so replacing it by an
   arbitrary per-parameter bound would be mathematically insufficient.
4. Prove the complex theorem, derive `GelfondSchneider`, and rewrite the existing consumer so no
   `hGS` argument remains.

## Open core

`[CLOSED]` The published auxiliary-function proof now builds under this project's Lean 4.30/Mathlib
4.30 API.  A proved explicit-constant Siegel bridge replaces the private Mathlib constant, and the
analytic-order layer uses the merged Mathlib declarations directly.

## Log

- 2026-07-10 -- created in `1-in-progress` after a direct RHTower Prop-interface audit.  Scratch
  verification: upstream `AnalyticPart.lean` compiles on Lean 4.30 after using Mathlib's merged
  `analyticOrderAt_iterated_deriv`; upstream `MainAlg.lean` compiles after one `Nat.zero_le` API
  adjustment.  No repository Lean source has yet been changed.
- 2026-07-10 -- formalized.  Added the complete algebraic, analytic-order, norm-bound,
  holomorphic-estimate, and contradiction chain under `GelfondSchneiderProof`; proved
  `gelfondSchneider_holds`; made the real theorem and `log_ratio_transcendental` unconditional.
  Targeted build and formal lint pass.  Axiom audit for all three public conclusions reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
