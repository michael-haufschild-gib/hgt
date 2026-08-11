# ULF stage-3 full sweep (2026-08-11)

## Goal
Every card in `docs/drafts/pipeline/2-fully-proven/universal-law-field/` must have its **complete
displayed surface** closed unconditionally in Lean, then be `git mv`-ed into
`docs/drafts/pipeline/3-formalized/universal-law-field/`.

## Persistent work list — READ THIS FIRST
`docs/drafts/pipeline/2-fully-proven/universal-law-field/_STAGE3-SWEEP-LEDGER.md`
Rows are `DONE` / `HARD — <precise missing item>` / `NEEDS-LEAN — <note>` / `OPEN`.
As of this checkpoint: **67 DONE**, 3 OPEN (new concurrent cards), 12 NEEDS-LEAN, ~14 HARD.

## Per-card loop
1. Read the card; list every displayed theorem/corollary/calibration/countermodel.
2. Read the named `GaloisForLFunctions.HTGeometry.*` module declarations.
   **Card Lean tables lie** — audit statements, not names.  Cards also state their own gaps in a
   "Lean certification boundary"/"paper-only" sentence: grep for `paper-only`, `remain`, `pending`.
3. Close the gaps; `lake env lean <file>`; wire new modules into `UniversalLawField.lean`;
   `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`; `#print axioms`.
4. Promote with `scratchpad/promote.py <rel> "<log line>"` (chdirs to the repo root itself):
   it sets `- **Stage:** 3-formalized`, appends the log line, `git mv`s the card, and updates the
   ledger.  Two special cases are handled: a stage-3 *companion* already occupying the card's
   filename is renamed `<name>-formalized.md`; a stale stage-2 *duplicate* of an already-promoted
   card is `git rm`-ed after the log line is appended to the stage-3 copy.

## Traps hit
- Umbrella name collisions are invisible to `lake env lean` (`analyticOnNhd_iteratedDeriv` already
  lived in `HTGeometry.UpperEndPrimeLogJets`).  Scan declaration names repo-wide first.
- `⁅x,y⁆` needs `open scoped commutatorElement`.
- `Nat.find` in a *statement* needs `open Classical` on the whole section, not the `classical`
  tactic — otherwise the decidability instances differ and `omega`/`rw` silently fail to see
  hypotheses.
- Some modules import only fragments of Mathlib (`ConstitutiveEndogenousViability` had no
  `Mathlib.Topology.Order.Basic`); add imports rather than assuming `import Mathlib`.
- The lint gate fails on Lean *warnings* (unused `simpa`, unused simp args, unused binders).
- The Bash tool's persisted cwd is `formal/`; always `cd` explicitly or let the script chdir.

## New Lean built this session
`HTGeometry.PoleUnitFormationAnalytic`, `HTGeometry.PoleUnitGammaBase`,
`HTGeometry.PoleUnitEulerShell` (three new modules for ULF-PUFM-2), plus additions to
`ConstitutiveCoefficientLiftTransgression`, `ConstitutiveViabilityCoercivityTransmutation`,
`ConstitutiveExchangeCentralPromotion`, `ConstitutiveExchangeStrictification`,
`ConstitutiveChallengeProlongation`, `ConstitutiveAdversarialLawStress`,
`ConstitutiveLawSaturation`, `ConstitutiveMutationalGenesis`, `NormingFaceFusion`,
`CalibrationSpectrumMechanics` (weighted triangle equality case),
`ConstitutiveProspectiveChallengeGeometry` (pseudoultrametric gauge),
`ConstitutiveFailureKernelTransversal`, `ConstitutiveTVConflictColoring`,
`ConstitutiveEndogenousCompatibility`, `ConstitutiveEndogenousViability` (three countermodels).
