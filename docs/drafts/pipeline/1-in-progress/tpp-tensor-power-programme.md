# The Tensor-Power Programme Ω (TPP) — programme card

- **ID:** TPP
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-1511/obstacles-summary.md §2.22 (best-shot proof route: the tensor-power programme Ω)
- **Statement:** carry Deligne's tensor-power argument to `Spec ℤ`: dissect the pole law (step iii), prove
  where it is missing, price every substitute frame, decide the pencil candidates, write the axioms of N1.

## Goal
Answer README §6 questions Q1–Q9 by Lean theorems; build the tools of README §7. Folder
`formal/GaloisForLFunctions/TensorPowerProgramme/`, umbrella `TensorPowerProgramme.lean`, README there.

## Corpus already owns (do not redo)
- Rankin/global-trace step over `𝔽_q`: AKT `tensor_moment_bound_iff`, `tensor_norm_pow_le_of_global_trace`.
- SL₂ invariants have det weight; golden Frobenius has a split SL₂ lift (AKT).
- Receiver-level tensor loss: linear loss = strip, fixed loss = RH (ACP `TheBaseIsAFixedLoss`); prime-trace
  moments ⇔ RH (SurfaceOfSpecZ `riemannHypothesis_iff_moments_primeTraces`).
- Family moments and fixed parts (IRP `member_norm_le_of_family_moments`).
- Frames, towers, walls, sign line, Stickelberger prices (FCT, EDCS); cubic correction = rung at 6s−3 (EDCS).

## Status
- README first draft written.

## Conjecture loop (ledger)
| # | Conjecture | Test | Status |
|---|---|---|---|

## Log
- 2026-11-15 — created; README draft.
