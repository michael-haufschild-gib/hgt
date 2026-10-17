# EGC enclosed-pole cancellation — 2026-10-17

## Scope and goal status

Current goal attachment: /Users/michael/.codex/attachments/96420293-cf9b-451e-9b1d-1fcd84b70704/pasted-text-1.txt. Objective remains active and incomplete. User requires one new route/candidate each turn, local Lean evidence only, no old research Markdown or web, no computations, no extra analytic premises or axioms, no full/umbrella builds, final lake --old env lean audit. Frontier map read-only. Attempts in this thread: XN, HF, IRK, EGC. No attempt credited as meeting strict significant RH-frontier criterion. Next turn select a different route/candidate.

## Exact result

New formal/GaloisForLFunctions/RHTower/PaperEGCEnclosedPoleCancellation.lean, 415 lines, wired after PaperEGCSourceLanding in RHTower.lean.

PaperEGCSourceRectangle packages positive orientation and actual continued-source boundary admissibility. Inside is strict coordinate interior. Exact finite factorization plus one-pole weighted argument principle gives the actual rational pair source contour with BOTH prescribed shifted residues:
I_R(e,w) = sum_(a in S_R) K_e(a,w) + (e/2)(L(w+e)-L(w-e)), L=logDeriv XiC.
For |e|, |Re w| <= 1, the source difference is the already constructed complete correction, and each enclosed K+C=1. Thus I_R = #S_R + complete C - finite interior C = #S_R + tsum exterior C, retaining all multiplicity copies.
Existing uniform copy convergence now supplies one finite cutoff controlling every containing source rectangle, every small shift and real offset, and every imaginary height for which both poles lie inside. No infinite contour/sum interchange.
Unconditional cofinal constructor: adjoin any actual Xi copy and its functional-equation reflection to requested finite packet. Native spectral gap puts real coordinates on opposite sides of [-2,2]; reflected imaginary coordinates straddle zero. Existing admissible rectangle constructor then encloses all centered shifts. Final existence endpoint has only n : Nat and F : Finset XiZeroCopy as inputs, no analytic assumptions.

Public theorems, namespace RHTower.PaperEGCSourceRectangle:
- enclosed_poles (line 122)
- enclosed_poles_eq_count_add_tail (277)
- enclosed_poles_eq_count_add_exterior (308)
- exists_uniform_contour_cutoff (327)
- exists_containing_centered_window (349)
- exists_uniform_centered_source_contour (390)

## Interpretation / honest frontier

This resolves an exact INNER enclosed-pole passage, not EGC's expanding-real-coordinate outer covariance. Complete cancellation removes pair information copy by copy and leaves unit multiplicity mass. It cannot alone force off-line pair charge to vanish. Centered negative full correction is canceled by the finite pair row's excess; it was not discarded or replaced by zero. No outer source sign, RH proof/equivalence, or significant-goal credit. Route remains live, not retired. Positive survivor is exact source/exterior decomposition plus actual cofinal construction.

Card with dependency-closed paper proof before Lean and failed second conjecture:
docs/drafts/pipeline/1-in-progress/egc-expanding-contour-source-2026-10-17.md

## Verification and cleanup

Final canonical command exit 0, no warnings:
lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/PaperEGCEnclosedPoleCancellation.olean GaloisForLFunctions/RHTower/PaperEGCEnclosedPoleCancellation.lean
Six public axiom audits exit 0; only propext, Classical.choice, Quot.sound. API scratch also passed. No sorry/admit/axiom/opaque/unsafe declarations, heartbeat changes, numerical experiments, full builds, or umbrella builds.
scripts/formal_tools.py index exit 0 twice. Final lint --check-generated exit 1 on unrelated concurrent changes: unwired PrimeLogLaplaceClosedGraphLiteral, ZeroAlgebraJetInvariantForms, BurnolWeightedShiftStrongContinuity; sorry in ZeroAlgebraJetInvariantForms.lean:382 exists_posDef_invariantForm; stale LEAN_OVERVIEW.md after concurrent change. No error mentions own EGC module. Do not claim global lint passed.
All /tmp/hgt_egc_* scratch removed using exact rm -- paths; absence verified. No owned active jobs. Canonical .olean retained. Frontier map not edited by us; shared worktree changed concurrently. No commits or pushes performed.

## Lean lessons

Open Complex BEFORE namespace RHTower; opening inside can resolve RHTower.Complex and silently introduce implicit I. For finite/complement tsum, explicitly change the generated Set-complement subtype to {a // a not in finset} before ring; ring treats syntactically different tsum binders as distinct atoms. Give explicit g1 := fun z => L z + P z for rectIntegral_add, since rewrite matching may not unfold function addition. Explicit g argument needed when rewriting order_sum under a sum.