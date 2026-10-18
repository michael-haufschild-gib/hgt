# Critical collar resonance and arithmetic dilation

- **ID:** APT-COLLAR-RESONANCE
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md`, topics 3–4.
- **Statement:** Determine the exact affine arithmetic skeleton and quantitative detuning of factorial shifted frequencies under prime dilation, then retain these couplings in the critical-envelope energy.

## Goal and scope

The active request is 100 significant, native APT contributions, each with an unconditional actual-source theorem, paper proof, novelty audit, and Lean certificate. Reading the attachment is initialization, not completion. Existing work is baseline, not credit toward this request. No result is counted merely because it adds a theorem or formalizes classical algebra. Current accepted count: **0/100**.

README is read-only. No numerical experiments, added axioms, full builds, or heartbeat increases. Use targeted `lake --old build` when dependencies need artifacts; final audit is `lake env lean` on each actual new leaf. Preserve existing shared changes, including the smoothing-channel module and envelope-module edit.

`update_plan` and `multi_tool_use.parallel` are unavailable in this session. This card tracks the plan; independent tool reads use `Promise.allSettled`. Serena symbol lookup on the Lean source reports the path ignored, so exact source reads are the available fallback.

## Plan

1. [x] Read all 92 lines of the field README, session instructions, relevant memories, WL/RW frontier, and exact collar/dilation sources.
2. [ ] Audit candidate against corpus and primary literature; identify overlap without treating missing search hits as novelty evidence.
3. [ ] Prove quantitative affine-clock defect and cross-scale resonance classification on paper.
4. [ ] Test the stronger proposed uniform nonstationary gain on actual source harmonics; retain a positive classification if it fails.
5. [ ] Formalize dependency-closed results, wire umbrella, run actual-leaf/axiom/lint audits.
6. [ ] Continue to a source-level critical prime budget; count only contributions meeting the original significance standard.

## Current exact input

`FactorialCollarIrrationalityAndSpacing.lean` proves

\[
4\lambda_N^3=N^2(4N+1),\qquad
1/15\le\delta_N:=\lambda_N-N\le1/12.
\]

It proves irrationality, a cubic equality criterion, and separation of `r λ_N` from `λ_(rN)`. It does not supply separation from every different scale. The envelope module's integration-by-parts theorem concerns a single base frequency and its dilation; applying it uniformly to all mixed scale pairs would need a new gap theorem.

## Conjecture loop

### C1: uniform cross-scale oscillatory gain

**Candidate to test:** high factorial scales force all shifted prime-dilation frequency gaps away from zero. This would allow a uniform integration-by-parts gain in the critical prime budget.

**Potential counterfamily:** `r=13`, `N=13M+1`. The affine clocks satisfy `N+1/12=13(M+1/12)` exactly. The exact cubic clocks remain distinct but may approach one another.

### C2: positive survivor — affine residue classification

Set `e_N=N+1/12−λ_N`. Cubic expansion gives the exact identity

\[
N e_N=\delta_N^2+\frac{\delta_N^3}{3N}.
\]

The existing collar bounds should imply `1/(225N) ≤ e_N ≤ 1/(140N)`. Consequently

\[
\lambda_N-r\lambda_M
=\frac{12N+1-r(12M+1)}{12}+r e_M-e_N.
\]

For `M≥r≥2`, a nonzero integer numerator gives a uniform gap; a zero numerator requires `r≡1 mod12` and forces a positive gap of order `r/M`. Prove both regimes with explicit constants, not numerical scans. This would identify exactly where the single-frequency oscillatory gain cannot transfer to mixed scales.

### C3: complete source consequence (open)

Use the arithmetic skeleton `12N+1` to isolate resonant shifted couplings and bound their aggregate cost together with the integer-frequency divisor couplings. A frequency classification alone does not establish a complete prime/Gamma/polar sign, nor does it yet pass the requested significance gate.

## Evidence and novelty status

Initial hybrid and divisor-energy deep searches completed with `partial=false`, no reported errors; compiler coverage is mixed and most indexed sources are not freshly compiled. Candidate/source-argument hits were inspected; no theorem was accepted from a search snippet. Further collar/resonance searches are pending. No external-priority claim and no accepted contribution yet.

## No-go closure

C1 is not retired yet. Its proposed positive survivor is C2, followed by a literal physical-correlation consequence. Paper and Lean status remain unproved until recorded audits pass.

## Log

- 2026-10-18 — Opened from the user attachment ending `4185f2f3-69a7-4408-a6e5-51260ec1f59e/pasted-text-1.txt`; persistent 100-contribution goal remains active.
