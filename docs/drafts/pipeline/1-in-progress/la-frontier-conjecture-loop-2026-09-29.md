# Route LA frontier conjecture loop

- **ID:** LA-20260929
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP
- **Source:** docs/reports/rh-current-frontier-map.md, route LA; existing near-double-zero-exclusion-loop, first-laguerre-all-heights, laguerre-anchor-producer-ladder.
- **Objective:** Significant unconditional, noncomputational Lean knowledge advancing LA toward RH proof or falsification, absent from checked corpus and literature. Universal literature/training-data absence cannot be certified; do not claim it.

## Working plan

1. Read current corpus frontier and exact source declarations; search before each new topic.
2. Conjecture; prove or refute on paper; record mechanism and strongest positive survivor.
3. Audit mathematical equivalence against corpus and primary literature.
4. Formalize only dependency-closed results; use foreground sequential targeted Lean checks/builds with `--old`; wire umbrella without building it.
5. Audit axioms in /tmp, run formal lint, clean owned scratch sources and jobs, record remaining exact question.

Task-plan tool is not exposed in this session; this file is persistent task tracking.

## Constraints and initial state

- No added axioms, admissions, unproved arithmetic hypotheses, numerical experiments/certificates, heartbeat increases, commits, or pushes.
- All claimed source theorems require direct `lake env lean <module>` final verification. No full or umbrella build.
- Existing unrelated dirty files were present at session start; preserve them. Shared `RHTower.lean` requires narrowly scoped import insertion only.
- Search inventory reports complete source inventory but most declarations are source-only; semantic coverage unmeasured. Search results are candidates, not compilation evidence.
- Current LA: all slice signs at every height are RH-equivalent; orders above `(1/4+epsilon) log t` are already positive. The remaining low orders have no source producer. First Laguerre at all heights is open and weaker than real-rootedness.
- Existing N1–N50 loop rejects pointwise local estimates, analytic halves, scalar positivity, saddle/arc methods within the strip, and generic finite data. Do not promote those mechanisms as new.

## Conjectures and audits

### C1 — finite theta-shell first Laguerre asymptotic

Candidate: for canonical prefix cosine transform `F_N`,
`t^6 (F_N'(t)^2 - F_N(t) F_N''(t)) -> -2 P_N'(0)^2 < 0` for every nonempty fixed cutoff.

Paper mechanism: differentiate the exact boundary expansion analytically;
`t^2 F_N -> -A`, `t^3 F_N' -> 2A`, `t^4 F_N'' -> -6A`, hence `4A^2-6A^2`.
**Verdict: reject as significant new knowledge.** Existing corpus proves infinitely many nonreal zeros of every prefix; Haglund 0910.5228 §4 explicitly derives the algebraic boundary expansion for these incomplete-gamma sums. The first-Laguerre refinement is too directly downstream to establish requested scientific novelty. No Lean written.

Positive survivor: complete omitted tail carries opposite boundary slope, already formalized in `ThetaFiniteShellFourierBoundary`; no new salvage to formalize.

### C2 — nonlinear head/tail Laguerre cancellation

Candidate: head and complete remainder each have scaled Laguerre limit `-2A^2`, mixed Laguerre cross term has limit `4A^2`, full source is flat at every algebraic order. Would prohibit separate head/tail sign estimates.

**Verdict: rejected as significant new knowledge.** This is polarization of the published boundary expansion, not a new source sign. Full-source Ward annihilation and Wigner continuous-prime cancellation are also already in the corpus and leave the mixed sign open.

### C3 — quantitative approach to the quarter-log edge

Candidate: replace fixed epsilon in the existing `(1/4+epsilon) log t` positive-order threshold by an explicit sublinear excess. The Euler-disc constants grow as epsilon tends to zero; current central-arc proof also uses a fixed-width convexity constant. Simple diagonal extraction of an unspecified `o(log t)` excess is already implicit in the existing theorem and is not new knowledge. An explicit excess needs new uniform bounds; it still avoids the RH-bearing low orders. **Status: deferred for insufficient impact relative to the goal.**

### C4 — sharpen first-Laguerre companion detection

Corpus search found the exact pair/background inequality and separation companion law already formalized in `XiLaguerreSeparation`. Classical first-Laguerre-positive nonreal-zero examples and shifted-Laguerre criteria are published. **Verdict: no new theorem identified by this pass.** No generic receiver or renamed local sign is promoted.

### C5 — moving theta-shell cutoff and sharp boundary-layer sign

Let `m=N+1`, `F_N(t)=integral_0^infty P_N(x) cos(tx) dx`, and let `T_N` be the complete omitted tail. Candidate at `t=lambda m^2`:

`exp(pi m^2) / m^2 * T_N(lambda m^2) -> H(lambda)`,
`H(lambda)=8 pi^3/(4 pi^2+lambda^2)`.

The analogous first and second frequency jets should converge after factors `exp(pi m^2)` and `m^2 exp(pi m^2)`. For `lambda>4`, the full Xi jet is exponentially smaller than this tail, so the normalized prefix Laguerre expression should converge to

`H'(lambda)^2-H(lambda)H''(lambda)
 = 128 pi^6 (4 pi^2-lambda^2)/(4 pi^2+lambda^2)^4`.

Thus the predicted sharp sign boundary is `lambda=2pi`, with positivity for `4<lambda<2pi` and negativity for `lambda>2pi`. This would quantify the still-live joint cutoff/height boundary, not merely repeat the fixed-cutoff no-go.

Paper mechanism under audit: omitted first atom dominates the rest; under `x=y/m^2`, its normalized source tends to `4pi^2 exp(-2pi y)`. Polynomially weighted dominated convergence transfers three frequency jets. Completed-Xi strip bounds supply exponential suppression for `lambda>4`. **Status: paper proof written in `2-fully-proven/la-moving-theta-cutoff-laguerre-transition.md`; Lean transfer open.** No numerical experiment. Normalization was corrected after reading the actual `thetaCuspSeed` (the corpus source is twice the classical half-normalized kernel).

## Primary-source audit

- https://arxiv.org/pdf/0910.5228 — read §§1,4: literal finite theta-shell transforms, Pólya evenness obstruction, incomplete-gamma asymptotics. No first-Laguerre wording found, but absence of wording is not novelty.
- https://arxiv.org/abs/1502.06844 — Pólya-like approximations modify the kernel; not literal prefixes.

## Log

- 2026-09-29 — Init: Serena manual/memories, root/formal instructions, formal README/overview, route LA and relevant STATUS gates. Architecture/testing documents absent. Current corpus searches executed directly; goal active. C1 rejected; C2 under audit; next full-source coupling search running.
- 2026-09-29 — C2 rejected; C3 deferred; C4 corpus/paper audit found no advance. C5 moving-cutoff boundary-layer conjecture selected for proof audit. Deep companion search timed out during reranking but supplied exact existing declarations; no complete semantic coverage claimed.
- 2026-09-29 — C5 paper proof closed with corrected corpus normalization. New `ThetaMovingShellBoundaryLayer.lean` carries scale/phase/amplitude and dominated integral jets; source audit still in progress, no compiled theorem claimed. Serena `find_symbol` rejects Lean files as ignored; using exact source reads and patch edits. Builds remain foreground and sequential, default heartbeat limits, no umbrella builds.
- 2026-09-29 — Direct Lean and targeted `--old` leaf build passed for `ThetaMovingShellBoundaryLayer.lean` and `ThetaMovingShellFourierJet.lean`. Exact literal-shell normalization now verified for every fixed jet order. Complete-tail Gaussian/Tannery proof is in `ThetaMovingShellTailJet.lean`; first checks exposed algebra and simplification errors, repaired, final check pending. Xi Cauchy decay and finite-prefix frequency derivatives written but not yet verified. No prefix sign theorem claimed. All-order tail limit is the stronger positive survivor exposed by formalization; paper card now states and proves it, literature search found no matching result but cannot certify universal absence.
- 2026-09-29 — Complete-tail final direct check passed: `tendsto_normalized_thetaShellTailFrequencyJet` gives the exact rational joint limit for every fixed jet, retaining all omitted shells. Targeted leaf build running. Xi and finite-prefix bridges remain unverified; continue through the sign transition before judging whether C5 satisfies the significant-frontier goal.
