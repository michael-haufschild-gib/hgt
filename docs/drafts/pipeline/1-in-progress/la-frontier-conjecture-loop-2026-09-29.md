# Route LA frontier conjecture loop

- **ID:** LA-20260929
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP
- **Source:** docs/reports/rh-current-frontier-map.md, route LA; existing near-double-zero-exclusion-loop, first-laguerre-all-heights, laguerre-anchor-producer-ladder.
- **Objective:** Continuous conjecture/proof/failure loop producing significant unconditional, noncomputational Lean knowledge advancing LA. User updated completion gate: an unconditional RH proof or falsification fully formalized in Lean. Intermediate contributions do not complete the goal. Universal literature/training-data absence cannot be certified; do not claim it.

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

Paper mechanism: omitted first atom dominates the rest; under `x=y/m^2`, its normalized source tends to `4pi^2 exp(-2pi y)`. Polynomially weighted dominated convergence transfers every fixed frequency jet. Completed-Xi strip bounds supply exponential suppression for `lambda>4`. **Status: formalized and audited in `3-formalized/la-moving-theta-cutoff-laguerre-transition.md`.** No numerical experiment. Normalization was corrected after reading the actual `thetaCuspSeed` (the corpus source is twice the classical half-normalized kernel).

### C6 — next-order critical ray and a possible half-unit shift

**Conjecture; unverified, not part of the compiled contribution.** The leading C5 limit vanishes at `lambda=2pi`. Expanding the exact Gamma amplitude and phase to first order in `1/a`, `a=(N+1)^2`, gives candidate correction

`B(lambda)=Re pi*((9pi/2)/c^2-3/c-2pi^2/c^3)`, `c=pi-i lambda/2`.

At `lambda=2pi`, algebra gives `B=-1`, `B'=-3/(8pi)`, `B''=9/(16pi^2)`. The resulting first-Laguerre correction is `1/(16pi)`, while the leading profile derivative is `-1/(8pi)`. Thus the candidate sharper law is

`a exp(2pi a) L_N(2pi a+s) -> (1-2s)/(16pi)`.

This predicts a transition at height `2pi (N+1)^2+1/2+o(1)`. It requires a dependency-closed first-order dominated-convergence proof and a fresh novelty audit. No numerical calculation was used; these expressions came from the literal coordinate expansion. Corpus lexical search `Laguerre moving cutoff boundary half offset` returned no indexed hits; that exact AND query has limited discovery power. Broaden before formalizing C6. Continue C5's unfinished bridges first.

## Primary-source audit

### C7 candidate — actual critical-root localization

Pending C6 proof, the next candidate is a unique real zero of the actual
first-Laguerre margin at `2pi(N+1)^2+1/2+o(1)`, rather than a sign-profile
boundary alone. C5's third-jet profile predicts
`a exp(2pi a) L_N'(2pi a+s) -> -1/(8pi)` uniformly for bounded `s`.
This is a conjecture, not a consequence already certified by fixed-ray limits.
A proof must retain uniformity on an actual interval: unit-circle Lipschitz
bounds give normalized coordinate-jet variation `<=B_(k+1)|delta lambda|`;
complete-tail Gaussian bounds and shifted Xi decay should retain uniformity.
C6 endpoint signs plus that uniform negative derivative would then give IVT
existence and uniqueness. Search/novelty audit before any C7 Lean code.
The full-source all-height low-order producer remains open throughout.

- https://arxiv.org/pdf/0910.5228 — read §§1,4: literal finite theta-shell transforms, Pólya evenness obstruction, incomplete-gamma asymptotics. No first-Laguerre wording found, but absence of wording is not novelty.
- https://arxiv.org/abs/1502.06844 — Pólya-like approximations modify the kernel; not literal prefixes.

## Log

- 2026-09-29 — Init: Serena manual/memories, root/formal instructions, formal README/overview, route LA and relevant STATUS gates. Architecture/testing documents absent. Current corpus searches executed directly; goal active. C1 rejected; C2 under audit; next full-source coupling search running.
- 2026-09-29 — C2 rejected; C3 deferred; C4 corpus/paper audit found no advance. C5 moving-cutoff boundary-layer conjecture selected for proof audit. Deep companion search timed out during reranking but supplied exact existing declarations; no complete semantic coverage claimed.
- 2026-09-29 — C5 paper proof closed with corrected corpus normalization. New `ThetaMovingShellBoundaryLayer.lean` carries scale/phase/amplitude and dominated integral jets; source audit still in progress, no compiled theorem claimed. Serena `find_symbol` rejects Lean files as ignored; using exact source reads and patch edits. Builds remain foreground and sequential, default heartbeat limits, no umbrella builds.
- 2026-09-29 — Direct Lean and targeted `--old` leaf build passed for `ThetaMovingShellBoundaryLayer.lean` and `ThetaMovingShellFourierJet.lean`. Exact literal-shell normalization now verified for every fixed jet order. Complete-tail Gaussian/Tannery proof is in `ThetaMovingShellTailJet.lean`; first checks exposed algebra and simplification errors, repaired, final check pending. Xi Cauchy decay and finite-prefix frequency derivatives written but not yet verified. No prefix sign theorem claimed. All-order tail limit is the stronger positive survivor exposed by formalization; paper card now states and proves it, literature search found no matching result but cannot certify universal absence.
- 2026-09-29 — Complete-tail final direct check passed: `tendsto_normalized_thetaShellTailFrequencyJet` gives the exact rational joint limit for every fixed jet, retaining all omitted shells. Targeted leaf build running. Xi and finite-prefix bridges remain unverified; continue through the sign transition before judging whether C5 satisfies the significant-frontier goal.
- 2026-09-29 — Complete-tail targeted `--old` leaf build passed; three finished modules wired into `RHTower.lean` without building the umbrella. `XiMovingShellJetDecay.lean` final direct check passed: fixed-radius Cauchy bounds retain the full exponential decay for every fixed jet; normalized Xi jets vanish for `lambda>4`. Prefix derivative/reassembly/sign checks remain. Completion gate updated by user to a fully unconditional formal RH proof/falsification; C5 and C6 remain intermediate research.
- 2026-09-29 — `ThetaFiniteShellFrequencyJet.lean` and cleaned `ThetaMovingShellLaguerreProfile.lean` passed final direct checks. Prefix moments are genuine iterated derivatives, with exact equality to the existing literal prefix cosine integral. Finite-frequency-jet targeted build completed; Xi jet targeted build running. Reassembly `ThetaMovingPrefixJet.lean` and sign capstone `ThetaMovingPrefixLaguerre.lean` remain unverified. Mathlib name scratch initially had three wrong namespace qualifiers, fixed; final scratch check still pending. Serena memory records the verified/open distinction.
- 2026-09-29 — Xi jet targeted build passed. Rational profile targeted build running. First reassembly check accepted all proofs except premature unfolding of the zero shell; fixed the simplification order, final check pending. C6 paper-proof draft with exact first-order correction, Gaussian tail domination, and critical algebra written in `la-critical-ray-half-shift.md`; C6 remains unverified. Six finished components wired without an umbrella build; two prefix capstone modules remain unwired.
- 2026-09-29 — Final direct `ThetaMovingPrefixJet.lean` audit passed. The normalized *actual prefix* real jets now converge to the negative rational tail jets for `lambda>4`; exact full-Xi/tail/prefix reassembly is verified. Final Laguerre capstones still unchecked. Rational-profile import was reduced to the exact mathlib algebra/trigonometry/tactic dependencies (no theta-source dependency); fresh direct audit is running because the import changed.
- 2026-09-29 — All eight C5 modules passed final direct `lake env lean <module>` checks. The capstone proves the exact normalized Laguerre limit, the unconditional combined sign classification on every fixed ray `4<lambda<2pi` and `lambda>2pi`, and bare 5/8 rays. First seven targeted `--old` leaf builds passed; final capstone leaf build running. Mathlib-name, all-declaration axiom, lint, and final umbrella wiring audits remain.
- 2026-09-29 — Fresh literature lead: Csordas, “The Laguerre inequalities and the zeros of the Riemann xi-function” (2011), DOI 10.1080/17476930903394820. Primary abstract concerns a finite Fourier cosine truncation with nonreal zeros; full text unavailable in this search, so exact overlap remains a coverage gap. Planat's posted 2026-08-25 preprint https://www.preprints.org/manuscript/202608.1692 proves phase-aligned growth-derivative block cancellation/no-go. Its definitions and Theorem 5 concern phase intervals, not the integer-shell moving cutoff in C5. No `cutoff`, `shell`, or `Laguerre` occurrence in accessible text; this does not certify universal priority. Generic nonlocal cancellation is already published and remains rejected as new knowledge.
- 2026-09-29 — Final capstone targeted `--old` leaf build passed (45 seconds); all eight imports now wired without an umbrella build. Core name scratch passed after marking its witness declarations noncomputable; this fixes scratch compilation of `Complex.conjCLE`, not a corpus theorem. Combined 72-qualified-name/67-declaration axiom audit running. Formal lint exited 1 solely on 12 unrelated unreachable modules: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMPrimePoleCurvatureAperturePlateau, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, WeilPolarConeExtremePoint, WeilPolarConeKernelTransformForm, ZetaZeroDensityPowerSaving. No C5 reachability/admission error remains.
- 2026-09-29 — C6 deep search returned partial results after a semantic deadline; every returned candidate/source argument/ingredient step inspected, none supplies the correction law. Lexical `Laguerre --module Theta` returned 16 matches across five modules (eight eligible declarations), including current C5 and existing polynomial/endpoint-atom receiver laws; no half-shift law. Existing spatial `ThetaTailScalingAsymptotics` and `ThetaTailGermExpansion` statements were read: fixed-kernel spatial limits and divisor-deformation germs, not growing-frequency cutoff corrections. C6 draft now includes an explicit fixed-order complex correction and polynomial first-order majorant. No computed samples or Lean C6 claim.
- 2026-09-29 — C5 closed: all eight clean final direct leaf audits and targeted `--old` builds; all eight umbrella imports; both Mathlib-name audits; all 67 public declaration axiom outputs inspected, each only propext/Classical.choice/Quot.sound. Card moved to `3-formalized`; LA and no-go-480 ledgers updated. Formal lint's 12 unrelated reachability failures remain explicitly recorded. RH unresolved, goal active. C6 toolchain-name scratch now running before first-order coordinate formalization.
- 2026-09-29 — C6 name scratch passed (including actual `abs_add_le` and Filter-qualified `eventually_gt_atTop`). `ThetaMovingShellFirstOrderCoordinate.lean` final direct audit passed, no errors or linter warnings; exact first-order phase/root/amplitude limits and global polynomial bounds, plus shifted critical phase, are verified. Targeted `--old` coordinate leaf build running. `ThetaMovingShellFirstOrderPhase.lean` written for exponential transfer and global unit-circle domination, not yet checked. No first-order integral/tail/prefix/Laguerre law claimed. Completed C5 scratch/log cleanup used non-forced explicit removal after `rm -f` was rejected; no owned C5 process remains.
- 2026-09-29 — C6 coordinate targeted `--old` leaf build passed. Phase module now includes both the relative exponential and the actual critical Fourier exponential, with explicit first-order norm bounds. Its direct check is running. Remaining: jet-power transfer, integral DCT and exact Gamma coefficients, all later shells at the additional `a` scale, shifted Xi decay, actual prefix reassembly and critical Laguerre capstone. C6 still open.
- 2026-09-29 — Coordinate module wired. Phase check first stopped on an incorrect RealDeriv import path; actual file inventory and verified finite-frequency module show `Mathlib.Analysis.Complex.RealDeriv`. Corrected and checking again. No object-file absence is treated as a mathematical failure.
