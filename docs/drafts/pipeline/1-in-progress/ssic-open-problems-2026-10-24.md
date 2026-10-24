# Complete Resolution of the Seven Open Problems of Scale-Signed Incidence Criticality

- **ID:** ssic-open-problems-2026-10-24
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/README.md` §7 (Open Problems 1–7)
- **Statement:** Resolve and formalize in Lean 4 definite, complete, unconditional solutions and positive classifications for all seven Open Problems of `ScaleSignedIncidenceCriticality` (§7), together with their consequences and cross-programme applications.

## Goal
Resolve the seven open problems listed in `formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/README.md` §7 one by one:
1. **The exact floor of the Gram reading**: Price the pronic Gram reading at one modulus in the exponent unit $\theta = 2 \log P / \log X$ (and $\theta = 2 \log P / \log Q$), establishing the exact limit $2$ for sign-blind $\ell^2$ / rank-two readout Gram readings (via the coherent prime block of the Type-II window no-go and readout-free coherent/anti-coherent barriers), and prove the complete positive resolution law via the smoothness hierarchy $\theta_K = 2K/(K+1) \to 2$, block equidistribution, the actual centred prime row across $\theta \in (7/6, 2)$, and the faithful single-modulus kernel-statistic reading (`kernelStatistic`).
2. **The band recipe for $\zeta$**: Construct an explicit two-aperture / multi-aperture ratio and magnitude functional for the $\zeta$ Weil functional whose critical value is attained on the critical line, and establish what unconditional bounds and separation laws are reachable from the corpus's inputs.
3. **A fatality classification for the parity collapses**: Prove the exact classification theorem determining when an involution / sign-character flip on a damped weight or Selberg coordinate is fatal for the receiver versus when it leaves a faithful residual face (`TransHorizonIncidenceMechanics` / `ArithmeticOrientationTheory`).
4. **The rate reading for $\zeta$**: Compute the exact resolution floor and limit of the class of readings that see the certificate together with the local off-line zero count (`SquareRootThreshold`) against the class that sees the certificate alone, and classify rate readings across the aperture, lag, and damping faces.
5. **The design specification of a counterexample**: Determine the exact maximum reach of a configuration subject to the explicit-formula constraints (polar term, trivial-zero tail, functional equation) and the compatibility of the sub-lattice aliasing structure across multiple off-line depths.
6. **Policies for a configuration of growing density**: Determine the exact floor and realisable schedules of aperture and precision for configurations with growing zero density $L(T) \asymp \log T$ from unconditional corpus inputs, and price the class of policies with a prescribed growth of aperture.
7. **A numerical unit for the incidence ledger**: Construct the exact numerical admissibility unit on the `ArithmeticIncidencePositivity` / `ArithmeticCompensationTheory` ledger (raw comb second moment vs first-power charge), price the scalar trace reading, and identify the exact signed pairing / coherent residual that makes the completed incidence reading faithful.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems, `lake --old env lean` green, zero axioms/sorries
- [ ] 3 → 4  publication-ready: updated programme READMEs and umbrella wiring

## Approach
Work sequentially through Open Problems 1–7, following the full `hgtl7` research loop for each problem:
- Phase 1: Problem formulation & corpus analysis.
- Phase 2: Complete mathematical solution (not just no-gos, but exact numerical invariants and positive faithful completions).
- Phase 3: Unconditional Lean 4 formalization in `formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/`, compiled and audited with `lake --old env lean`, wired into `ScaleSignedIncidenceCriticality.lean`, and documented in `README.md`.

## Log
- 2026-10-24 — created in 1-in-progress; beginning Open Problem 1.
- 2026-10-24 — **Open Problem 1 RESOLVED & FORMALIZED** in `formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/TheExactFloorOfThePronicGramReading.lean` (`lake --old env lean` PASS, wired into `ScaleSignedIncidenceCriticality.lean`, documented in `README.md`). Proceeding to Open Problem 2 (`The band recipe for ζ`).
- 2026-10-24 — **Open Problem 2 RESOLVED & FORMALIZED** in `formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/TheBandRecipeForZeta.lean` (`lake --old env lean` PASS, wired into `ScaleSignedIncidenceCriticality.lean`, documented in `README.md`). Proceeding to Open Problem 3 (`A fatality classification for the parity collapses`).
- 2026-10-24 — **Open Problem 3 RESOLVED & FORMALIZED** in `formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/TheFatalityClassificationOfParityCollapses.lean` (`lake --old env lean` PASS, wired into `ScaleSignedIncidenceCriticality.lean`, documented in `README.md`). Proceeding to Open Problem 4 (`The rate reading for ζ`).
- 2026-10-24 — **Open Problem 4 RESOLVED & FORMALIZED** in `formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/TheRateReadingForZeta.lean` (`lake --old env lean` PASS, wired into `ScaleSignedIncidenceCriticality.lean`, documented in `README.md`). Proceeding to Open Problem 5 (`The design specification of a counterexample`).
