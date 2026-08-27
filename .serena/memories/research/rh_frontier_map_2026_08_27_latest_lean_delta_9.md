# RH frontier map update — Lean delta 9 (2026-08-27)

Target: `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`.

User constraints: Lean-only evidence via `scripts/formal_tools.py research`; no cards/papers/literature; no builds; no subagents; map is present-tense topology, not diary; <=4000 lines.

Current map after update: 835 lines, 23 live labels, 35 candidates. `git diff --check` clean. Live NB/BD removed.

Lean-derived changes folded:
- `BaezDuarteMobiusCriticalTailObstruction.lean`: canonical raw-Möbius full error and complementary-tail energy do not tend to zero. Critical harmonic energy, full error, and complementary tail each have cofinal positive floors. NB/BD canonical raw route moved to terminal; successor must change coefficients/carrier/normalization.
- `XiPhysicalPrimeAperturePNTDecay.lean`: every fixed-width complete FCRJ carrier tends to zero by corpus PNT.
- `XiPhysicalPrimeApertureThetaAbelModeRateWall.lean`: exact one-mode raw energy. After `exp(m)` renormalization it dies for Re z<-1/2, is positive constant at Re z=-1/2, and beats every real power above wall (away from z=-1). Remaining FCRJ core: actual source-to-mode decomposition/aggregate cross terms at sharp rate and coefficient-faithful checkpoint handoff; shrinking remains source-censoring.
- Sieve: terminal coefficients have depth-uniform divisor envelope; divisor-bounded Lemma 2.3(i) transfers paper saving. `MatomakiTeravainenLayerPaperScale.lean` accumulates terminal cutoffs and layers with loss `(t+1)^2(J+1)^2`. Remaining: construct `MTPaperScaleCertificate` for actual moving schedule and absorb moving counts. E still separately needs fixed physical relation/Hall/flux.
- `ThetaCuspLikelihoodEighthScoreRayTransform.lean`: exact ray-ray transform.
- `ThetaCuspLikelihoodEighthDominantPairCompensation.lean`: complete dominant two-particle eighth-score mass is strictly smaller than dominant one-particle mass. S6F/TCD remaining: non-dominant mixed sectors, summation, cofinal/all-order landing.
- `ThetaCuspHawkingParikhWilczekSignedMatrixThreeMomentClassification.lean`: finite signed matrix energy factors through three moments; explicit nonzero signed rank-one PSD dark matrix.
- `ThetaCuspHawkingParikhWilczekQuadraticHalfLineReceiverCone.lean`: exact four-chamber semialgebraic receiver cone on x>1; in cone energy zero iff wall and universal zero iff RH. Finite matrix algebra fully classified as receiver/counterfeit/dark; no producer.
- `ReflectedBiHeatPositiveMatrixApertureClassification.lean`: positive finite aperture matrices preserve strict side order; universal balance iff RH. RBH successor must be signed/indefinite, nonlinear, singular, or global.
- `FZZCigarPunctureTwoChannelBarePencilNoGo.lean`: fixed two-channel bare pencil at most one real energy.
- `FZZCigarPunctureFiniteDimensionalBarePencilNoGo.lean`: injective positive Hardy-zero packets of every finite size; no fixed finite-dimensional bare pencil Xi-complete. FZZ successor must be infinite-dimensional/energy-dependent/nonlinear/singular and literal-source-selected.
- New HTGeometry thermodynamic path/pair phase witnesses have no formal RH/Xi bridge, so no route topology change.

Latest freshness check showed no unaudited Lean module beyond above. Other agents own all non-map working-tree changes. Do not overwrite them.