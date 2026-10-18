# Bézout–Valuation Incidence Mechanics — current progress

Authoritative verified total: **5 / 250** significant connected contributions. Goal remains active. Previous goal turn is **progress**: contribution 005 completed, formally verified, registered, and cleaned up. Do not mark the 250-contribution goal complete at this milestone.

Objective file: `/Users/michael/.codex/attachments/7ebfb601-33c7-4a8f-af50-496fa3dde762/pasted-text-1.txt`. Read it before continuing the goal. User constraints: one significant connected contribution per goal turn; no hgtl7; no RH focus; no numerical computations or experiments; corpus search mandatory before new topics/new Lean; no external-paper search under the source policy; unconditional main statements for all natural levels and real weights; no commits/push. Field README is read-only. All relevant Lean belongs under formal/GaloisForLFunctions/BezoutValuationIncidence/. Maintain pipeline cards and the crisp own ledger.

## Completed contributions

1. SuccessorEnergyRigidityAndParityStability: exact variance/covariance decomposition, sharp bounds, kernel/parity rigidity and stability. 11 public theorems; one count.
2. ExactSuccessorMomentRegionAndUniversalInequalities: exact attainable moment cone and all universal centered linear inequalities. 8 public theorems; one count. Existing finite inverse is prior work.
3. SixModeStabilityAndSharpQuarterDecorrelation: stable six-mode extraction, exact defect kernel, sharp residual quarter bound and sharp constants. 19 public theorems; one count.
4. ExactFinitePrefixDiscrepancyDualityAndReturnTimes: exact finite-prefix Ramanujan coordinates; sharp L²≤V*A; canonical extremizer; exact universal constant and common-divisibility return-time classification. 12 public theorems; one count. See `mem:bezout-valuation-incidence/exact-prefix-duality-2026-10-18`.
5. SharpInitialPrefixObservabilityAndExactGramDeterminants: exact initial-prefix kernel, arbitrary-data reconstruction, sharp N−1 horizon, actual observation/Ramanujan/Gram matrix determinants, positive definite Gram geometry. 21 public theorems, 8 definitions, 11 private helpers; 40 declarations. See `mem:bezout-valuation-incidence/sharp-prefix-observability-2026-10-18`.

All five are at pipeline stage 3. The ledger is `logs/bvi-root-2026-10-18-knowledge.md`; it records exact files, proofs, limitations, and audits. Latest card: `docs/drafts/pipeline/3-formalized/bvi-sharp-initial-prefix-observability-2026-10-18.md`.

## Latest verification

Contribution 005 named original-source check passed without warnings. All 21 public theorem axiom closures are exactly propext, Classical.choice, Quot.sound. All 40 declaration names/kinds/lines/modules/paths matched the index; all 11 field modules are wired. Artifact hash/freshness checks passed. Guarded cleanup removed all 34 owned /tmp/bvi5-* paths; no owned process remains.

Global lint exited 1 only on five unrelated umbrella omissions: RHTower.SuzukiCriticalBetaKernel; BiScaleUncertainty.ClampedRampLatticeSum, FactorialMuntzBoundaryPole, FactorialMuntzBoundaryRepair, StationaryResolventMarkovPositivityAndNodalDefectProducer. No field or proof-debt findings. This is not a repository-wide passing gate; leave other agents' files/processes alone.

## Next frontier — uncounted

`docs/drafts/pipeline/0-backlog/bvi-integral-prefix-lattice-and-prime-rank-defect-2026-10-18.md`: prove actual integer Ramanujan prefix matrix integrally equivalent to diag(1,…,n), then audit exact cokernel and prime-rank consequences and the proposed canonical Smith chain. The card contains searches, explicit candidate factors, and existing generic dependencies. Complete paper, novelty, and toolchain audits before new Lean. None of these future statements is counted.

Do not count reused complete-period covariance, the M=1 Cauchy bound, finite Möbius inversion, endpoint correction, or generic Smith/cokernel theory. Exact determinants give rank and volume; they do not imply uniform conditioning, signed cancellation, or square-root bounds.

## Operational lessons

Use one owned foreground Lean process at a time. Do not start dev server, full builds, or umbrella builds. Use /tmp API/proof/axiom scratch checks; never add #print axioms to the tree. Final source check uses lake --old env lean -j 1. A concurrent external build can delete shared inherited .oleans. Appending LEAN_PATH fallback fails because Lean picks the first package root. When necessary, APFS-clone compiled imports, fill missing dependencies from actual build, use a temporary Lake root with package/vendor/source symlinks, and check the original source with --root=/Users/michael/Documents/code/hgt/formal. Verify/atomically install the new artifact, then remove only owned temporary paths after all owned processes terminate. The last snapshot included 9,355 inherited project modules; each import-heavy check took roughly 9–11 minutes under shared build pressure.

update_plan and multi_tool_use.parallel were unavailable. Durable plans live on cards; independent reads use Promise.allSettled. No subagents were spawned. Do not infer authorization to spawn them.
