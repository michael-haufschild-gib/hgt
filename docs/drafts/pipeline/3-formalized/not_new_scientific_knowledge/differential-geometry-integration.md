# Differential geometry proof integration

- **Stage:** 3-formalized; selected integrations complete
- **Type:** integration audit and Lean theorem development
- **Source:** https://github.com/qinz1yang/differential-geometry/tree/main/DifferentialGeometry
- **Goal:** Investigate upstream proof mechanisms and integrate relevant unconditional results into HTGeometry, RHTower, and HilbertMetric, reusing existing definitions and proofs.

## Requirements

- No upstream dependency or bulk copying; document source mechanisms and local reuse.
- No extra axioms, proof debt, computational certificates, or heartbeat increases.
- Endpoints must discharge analytic premises for concrete existing objects; no assumption-only interfaces.
- Foreground, sequential targeted Lean checks; `lake --old env lean <module>` final audits; no full or umbrella builds.
- Wire new modules into area umbrellas; lint, check axioms from scratch files, remove task scratch artifacts.
- Preserve concurrent unrelated worktree changes.

## Plan

1. Inventory pinned upstream tree, inspect candidate proofs and dependencies, search local reuse.
2. Select and prove useful unconditional integrations across all three areas.
3. Audit changed leaves, theorem axioms, imports, lint, and provenance.

## Investigation

- Local toolchain: Lean/mathlib v4.32.2; upstream README advertises v4.33.1.
- Existing local Levi–Civita connection/fundamental theorem and Gaussian coherent Fisher infrastructure must be reused where applicable.
- No previous task-specific integration files or memory located at start.
- `update_plan` tool unavailable in this session; this card carries task tracking.
- Initial broad hybrid corpus query completed with partial coverage; refined Gaussian and Gram queries completed with `partial=false`. Source inspection and Lean checks determined applicability.

## Pinned inventory and first integration

- Upstream commit: `7a48598d35109aa99d1cc678e2724c213cdf4ff3` (17,555 Lean files; Apache-2.0). The temporary read-only checkout used for inspection is removed during cleanup; the pinned commit identifies reproducible source.
- All paths inventoried by topic. Large families include Ricci flow (4,341 files), PL topology (2,769), parabolic analysis (766), metrics (753), spectral theory (701), Sobolev analysis (577), comparison geometry (502), elliptic analysis (448), curvature (413), connections (352). Inventory is not a claim that every proof body has been audited.
- Inspected candidates: `Analysis/Parabolic/Harnack/PathIntegration.lean`, `LiYau.lean` endpoint, `LiYauHarnack.lean` endpoint/path proof; `Analysis/Parabolic/Euclidean/HeatKernel/PDE.lean`; `Analysis/Spectral/HamiltonGram.lean` and reaction construction; `Analysis/Convex/LogConvexSequence.lean`; Gaussian normalization and polarized Bochner interfaces.
- Generic manifold Li–Yau/Bochner results carry geometric and analytic premises. Do not import their interfaces as unconditional results. Existing local Levi–Civita and spectral heat infrastructure also makes wholesale translation redundant.
- Selected mechanism: Li–Yau path-action completion of the square, specialized and sharpened directly for existing Gaussian kernels. Independent local proofs; no copied declarations or upstream imports.
- New HilbertMetric leaf: exact Hilbert-space square remainder, sharp Gaussian comparison/equality, Gaussian distance-matrix entry and weighted-row bounds.
- New HTGeometry leaf: existing translated/reflected Gaussian tests, reflected equality rigidity, logarithmic transport cost.
- New RHTower leaf: reuse `heatGauss`, `summable_heatGauss`, `heatMultiplier_eq_ofReal`; strict comparison for the full Poisson lattice and normalized theta multiplier. No RH conclusion is asserted.
- Broad first search returned partial coverage (deadline/text prose); refined Gaussian/Hessian query returned `partial=false`, 61,006 inventoried files, with many compiler snapshots pending/stale. Source and scratch Lean verification remain authoritative.
- Serena symbol request failed because Lean paths are ignored by this project configuration; inspected-text edits used instead.
- These three modules subsequently passed final leaf and axiom audits and were wired into their umbrellas.

## Cayley integration

- Inspected upstream `Analysis/InnerProductSpace/Cayley.lean` (coercive `1±K`, exact inverse, bundled linear isometry).
- Local reuse audit found `HTGeometry/ConservativeDissipativeResolvent.lean` already stronger on existence/energy: constructed skew part, dissipative observation map, unconditional inverse, midpoint energy balance. Do not duplicate these constructions.
- New leaf `HTGeometry/ConservativeCayleyIsometry.lean` promotes the existing conservative `cayleyStep` to a surjective linear isometry, proves reversal by `-A`, and preserves arbitrary Gram pairings. No new skew-adjointness premise.
- Cayley and all three Harnack leaves passed targeted compilation and final audits without warnings.

## Dependency-closed mathematical proof of completed integrations

Write `a = exp(s)`, `d = exp(r)`, `b = a+d`. For Hilbert vectors `x,y,z`, polarization gives

`||x-z||²/(4a) - ||y-z||²/(4b) + ||x-y||²/(4d)
 = ||d(x-z)-a(y-x)||²/(4adb)`.

The denominator is positive, so exponentiation yields the Gaussian comparison. Equality is exactly `d(x-z)=a(y-x)`. Nonnegative weighted finite sums preserve the bound. For the reflected source pair `z,-z`, equality of the sum forces equality in both terms, hence `z=0` and `b*x=a*y`. Strict positivity permits taking logarithms.

For the existing Poisson bumps `heatGauss`, substitute physical times `πa,πd`. Existing `summable_heatGauss` justifies summing. Equality cannot hold at both lattice centres `0` and `2π`, because subtracting the characteristic relations would give `2πd=0`. At least one summand is strict, hence the full sum is strict. Existing `heatMultiplier_eq_ofReal` multiplies the lattice sum by the positive factor `a^(-1/2)`; the normalization ratio is `exp((log(b)-s)/2)`. This proves the strict theta heat-multiplier bound for all real `s,r,θ,φ`.

For the Cayley result, use the existing constructed generator `J=A-A†` and zero observation map. Let `D(A)=1-tJ`. Existing `implicitShift_isUnit` proves both `D(A)` and `D(-A)` invertible for every `t:NNReal`. The existing step is `C(A)=D(-A)D(A)^(-1)`. Associativity and two-sided inverse cancellation give `C(-A)C(A)=C(A)C(-A)=1`. Existing `cayleyStep_conservative_energy` gives norm preservation. Invertibility plus norm preservation yields a bundled linear isometry equivalence, whose inverse is `C(-A)` and which preserves all inner products.

## Verification checkpoint

- Four new leaf files, 22 theorems plus one definition; 364 lines total.
- All four passed final foreground `lake --old env lean <leaf>` checks, sequentially, exit 0, no warnings.
- All 23 new declarations audited via `#print axioms` in `/tmp/hgt_dg_axioms.lean`: only `propext`, `Classical.choice`, `Quot.sound`.
- Every new public theorem has only mathematical data/ambient structure parameters; no added propositional hypotheses, missing analytic interfaces, computational certificates, or heartbeat overrides.
- All four imported exactly once by the appropriate umbrella. No umbrella or full build run.
- Direct reused dependency objects are newer than their source files.
- `scripts/formal_tools.py index` succeeded and indexed all 23 declarations.
- `lint --check-generated` exited 1: 18 unrelated concurrently present modules were not reachable from their area umbrellas; generated `LEAN_API.md` and `LEAN_OVERVIEW.md` became stale after the index pass. None of the four integration leaves was reported. Preserve other authors' unverified drafts instead of wiring them merely to clear this gate.

## Second applicability pass

- Read upstream Gram square-root regularization and sectional orthonormalization proofs. The latter depends on a separate smooth-metric/curvature stack; local `LeviCivita/Fundamental`, `CoordinateCurvature`, and `ComplexMetricCurvatureSymmetry` already establish relevant connections and curvature laws. Avoid a parallel upstream geometry model.
- Read upstream constant metric scaling proof. Its metric-as-data representation differs from the local RiemannianBundle instance; direct translation would duplicate representations. No new unconditional concrete consumer identified.
- Reviewed spectral heat-power coefficient bound and operator endpoint: existing `DaiYoshikawa/PowerExpSup` and `SpectralHeatCauchySchwarz` already contain the maximizing scalar inequality and heat-kernel consumer. Reviewed discrete Sobolev log-convexity mechanism; generic derivative-sequence premises do not establish a new unconditional local endpoint, while `PositiveExpSumLogConvex` already supplies concrete exponential-sum convexity.
- Selected additional mechanism: quantitative two-channel Gram-area regularization, including singular Gram pairs. Reuse `projectiveQuantumTangentValue`, `projectiveGramTangentEnergy`, and Gaussian coherent-clock mass/overlap/tangent formulas. Prove positivity internally, with no spectral-gap or independence premise. Paper proof: adding delta to both diagonal Gram entries adds `delta * trace + delta^2` to the determinant; square-root subadditivity bounds the area error, and rationalizing gives an exact error identity. The coherent-clock determinant equals mass squared times Euclidean speed squared.
- Read tensor bilinear symmetrization, metric polarization, and block-kernel graph proofs. Their geometric bundle representations are distinct from the local instance-based bundle model; algebraic mechanisms already occur in `GramCompletionOfSquare`, mathlib polarization, and the more general local `SchurComplementKernel.kerSchurBlockOperatorEquivKerSchur`. No duplicate graph-of-kernel API added.
- Gram search: `partial=false`, 61,021 inventoried/indexed files; compiler snapshots largely pending/stale. Both candidate lemmas and source arguments inspected. Local `ProjectiveQuantumFisherValue` and `GaussianCoherentFisherClock` provided the actual reused objects.

## Selection coverage and exclusions

All 17,555 Lean paths were classified. Detailed proof review was directed by relevance to existing target objects, rather than importing every upstream theorem. This record does not certify every upstream proof body.

| Upstream area | Lean files | Integration disposition |
|---|---:|---|
| Geometry | 7,549 | Connection/curvature/metric candidates reviewed; reuse local Levi–Civita and coordinate geometry. Ricci-flow, surgery, comparison and compactness developments require a substantial independent manifold programme without an identified unconditional consumer in this task. |
| Analysis | 3,599 | Harnack square completion and Cayley transport integrated; Gram regularization integrated. Heat-power estimates, exponential-sum convexity and Gram mechanisms overlap existing code. Generic Sobolev/elliptic interfaces were not substituted for proved concrete endpoints. |
| Tensor | 131 | Symmetrization and kernel-graph candidates reviewed against existing Gram/Schur code; avoid duplicate representations. |
| Bundle | 86 | Infrastructure for upstream geometry representation; no separate framework added. |
| Topology | 5,773 | Mostly PL/manifold/three-manifold/homology infrastructure. No direct consumer identified for the selected Gaussian, theta, Fisher or conservative-operator objects. |
| External | 417 | Auxiliary topology and regularity developments; not used as new assumptions or dependencies. |

## Final integrated results

Five leaves add **29 public theorems, one isometry definition, and two private inequality helpers**. The public endpoints take only mathematical data and ambient structures; the private helper inequalities discharge their nonnegativity premises inside each public proof.

| Local leaf under `formal/GaloisForLFunctions/` | Result and local reuse |
|---|---|
| `HilbertMetric/GaussianHarnack.lean` | Hilbert-space square remainder, sharp equality, existing Gaussian matrix and weighted-row comparison. |
| `HTGeometry/RiemannGaussian/GaussianHarnack.lean` | Existing translated/reflected Gaussian comparison, source-collision equality rigidity, logarithmic cost. |
| `RHTower/HeatMultiplierHarnack.lean` | Existing Poisson lattice and theta multiplier; strict comparison from incompatible equality centres. |
| `HTGeometry/ConservativeCayleyIsometry.lean` | Existing conservative midpoint step promoted to a surjective isometry with exact reversal and Gram preservation. |
| `HilbertMetric/ProjectiveGramRegularization.lean` | Existing projective Gram/Fisher energy: quantitative regularization through rank loss, exact rationalized error, coherent-clock specialization and stationary sharpness. |

For the final Gram leaf, let `D` be the original nonnegative Gram determinant and `B = δ * trace + δ²`. The regularized area is `sqrt(D+B)`, so `0 ≤ sqrt(D+B)-sqrt(D) ≤ sqrt(B)` and the difference times the sum of areas is exactly `B`. Existing Cauchy–Schwarz proves intrinsic `D ≥ 0`. Existing coherent formulas give `D = mass² * sum(v_i²)` and positive mass, proving all analytic premises internally. At `v=0`, `D=0` and the bound is attained. This is a standard mechanism applied to existing corpus objects; no novelty claim is made.

- The fifth leaf passed final `lake --old env lean GaloisForLFunctions/HilbertMetric/ProjectiveGramRegularization.lean`, exit 0 without warnings. Its seven public theorems passed `#print axioms`; only `propext`, `Classical.choice`, `Quot.sound` occur, including transitive dependencies through both private helpers.
- All five imports occur exactly once in the correct area umbrellas. No full or umbrella builds run.
- Final indexing succeeded and includes all 30 public declarations. No `sorry`, `admit`, extra axioms, opaque/unsafe declarations, computational certificates, upstream imports, or heartbeat overrides were introduced.
- Final repository-wide `scripts/formal_tools.py lint --check-generated` exited 1. It reported **19 unrelated modules unreachable from their umbrellas**, plus stale generated `LEAN_API.md`/`LEAN_OVERVIEW.md` after concurrent edits. No integration leaf was reported, and no proof-debt error occurred. Index generation is refreshed after this check; a global green lint result is not claimed.
- Unrelated unreachable modules at that check: RHTower `CCMApertureChainProfile`, `CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`, `MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`, `MoebiusMollifiedZetaField`, `ThetaRelativeSourceRigidity`, `ZetaZeroDensityPowerSaving`; HTGeometry `AutonomousFirstOrderEntireClassification`, `AutonomousFirstOrderEntirePeriod`, `CasoratiWeierstrassAtInfinity`, `FirstOrderRepeatedRegularValue`, `GammaHorizontalRatio`, `SectorPhragmenLindelof`, `UnitriangularRepairGenealogyCofinal`, `UnitriangularRepairGenealogyFinite`. These are outside this integration's write scope and were not wired without their authors' completed audits.
- Cleanup removes task-owned scratch Lean files, search JSON, temporary logs, and upstream checkout. The five current compiled leaf artifacts remain available for downstream imports. No commit or push performed.
