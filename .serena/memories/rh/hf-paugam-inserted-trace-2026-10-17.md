# HF: fixed bounded insertion recovers the full source Paugam trace

## Goal status
The all-21-live-routes/all-23-candidates RH objective remains active. XN was attempted in the previous turn; HF selected this turn. Neither is credited with the user's requested significant obstruction-removing RH advance. Next turn must select another route/candidate per user instruction. The result below is a verified structural bridge, not positivity, native-BV Gaussian removal, or geometric cup identification. Do not mark the goal complete or blocked because the remaining mathematics is hard.

Card: `docs/drafts/pipeline/1-in-progress/hf-native-gaussian-removal-2026-10-17.md` (title now HF: source cup trace and native Gaussian removal). Only local Lean corpus used as mathematical evidence. No old research Markdown, web, external novelty audit, numerical experiment, added axioms, heartbeat increases, full builds, commits, or pushes. Frontier map stayed read-only with SHA-256 `6e287eaa43d5ee46e7e0ce07051102706936fbd38604e06d7423c895b717da1c`.

## Actual new module and paper result
`formal/GaloisForLFunctions/RHTower/DeningerMeyerPaugamInsertedTrace.lean`, wired into `RHTower.lean` after DeningerMeyerConvolutionPaugam. Namespace RHTower.
- `deningerHasseTopInsertion`: on each upper-half-plane Xi Hasse block, sends top coordinate to bottom coordinate and kills other inputs. One fixed bounded contraction handles every multiplicity.
- `deningerMeyerHilbertConvolution_topInsertion_trace`: Tr(T_g E) = sum over upper zeros rho of Mellin Hasse coefficient a_{m(rho)-1}(g,rho).
- `deningerMeyerSourceCup g h`: literal alternating source convolution g*J(h)-h*J(g). The name does not assert a geometric cup identification.
- `deningerMeyerSourceCup_class`: agrees with existing deningerMeyerConvolutionSkewProduct on the genuine Poisson quotient.
- `deningerMeyerSourceCup_inserted_trace`: Tr(T_{cup(g,h)} E) equals the complete global Hasse Paugam pairing of [g],[h], retaining all complementary jets.
- `deningerMeyerSourceCup_ordinary_trace`: Tr(T_{cup(g,h)})=0 for all original sources.
- `deningerMeyerSourceCup_trace_detects`: inserted trace against every original h vanishes iff [g]=0.

Proof: E is coordinate reversal followed by projection, hence norm <=1. Full-Jordan convolution is lower triangular Toeplitz. Its composition with E has only one nonzero diagonal entry per upper block, exactly the top Hasse coefficient. Existing all-source trace-class admission pays the absolutely convergent diagonal sum. Existing Paugam complementary-jet/convolution identity identifies it with the global form. Ordinary trace vanishes by functional-equation reflection of the antisymmetric Mellin product. Zero radical gives faithful detection. Full dependency-closed proof is in the card.

## Rejected shortcuts and next conjecture
Gaussian removal in original all-weight source topology and finite native density are already proved in DeningerMeyerGaussianSourceApproximation and DeningerMeyerFiniteNativeDensity. They do not imply native BV/full arithmetic graph convergence; no continuity theorem for the unsmoothed map was found or proved.
Convolution adjunction for Paugam already exists in DeningerMeyerConvolutionPaugam. It does not identify arithmetic sharp with the positive Hilbert adjoint.
Next exact conjecture: does E preserve `LinearMap.range deningerMeyerHasseHilbertLM`? True on finite packets by finite synthesis; boundedness and density do not establish full-image preservation. No theorem assumes it. Geometric cup compatibility and actual source sign remain separate. Do not replace them by arbitrary square-zero algebra constructions or another RH receiver.

## Validation
Final foreground command from formal passed exit0:
`lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/DeningerMeyerPaugamInsertedTrace.olean GaloisForLFunctions/RHTower/DeningerMeyerPaugamInsertedTrace.lean`.
Separate `/tmp` import/#print axioms for all eight public theorems passed exit0, each only `[propext, Classical.choice, Quot.sound]`. No sorry/admit/axiom/opaque/unsafe/native_decide/set_option. index passed and registered declarations. Scoped git diff --check passed.
Global `scripts/formal_tools.py lint --check-generated` failed exit1 only on twelve concurrent unwired modules: CHMDBVUniformConvergence, CHMDBVUniformGraph, CHMDBoundedContinuousSource, CHMDCompactBVTranslations, MobiusDivisorClockGraphSource, MobiusDivisorCriticalBVProfile, ThetaCuspRatioBoundaryNormOrientation, BoundedVariationNormAlgebra, BoundedVariationPrimitive, BoundedVariationUniformJump, ClosedConeBochnerIntegral, ContinuousKernelBochnerControl. No generated-file staleness error this time. Do not change other sessions' unfinished files or claim global lint passed.
All own Lean/search/index/lint handles are terminal. Owned `/tmp/hgt_hf_*` scratch/log/search files are being removed after recording audit. Preserve the canonical new .olean and all unrelated concurrent worktree changes.

Search notes: three deep queries completed (partial false), semantic coverage not measured, compiler metadata mostly source-only/pending/stale. Broad smoothing query irrelevant suggestions rejected. Targeted lexical search plus exhaustive rg did not find an existing Paugam opTrace insertion theorem. No external novelty claim.