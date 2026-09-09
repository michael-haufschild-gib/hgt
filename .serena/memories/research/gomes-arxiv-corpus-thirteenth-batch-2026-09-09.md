# Gomes arXiv corpus experiments: batch 13, verified checkpoint

Overall user goal remains ACTIVE and unbounded. This checkpoint is progress, not completion. Cumulative verified result: 722 theorems across 84 modules (previous 651/76; this batch 71/8). No commits or full/umbrella builds.

## Verified modules
All under formal/GaloisForLFunctions/HTGeometry/, namespace GaloisForLFunctions.HTGeometry:
- GomesFockSpectralMeasure: 5 theorems, 1 def, 1 named finite-measure instance. Data-only completed Fock measure; exact moments, compact support, total mass, equality iff all moments (even across dimensions/generator counts), zero iff vector zero.
- GomesFockSpectralGauge: 5 theorems. Scalar measure homogeneity; equal scalar measures iff equal squared moduli or zero state; scalar stabilizers; universal simultaneous generator/vector spectral gauge iff Uᴴ*U=1.
- GomesFockSpectralWindowMatrix: 12 theorems, 2 defs. Arbitrary set window mass (μ S).toReal and its polarized matrix. Homogeneity, parallelogram, bound, exact quadratic observation, Hermitian PSD contraction, univ identity, empty zero, singleton existing atom matrix.
- GomesFockSpectralWindowGauge: 2 theorems. Full scalar-window gauge and matrix-window conjugation each iff unitarity.
- GomesFockSpectralWindowSupport: 7 theorems. Zero mass iff measure-zero iff W*x=0; W=0 iff all states/basis states have zero mass; exact trace formula; trace=0 iff W=0.
- GomesFockSpectralCoherentWindow: 5 theorems, 2 defs. Three intensities at c, c+1, c+I recover c iff window mass nonzero. Every two-reference menu has reflection ambiguity. Exact kernel reconstruction and injectivity criteria. This improves prior four-reference menus and proves sharp positive survivor.
- GomesFockAnalyticGauge: 11 theorems, 5 defs. gomesFockSpectralObservable (real integral), gomesFockFourier, gomesFockMGF, gomesFockStieltjes, gomesFockAnalyticMenu. Full real observable equality iff measure equality; scalar modulus classification; universal real-observable gauge iff unitarity. Fourier0 and MGF0 recover source mass. Fourier alone, MGF alone, and joint Fourier/MGF/Stieltjes menu each have exact unitary gauge. Joint analytic menu on scalar orbits retains only modulus (or zero state). Stieltjes ALONE reconstruction is not proved here.
- GomesFockQubitSpectralGauge: 24 theorems. All four existing QuantumAlg gates phaseGateOp, phaseGateOnZeroOp, rotZOp, rotYOp, applied to measure, window matrix, original atom matrix, Fourier, MGF, Stieltjes. No supplied unitarity/generator hypotheses.

## Verification
/tmp/hgt-gomes/thirteenth contains all source scratch files, clean scratch logs, successful exact-module build logs, modules.json, counts.json, totals.json, build-status.json with source hashes, corpus-search-audit.json, AxiomAudit.lean and axioms.log, axiom-audit.json, process-audit.json, progress.json.
All 82 declarations (71 theorems, 10 definitions, 1 named instance) audited using #print axioms in scratch. Only propext, Classical.choice, Quot.sound. No added axioms/proof debt/numerical tactics in new sources. Named instance gomesFockSpectralMeasure_isFinite INCLUDED in audit. Eight modules wired into HTGeometry.lean. All source copies equal tested scratch copies; 25 prior source hashes checked unchanged. Corpus search confirms all 82 declarations indexed, zero markers. No remaining own Lean/Lake process.
GLOBAL LINT FAILED only on four unrelated RHTower modules missing umbrella imports: SelbergMaassFullGradient, SelbergMaassStripGap, SelbergMaassStripSlice, SelbergModularStripComparison. Recorded exact errors in lint-status.json; no lint errors in these eight modules. Do not wire other tasks' unfinished modules merely to clear lint. Prior batch12 global lint passed. This batch's targeted builds all pass.

## Discipline / API lessons
One foreground Lean command at a time: LEAN_NUM_THREADS=1 lake env lean /tmp/file.lean; only exact-module lake build for final/dependency audit. Wait for exit_code before dependent Lean. Targeted analytic build refreshed genuinely needed dependencies (including FreeFockMatrixFullAnalyticLaw and FreeFockMatrixFullFourierDecay); all succeeded. No full umbrella builds.
Put `open scoped Matrix` BEFORE entering namespace GaloisForLFunctions.HTGeometry: nested Matrix namespace otherwise shadows root scoped notation. This caused parser errors on *ᵥ and ᴴ until fixed. Explicit Matrix.mulVec also avoids parser ambiguity.
For analytic joint tuple transport, after unfolding and changing LHS back to wrapped measures, `simp only [h]` leaves definitional wrapper equality; finish with `rfl`.
ENNReal.toReal_eq_zero_iff takes explicit argument; measure_mono_null has two universes. Matrix.PosSemidef.dotProduct_mulVec_zero_iff lives in Mathlib.Analysis.Matrix.Order. Basis simplification: Matrix.mulVec_single_one, Pi.star_single; do not unfold dotProduct/mulVec too early.
Audit parser must strip nested comments and strings, and include named instances. Reusable prepare_audit.py/check_axioms.py/finalize_batch.py saved.

## Next candidates: researched, NOT proved
1. Full spectral-window countable additivity / operator-valued measure infrastructure. Current window tensors are PSD contractions with exact quadratic reconstruction, but NO countably additive POVM structure yet. Do not claim one.
2. Stieltjes-only compact measure reconstruction. Corpus search found StieltjesMomentDetermination.hausdorffSource_eq_of_stieltjes_eq. Read source lines1–146 of its182 lines: it concerns compactified real kernel y/(1+t*y) on HausdorffSourceSpace=[0,1], assumes equal zeroth mass separately, and equality near zero. It is not directly the complex Cauchy transform; adaptation needs compactification or mass-at-infinity reconstruction.
3. Exact invisible zero-atom classification for that compactified kernel: kernel vanishes at y=0, explaining separate mass hypothesis. Conjectural positive survivor: observational equivalence modulo the zero atom for a concrete finite-source interface. Search corpus before coding.

Paper status: applications of reconstruction/internal-frame viewpoints, not claimed numbered theorem transcriptions. 2509.25276 latest v7 retracts earlier equivalence: never revive it. User bans cards/docs reads; work directly in Lean and corpus research tool. No subagents or unrelated edits.