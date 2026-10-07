# WP01 evidence — 2026-10-07

## Formal result

Module: `formal/GaloisForLFunctions/RHTower/WeilWorkPBAPNullRepair.lean`.
Namespace: `RHTower.WeilWorkPBAP`.

The formalized bridge constructs a nonnegative finite mixture realizing any finitely supported logarithmic vector. Its full energy is bounded in absolute value by the explicit weighted total defect. Adding the repair of the negative defect cancels every integer node exactly. All test-function smoothness and isolated-atom identities come from the existing exact pair-test construction. No PBAP assumption is used.

Capstones: `repair_nonneg`, `defect_repair`, `abs_energy_repair_le`, `defect_nullRepair`, `nullRepair_nonneg`, `abs_energy_nullRepair_sub_le`, `logValue_nullRepair`. `contDiff_signedPair` records smoothness of correction tests. Nonnegative coefficients and `n >= 2` in the relevant theorem signatures are domain conditions, not assumed positivity principles.

## Commands and outcomes

Commands involving Lean ran from `formal/`, in the foreground, with one active Lean process owned by this agent at a time.

| Command | Outcome |
|---|---|
| `lake env lean /tmp/wp01-names.lean` | Exit 0; initial mathlib names and pair-test interfaces verified. |
| `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPNullRepair` | Exit 0; final leaf build successful. Existing dependency diagnostics replayed. |
| `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPNullRepair.lean` | Exit 0; final source audit, no output. |
| `lake env lean /tmp/wp01-audit.lean` | Exit 0; remaining mathlib names and all eight capstone axiom checks pass. |
| `scripts/formal_tools.py index` | Exit 0; generated indexes refreshed. |
| `git diff --check -- <owned paths>` | Exit 0. |
| `scripts/formal_tools.py lint` | Exit 1; eight unrelated umbrella-reachability errors below. |

Intermediate diagnostics repaired: missing `Zeta23` namespace for `EF.weilTest`; missing `ContDiff` notation scope in the later smoothness theorem. No placeholder proof remains in the source. No umbrella/full build, heartbeat override, or numerical experiment was run.

All eight printed capstones depend only on `[propext, Classical.choice, Quot.sound]`; no added mathematical axiom or `sorryAx`. The scratch name check needed top-level examples to generalize universes and a `noncomputable section` for the linear-map definition; these were scratch-only diagnostics, fixed before the successful final exit. Final module Git blob hash: `00d96a1f5d99637bd6731d1c3b18ef249255a3b9`.

The lint errors concern these existing/concurrently edited modules, outside WP01's write scope:

- `RHTower.WeilWorkDeficitRecovery`
- `RHTower.WeilWorkHigherDenominatorCentralTest`
- `RHTower.WeilWorkSingularArithmeticSharpReciprocal`
- `HTGeometry.ApertureConeCalculus`
- `HTGeometry.ApertureConeWinding`
- `HTGeometry.ApertureLogTranslation`
- `HTGeometry.ApertureOpenHistoryIdeal`
- `HTGeometry.BoundaryCoronaCStarAlgebra`

The new PBAP leaf is imported by `RHTower.lean`. Only this import was added by WP01; unrelated umbrella edits were preserved.

## Search and novelty audit

- Exact full `PrimeBlindPositive` lexical search: seven declarations in two modules; no unconditional closing theorem found.
- Deep `prime blind signed mixtures archimedean pole positivity`: completed (`partial=false`), 68,275 indexed files at that snapshot. Candidate lemmas and source arguments inspected; compiler metadata mostly pending/source-only.
- Deep multiplicative-autocorrelation and polar/full searches completed; no applicable closure located. A proposed implication from already-assumed Weil positivity is circular for this task.
- Short-window archimedean search completed; its candidates did not prove the needed ground-energy bound.
- Co-Poisson and divisibility searches returned partial results. Available candidates and arguments inspected; their incomplete coverage is not evidence of absence.
- Corpus L248 already states scalarization by one-dimensional convolution factorization. L353 records the prime-torus viewpoint; L390 records the lost frequency resolution in the two-cluster estimate. None is a new result of WP01.

Primary external references inspected:

- [Connes–Consani, archimedean positivity](https://arxiv.org/abs/2006.13771).
- [Suzuki, current spectral framework](https://arxiv.org/html/2606.09096v3).
- [Zhu, quantitative small-support positivity](https://arxiv.org/html/2608.24827): full complex tests supported in an interval of length 1.6, with certified positive lower bound. This rules out novelty for the proposed small two-window sector; no computational part of that proof was reproduced here.
- [Laptev–Weth, logarithmic Laplacian](https://link.springer.com/article/10.1007/s13324-021-00527-y): parent theory for short-support spectral lower bounds.
- [Ehm–Gneiting–Richards, convolution roots](https://pure.psu.edu/en/publications/convolution-roots-of-radial-positive-definite-functions-with-comp/): author-institution account of classical one-dimensional factorization. The full AMS PDF was inaccessible; scalarization is not claimed formalized.
- [Cole–Gamelin, infinite polydisk representing measures](https://doi.org/10.1112/plms/s3-53.1.112): abstract accessible, full article inaccessible. Parent theory only.
- [Nilsson, boundary pluripolar sets](https://arxiv.org/html/2602.10853v1): representing/Jensen noncoincidence on smooth strictly pseudoconvex domains. It does not automatically apply to the prime polydisc.

## Remaining obligation

Full `RHTower.WeilOneSided.PrimeBlindPositive` is unproved. No unconditional application of `exists_weilPositiveFull_iff_primeBlindPositive` has been produced. The active goal remains open.

The larger weak-density construction in `TORUS-DENSITY.md` remains unformalized. Its finite Gram-packet subtheorem has now passed the checks recorded below; this does not certify measure-level convergence or the Jensen transfer.

## Finite Gram-packet continuation

New module: `formal/GaloisForLFunctions/RHTower/WeilWorkPBAPGramPackets.lean`.
Source Git blob hash: `0647ce6d3dfb8abb197616fe3f575c5999128ca5`.

- `exists_gramPacket_realization`: actual smooth compact tests for every PSD matrix, with the exact rational-log sample formula for every positive numerator and every denominator up to the selected resolution.
- `exists_nullPacket_realization`: finite divisibility-diagonal conditions imply all positive integer autocorrelation nulls.
- `exists_nullPacket_mixture`: actual nonnegative Finsupp weights satisfy the exact WP01 `logValue` constraints; the same family retains its total mass `packetMass * trace(A)` and rational samples.

PSD and finite divisibility conditions specify the input matrix class. There is no assumed Weil positivity, unexplained test-function existence, energy estimate, or PBAP premise. The zero matrix is allowed, while the mass identity records what happens for every nonzero trace. No scientific novelty claim is made for this bridge.

| Command | Outcome |
|---|---|
| `lake env lean /tmp/wp01-gram-names.lean` | Exit 0; Gram factorization and initial APIs verified. |
| `lake env lean /tmp/wp01-gram-bridge-names.lean` | Exit 0; Finsupp passage, symmetry, and trace simplification verified. |
| `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPGramPackets.lean` | Exit 0; final unchanged source, no diagnostics. |
| `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPGramPackets` | Exit 0; new leaf built, cached dependency diagnostics replayed. No umbrella build. |
| `scripts/formal_tools.py index` | Exit 0; indexes refreshed. |
| `git diff --check -- <owned paths>` | Exit 0. |
| `lake env lean /tmp/wp01-gram-audit.lean` | Exit 0; ten printed theorems depend only on `propext`, `Classical.choice`, `Quot.sound`. |
| `scripts/formal_tools.py lint` | Exit 1; nine unrelated umbrella-reachability errors listed below. |

Fixed intermediate diagnostics: function-valued finite sums needed an explicit extensional equality for compact support; the reciprocal identity needed `field_simp`; rational sample simplification needed the natural-number cast of one; autocorrelation symmetry required its explicit existing import. No heartbeat override or placeholder was used. Added only the new leaf's umbrella import, preserving concurrent edits.

Refreshed deep searches for finite torus realization, Gram-packet energy, and frequency tightness all returned partial coverage; candidate lemmas and source arguments inspected. The energy search indexed 68,329 files, with compiler metadata mostly pending/source-only; the tightness search reported a running background indexer. An ingredient suggestion citing this agent's unfinished source is not independent evidence. Located and source-checked the existing polar-packet coercivity result and the multidimensional Fejér fibre/multiplier formulas. Neither closes full nonpolar PBAP. The tightness search's spectral-measure existence theorem assumes full Weil positivity and is circular as an existence input here.

## Normalized representing-measure continuation

New leaf: `formal/GaloisForLFunctions/RHTower/WeilWorkPBAPMomentPackets.lean`.

- Reused `InfiniteTorusCharacter`, `SmoothNumbers.primeExponentVector`, and `ComplexIntegralGram.complexFeatureGram_posSemidef` after source inspection. Abandoned the custom circle-coordinate prototype. Revised `/tmp/wp01-torus-names.lean`: exit 0.
- Direct source compile with the normalized capstone: exit 0, no diagnostics.
- `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPMomentPackets`: exit 0. Requested leaf built; existing dependency diagnostics replayed. No umbrella build.
- `/tmp/wp01-moment-audit.lean`: exit 0. All ten audited declarations, including `exists_normalized_representing_mixture`, use only `propext`, `Classical.choice`, `Quot.sound`.
- Source SHA-1: `7f77ab2fbe9632cca6aae99daf0eec2ee4699172`. Umbrella import added beside the two earlier owned leaves.
- `scripts/formal_tools.py index`: exit 0; no tracked generated Markdown diff.
- `scripts/formal_tools.py lint`: exit 1, eight unrelated umbrella-reachability failures at this snapshot. None identifies an owned `WeilWorkPBAP` leaf:
  - `RHTower.WeilWorkDeficitFourierTransport`
  - `RHTower.WeilWorkHigherDenominatorPeriodDefect`
  - `RHTower.WeilWorkSettledPhaseTrace`
  - `HTGeometry.ApertureConeCalculus`
  - `HTGeometry.ApertureConeWinding`
  - `HTGeometry.ApertureLogTranslation`
  - `HTGeometry.ApertureOpenHistoryIdeal`
  - `HTGeometry.BoundaryCoronaCStarAlgebra`

Search evidence: the actual-moment-Gram deep search completed with `partial=false`, 68,336 files; candidate lemmas and source arguments inspected. The later box-overlap and Schur-energy deep searches were partial at 68,348 files, with reranking deadline and background-indexer freshness warnings. Their candidates and source arguments did not close either the box connection or the energy sign. Exact text search located the relevant reusable torus, bounded-smooth-counting, and Fejér APIs. The lexical spectral-probability search returned 1,620 hits with no partial/coverage fields and empty candidate/source-argument arrays. Source inspection found the applicable literal C² Fourier inversion in `WeilRegularDeviationRigidity`, as opposed to a spectral-producer existence theorem requiring the unproved positivity input.

External audit revisited [Cole–Gamelin's representing-measure paper](https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/plms/s3-53.1.112) and [Gaál–Révész's integral-comparison paper](https://link.springer.com/article/10.1007/s00209-022-03055-y). The latter assumes pointwise nonnegative positive-definite functions; arbitrary signed autocorrelations here do not satisfy that extra condition. Neither source supplies the missing Weil-energy inequality. No scientific novelty is claimed for the new Lean bridge.

Remaining: exact prime-exponent-box multiplier, actual spectral probability pushforward, weak convergence, and Jensen obstruction transfer. The full PBAP sign is still open. All five anti-theatre and four anti-laziness answers were posted in chat.

Final post-build `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPMomentPackets.lean`: exit 0, no diagnostics. Source hash unchanged. Owned diff check passed. All owned search, Lean, index, and lint commands exited. Removed the abandoned custom-coordinate scratch file; retained passing scratch/audit files and logs in `/tmp`. No computations, new assumptions, heartbeat changes, full/umbrella builds, commits, or pushes.

The latest lint errors are `RHTower.WeilWorkDeficitLeakageIntegral`, `RHTower.WeilWorkDeficitMassBounds`, `RHTower.WeilWorkDeficitPoissonLeakage`, `HTGeometry.ApertureConeCalculus`, `HTGeometry.ApertureConeWinding`, `HTGeometry.ApertureLogTranslation`, `HTGeometry.ApertureOpenHistoryIdeal`, `HTGeometry.BoundaryCoronaCStarAlgebra`, and `HTGeometry.HilbertSphereExtension`. Neither owned PBAP leaf is flagged. These results supersede the earlier eight-item baseline for the current snapshot; unrelated files were not changed.

All owned Lean/build/search/index/lint commands exited. No stale owned process remains. Generated API/index Markdown has no tracked diff. No commit or push was requested or performed.
