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

## Actual spectral probability continuation

New leaf: `formal/GaloisForLFunctions/RHTower/WeilWorkPBAPSpectralMeasure.lean`.
Git blob hash: `64190369ffaf22352f991b3dccb17fa381a2d176`.

- `/tmp/wp01-spectral-names.lean`: exit 0; signed Fourier rescaling, phase detuning, continuity and measure APIs verified against this toolchain.
- `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPSpectralMeasure`: exit 0. Requested leaf built, cached dependency diagnostics replayed. No full or umbrella build.
- `/tmp/wp01-spectral-audit.lean`: exit 0. Nine printed declarations, including `spectralRepresentingMeasure` and `exists_spectral_representing_mixture`, depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPSpectralMeasure.lean`: exit 0, no diagnostics. Umbrella import added.
- `scripts/formal_tools.py index`: exit 0, zero generated Markdown changes reported.
- `scripts/formal_tools.py lint`: exit 1, nine unrelated reachability errors: `WeilWorkDeficitSquareWindow`, `WeilWorkQuantizationRadialContour`, `WeilWorkQuantizationRadialGrowth`, `WeilWorkSettledPhaseMellinTrace`, `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. No owned PBAP leaf is flagged. This is the latest lint snapshot; do not treat earlier lists as current.

The literal density, its normalization, and its pushforward are now conclusions. `phaseMoment_spectralTorusProbability` identifies rational moments with actual autocorrelation samples. The capstone composes this with smooth packet realization without assuming full Weil positivity. The input `ComplexNullMixture` has complex integer cancellation, stronger than WP01's real symmetric condition; the broader equivalence still requires symmetrization.

The spectral-measure and divisor-overlap deep searches completed with `partial=false`, respectively 68,352 and 68,364 files. Candidates and source arguments were inspected. The divisor hits do not supply the required multiplicative box count. The refreshed full-sign search returned `partial=true` at 68,366 files, and the narrow-packet and Montgomery–Vaughan searches were partial at 68,367 files. Compiler metadata was mostly pending/source-only. Source inspection, not retrieval rank, established applicability of `dirichlet_meanValue_sharp` and `log_sub_seven_le_re_digamma_quarter`.

`PACKET-ENERGY.md` now records a dependency-closed paper bound for arbitrary complex coefficients in the literal narrow integer packet family: for `N >= 1`, `L >= 105`, normalized full energy is at least `(1/2) log(1+N*L/4)-10-(2/L) sqrt(1+log N)`. The exact constant uses the corpus's mean-value error `104`, not the sharper literature constant. Its Lean proof remains outstanding. This is a bridge to the classical mean-value mechanism, not a claimed novel solution. The primary external audit used [Montgomery's survey, sections 5–6](https://www.nato-us.org/analysis2000/papers/montgomery.pdf); this also prevents presenting the spreading mechanism itself as new.

No computation, new axiom, heartbeat increase, full build, commit, or push was performed. Full PBAP, box-multiplier convergence, and the Jensen transfer remain open. The positive survivor is not retired as a completed no-go.

Final `/tmp/wp01-energy-names.lean`: exit 0, no diagnostics. It verifies the next target's corpus interfaces and proves two scratch sublemmas: `gammaBracket(t) >= log(1+|t|/4)-10`, and the two-sided mean-square upper bound `(2*T+208*N)*sum |c|^2`. Fixed the unnecessary Herglotz-import dependency by unfolding the literal gamma definition, and fixed measure inference/function-power normalization in the adjacent-integral identity. The full packet lower bound is still not formalized. All owned Lean, search, index, and lint processes have exited; spectral-leaf hash remains unchanged. No generated-index diff remains.

## Full narrow-packet energy continuation

New leaves and verified Git blob hashes:

- `WeilWorkPBAPPacketFourier.lean`: `f9729fc75387de461016b8844e655beea0de413e`, 228 lines.
- `WeilWorkPBAPPacketEnergy.lean`: `344ffe13b9c97068b3a3aa96adf0608c5f3ca03e`, 386 lines.

Each targeted `lake build --old +GaloisForLFunctions.RHTower.<leaf>` exited 0. Both final commands `lake env lean GaloisForLFunctions/RHTower/<leaf>.lean` exited 0 with empty logs (`/tmp/wp01-packet-fourier-final.log`, `/tmp/wp01-packet-energy-final.log`). The twenty-declaration `/tmp/wp01-packet-audit.lean` exited 0; every printed axiom list is exactly `[propext, Classical.choice, Quot.sound]`. Both leaves are imported by `RHTower.lean`. No umbrella or full build ran.

The Fourier leaf proves literal mass, complex Fourier factorization, the bump envelope, symmetric mean-square bound, and actual low-frequency mass. The energy leaf proves gamma coercivity, exact cancellation of centering in the two pole weights, their harmonic-product bound, and the full signed lower bound. Its uniform escape capstone quantifies over every coefficient function and every `L>=104`, without assuming null constraints or an energy sign. The simpler logarithmic bound applies for `N>=1`. No general PBAP theorem or fixed-`N`/growing-`L` Lean limit theorem is claimed.

`scripts/formal_tools.py index`: exit 0, seven changed source-index entries, zero removed. Generated API/index Markdown has no tracked diff. `scripts/formal_tools.py lint`: exit 1 on ten unrelated reachability errors; no owned PBAP leaf is flagged:

- `RHTower.WeilWorkDeficitZeroTransport`
- `RHTower.WeilWorkHigherDenominatorAxisPolynomial`
- `RHTower.WeilWorkHigherDenominatorLogMoments`
- `RHTower.WeilWorkSettledPhaseAbelRigidity`
- `RHTower.WeilWorkSingularArithmeticReciprocalMeanSquare`
- `HTGeometry.ApertureConeCalculus`
- `HTGeometry.ApertureConeWinding`
- `HTGeometry.ApertureLogTranslation`
- `HTGeometry.ApertureOpenHistoryIdeal`
- `HTGeometry.BoundaryCoronaCStarAlgebra`

This supersedes earlier lint snapshots. Unrelated files were not edited.

The packet-energy deep search completed with `partial=false`, 68,370 files; candidate and source-argument fields inspected. The subsequent overlapping-support search was partial at 68,389 files and did not supply the signed extension. Source inspection and fresh scratch checks established the applicable Cauchy–Schwarz, Fourier, mean-value and gamma interfaces. [Montgomery–Vaughan's original Hilbert-inequality paper, Corollaries 2–3](https://personal.science.psu.edu/rcv4/personal/Publications/s2-8-1-73.pdf), independently confirms the classical parent mechanism. Scientific novelty remains unestablished; the WP01 subclass advance is not a full solution.

All five anti-theatre and four anti-laziness questions were answered in chat. No computation, added axiom, heartbeat increase, commit, or push. Intermediate failed scratch scripts were removed after the completed source and final audit were preserved. All owned processes exited. Next work returns to the signed comparison for overlapping tests; torus density/Jensen is not retired.

## Critical coefficient boundary — final verification, 2026-10-07

All ten `WeilWorkPBAPCritical*` leaves passed targeted `lake build --old +<module>` builds. The final leaf's mass-zero proof initially timed out; explicit intermediate types fixed it without changing heartbeat limits. All ten final direct-source audits and the 22-declaration axiom audit completed sequentially with exit 0. Ten umbrella imports added; no umbrella or full build.

`scripts/formal_tools.py index` exited 0 and regenerated the API/gaps/overview indexes; new critical declarations are present in `formal/LEAN_API.md`. Generated index files produce no tracked Git diff. `scripts/formal_tools.py lint` exited 1: nine unrelated umbrella-reachability errors, for `WeilPaperCauchyDeficitProfile`, `WeilWorkHigherDenominatorWeightedIntegral`, `WeilWorkSingularArithmeticPolePerron`, `WeilWorkSingularArithmeticSummatory`, `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, and `BoundaryCoronaCStarAlgebra`. No critical-leaf reachability or proof-debt error. File-size warnings also remain. This is a timestamped shared-tree snapshot, not a clean global lint claim.

Recent searches: finite-part deep search `partial=true`, 68,456 inventoried files; signed sampling deep search `partial=true`, 68,460 files and interrupted retrieval/malformed reranker output; module-filtered full-null deep search `partial=true`, 68,462 files. All three report background refresh incomplete; compiler metadata is mostly pending/stale/source-only. Candidate lemmas, source arguments and ingredient proposals inspected. The final search's proposal to derive positivity from positive mass and an existence equivalence is not a proof: its nonnegativity obligation is precisely unpaid PBAP. No search hit is treated as a kernel audit.

### Final source and axiom checks

For each of Resonator, Datum, Coefficients, Kernel, Window, Laplace, Residue, Abel, DensityLaplace and Boundary, ran `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPCritical<suffix>.lean` from `formal/`, one foreground Lean process at a time. All ten exited 0 with empty diagnostic logs. `lake env lean /tmp/wp01-critical-axioms.lean` exited 0; every one of its 22 declarations reports exactly `propext`, `Classical.choice`, and `Quot.sound`. This includes the negative-mixture, fixed half-gamma, and normalized-unboundedness capstones. No `sorryAx` or new axiom occurs.

Verified hashes remained unchanged through the final audit:

| Leaf | SHA-256 |
|---|---|
| `WeilWorkPBAPCriticalResonator.lean` | `20cbe33addb7cf30adda2b2fb82df97c74784099cb65776993e29d86fa9ee62a` |
| `WeilWorkPBAPCriticalDatum.lean` | `55f29fc853e3f57e00468f49ccaa75348193044d26b2d329813c1562cfcc6f41` |
| `WeilWorkPBAPCriticalCoefficients.lean` | `99317dca2ca8e6b06797af631ca184596b516aaf18b0ca2ac734c5c07ecc9e42` |
| `WeilWorkPBAPCriticalKernel.lean` | `dbedcec20d21a0e3ef00ee19650dde154778c1914f6131fc044e71253f4c634e` |
| `WeilWorkPBAPCriticalWindow.lean` | `738b4b4c04d0ba7b623ebd4c290a01b211793477b42e0e1f316c8cf9e89056fa` |
| `WeilWorkPBAPCriticalLaplace.lean` | `8779c517f35ca668b3ac6482b733418e56e5c88f6b0a11cbecd0594c973af62b` |
| `WeilWorkPBAPCriticalResidue.lean` | `4675dfc880c9b6fe0f9e54a976b46159a75f1c41477ef0fb3f430b6386464449` |
| `WeilWorkPBAPCriticalAbel.lean` | `88b32eefe60b60aa735be5088f352b6a9e3a34fe8331b8841cc99153485bfcdd` |
| `WeilWorkPBAPCriticalDensityLaplace.lean` | `817ad8c1f8cb10fb3e624c3be8b26835dae5d215f04ac19708bebfb98527716a` |
| `WeilWorkPBAPCriticalBoundary.lean` | `6c36ee5e544c6332e522988c6e57b7629a1fa55f3646b83ce53540b8ebbe5832` |

The axiom audit covers exact resonator mass/gamma/sample identities; generic completion; modified Toeplitz and primitive-square bounds; absolute summability; harmonic ceiling; translated positive-definite kernel and remainder; window identity; signed Laplace identity and residue; signed cumulative Fubini and ceiling; arithmetic cumulative/product transform; coefficient boundary; both negative-witness forms and mass-normalized unboundedness. The scratch audit changes no production source.

A later two-cluster search completed `partial=false`, 68,464 inventoried files; refresh remained incomplete and compiler coverage mostly source-only/pending. The retrieved ground-shift Cauchy-Schwarz retains the unknown aperture ground correction. It cannot discharge the proposed unshifted signed cross bound.

External next-route correction: [Beckner, Section 2/Theorem 4](https://arxiv.org/html/math/0701939v6) states nonattainment for logarithmic uncertainty and supplies an exact deficit identity. L371's Gaussian-extremal heuristic is therefore not used. This does not affect the critical-coefficient proof.


## Joint phase threshold and logarithmic cost

`WeilWorkPBAPJointConvex`, `JointPhase`, and `JointEscape` each passed targeted `lake build --old +<leaf>` and final direct `lake env lean GaloisForLFunctions/RHTower/<leaf>.lean`. The three final source logs are empty. The 17-declaration `/tmp/wp01-joint-axioms.lean` audit exits 0 and reports only `propext`, `Classical.choice`, and `Quot.sound`. The audit includes strict-positive finite correction with cardinality bound, the arbitrary distinct-node antiphase obstruction, mass classification, pair defect, pointwise log-cost minorant and both escape capstones. Imports are wired. No full or umbrella build.

`JointProfiles` scratch source and targeted build pass; final direct audit and the downstream actual null/mass interface remain in progress at this checkpoint. The full-energy coercivity estimate in `JOINT-PHASE-COST.md` remains a paper proof. These phase and realization bridges do not prove PBAP or establish scientific novelty.


Fresh joint-phase lint snapshot: `scripts/formal_tools.py lint` exits 1 with nine unrelated unreachable modules: RHTower `WeilPaperPacketPrimeMasks`, `WeilWorkSettledPhasePowerCoefficients`, `WeilWorkSettledPhasePowerLogMoment`, `WeilWorkSingularArithmeticGaussianBound`; HTGeometry `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. File-size warnings remain. All six current Joint leaves are wired; none appears in lint errors. This is a shared-tree snapshot, not a clean global lint claim.


Joint realization checkpoint completed: `JointProfiles`, `JointNull`, and `JointActive` all pass targeted `--old` builds and final direct `lake env lean <leaf>` source audits. All final source logs are empty. Nineteen realization and four actual-active-interface axiom checks pass, standard axioms only. Together with the earlier phase checks, all six Joint leaves and all 40 named declarations are audited. `scripts/formal_tools.py index` exits 0; the exact-null and actual-null escape capstones are present in `formal/LEAN_API.md`, with no tracked generated-index diff. Scoped `git diff --check` passes. No full/umbrella build or numerical experiment. Fourier/coercivity work remains in scratch.

Audited source hashes:

- `WeilWorkPBAPJointConvex.lean`: `673e23f41c8940aea1d5b3829e1fdf09340fdecf270d4ee9f95280783615c5e2`
- `WeilWorkPBAPJointPhase.lean`: `a602a20ebe121e894801460b87e07d222dfd86ae0f622defc25c453e14743ef2`
- `WeilWorkPBAPJointEscape.lean`: `e1747b8fcc98ee8e5038143e65473f9c9b422477c13ee99e96e2a3d2c5750573`
- `WeilWorkPBAPJointProfiles.lean`: `e6b0cc9937f35cd47e25e808617b081f46231e1fdf3b8ad14bc48a1c66ef6188`
- `WeilWorkPBAPJointNull.lean`: `0f1434d27f0265d32915e50a2c28c4de8dd761652ac74dbc55526ad9ec571d45`
- `WeilWorkPBAPJointActive.lean`: `2681b52aaaf76341422debb9102e5dd2b9ee80f3453aeb11e362fbf56c7ea39c`


After adding JointFourier, index again exits 0. Fresh lint exits 1 on seven unrelated unreachable modules: RHTower `WeilWorkDeficitXiApproximationCost`, `WeilWorkSingularArithmeticGaussianBound`; HTGeometry `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. No Joint-leaf error. The changed list reflects concurrent shared-tree work; unrelated sources were not modified.


JointFourier final checkpoint: targeted `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPJointFourier` exits 0 (245s); final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointFourier.lean` exits 0 with empty diagnostics; seven named axiom checks exit 0, standard axioms only. All seven Joint leaves and all 47 named axiom checks now pass. Prior six source hashes are unchanged. JointFourier SHA-256: `70700e3b041c3ecfb1c72d1432c76b8c36e6ca63a0f8d092c2f99f6c92ec00d5`. All seven imports are wired. The log-moment/coercivity scratch has not been run; full-energy coercivity remains paper-only.

## Literal joint full-energy coercivity (audit in progress)

The complete `/tmp/wp01-joint-coercivity.lean` scratch exits 0 with empty diagnostics. It includes exact physical/Fourier paired mass, central-band mass control, finite base logarithmic moment, full-mass actual gamma lower bound, both signed poles, explicit fixed-profile energy cost, finite-mixture lower bound, exact physical mixture mass, and actual-real-null energy/normalized-energy escape. Promoted to three wired leaves: `JointCoercivity`, `JointEnergy`, `JointEnergyEscape`. Targeted `--old` builds, final direct source audits and 24 named axiom checks are running sequentially. This is not yet a completed production-audit checkpoint.

`scripts/formal_tools.py index` exits 0 after promotion. Scoped diff check passes. Fresh global lint exits 1 with ten unrelated unreachable modules: RHTower `WeilWorkHigherDenominatorBesselBoundary`, `WeilWorkSingularArithmeticHarmonicSign`, `WeilWorkSingularArithmeticMellin`, `WeilWorkSingularArithmeticMellinBound`, `WeilWorkSingularArithmeticPoleSign`; HTGeometry `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. Existing file-size warnings remain. No new Joint-leaf error. Shared-tree work was not altered.

**Completed production checkpoint, 8 October 2026:** the sequential audit script exits 0. Targeted `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPJointCoercivity`, `...JointEnergy`, and `...JointEnergyEscape` pass (71s, 149s, 41s respectively). Each final `lake env lean GaloisForLFunctions/RHTower/<leaf>.lean` audit exits 0 with empty diagnostics. All 24 named `#print axioms` checks in `/tmp/wp01-joint-energy-axioms.lean` pass; only `propext`, `Classical.choice`, `Quot.sound` occur. All prior seven source hashes are unchanged. Ten Joint leaves and 71 named axiom checks are now complete. No owned Lean/build process remains from this audit chain.

| Audited source | SHA-256 |
|---|---|
| `WeilWorkPBAPJointCoercivity.lean` | `3206198dc05483d824d5080b76e11deadba3b52cbd9d645e07cad498044f6ee0` |
| `WeilWorkPBAPJointEnergy.lean` | `7463d28fa0ad4f8d379a51941232dcb2b5dca2516f2b4f9aae20eaa6efe61514` |
| `WeilWorkPBAPJointEnergyEscape.lean` | `689991d18da95be41e2cd63664fdde96e292d84cc31e478d1bccc05337d9da35` |

Final logs: `/tmp/wp01-final-joint-Coercivity.log`, `/tmp/wp01-final-joint-Energy.log`, `/tmp/wp01-final-joint-EnergyEscape.log`, `/tmp/wp01-joint-energy-axioms.log`. Index includes the gamma, literal-energy and both escape capstones. Global lint remains limited by the ten unrelated reachability errors listed above. Full PBAP remains open; goal stays active.
