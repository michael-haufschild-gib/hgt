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

## GY complex-pole orientation audit — completed 8 October 2026

`WeilWorkPBAPMollifierCausality.lean` targeted `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPMollifierCausality` passed in the preceding turn (24s). Its interrupted final-audit handles were unavailable and their temporary logs missing on continuation; no matching owned processes remained. Consequently the final direct source audit and seven `#print axioms` checks were rerun. Both exit 0; the source log is empty. The seven declarations are `poleWave_integral`, `poleWave_integral_nonneg`, `poleWave_integral_neg`, `poleWave_integrable`, `finite_poleWave_integral`, `finite_poleWave_tail`, `finite_poleWave_integral_eq_zero`, all in `RHTower.WeilWorkPBAP`. Only `propext`, `Classical.choice`, `Quot.sound` occur. SHA-256: `54567658a1d605d64ce79ef9715b90bb49610b1610dd318eae68d106a880944c`. Umbrella import verified. Final logs: `/tmp/wp01-mollifier-final-20261008.log`, `/tmp/wp01-mollifier-axioms-20261008.log`.

Index refresh passed. Global formal lint exits 1 on thirteen unrelated unreachable modules: RHTower `WeilPaperFiniteObservations`, `WeilWorkHigherDenominatorNonstationary`, `WeilWorkHigherDenominatorScaledBessel`, `WeilWorkQuantizationPeriodicSymbol`, `WeilWorkSingularArithmeticParityMellin`, `WeilWorkSingularArithmeticPolynomialMellin`, `WeilWorkSingularArithmeticPolynomialMellinBound`, `WeilWorkSingularArithmeticPolynomialTail`; HTGeometry `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. Existing file-size warnings remain; no error concerns this leaf. Unrelated shared-tree sources were not modified. This classical Fourier/Perron correction does not prove full PBAP or disprove the actual GY window conjecture.

Current constrained-energy search `/tmp/wp01-critical-cone-20261008.json`: `partial=false`, 68,586 indexed/inventoried files; background refresh incomplete, mostly pending/source-only compiler metadata. Every candidate/source statement and the full ingredient set inspected. Abstract cochain energy compactness and prime first-trace null sequences are not the actual PBAP quadratic form. The suggested ingredient chain does not establish its claimed link. `WeilPaperFiniteObservations` gives equal-mass, equal-energy null pairs with different rational samples; it supplies no energy sign. The actual polar ground-state theorem concerns a different linear pole-constrained space, not the aggregate integer-null cone. No absence claim.

## Exact joint modulation kernel — completed 8 October 2026

`WeilWorkPBAPJointJump` and `WeilWorkPBAPJointModulation` pass targeted
`lake build --old +GaloisForLFunctions.RHTower.<leaf>` (57s and 65s), followed
by final `lake env lean GaloisForLFunctions/RHTower/<leaf>.lean` audits
(36s and 6s). Both final logs are empty. The guarded sequential audit exits 0;
no full/umbrella build, numerical experiment or heartbeat increase was used.
Both imports are wired. Eleven `#print axioms` checks pass and report only
`propext`, `Classical.choice`, `Quot.sound`:

- `integrable_testGamma_jump`, `testGamma_eq_jump`, `jointModulationKernel_pos`;
- `testPole_eq_integral_cosh`, `testGamma_eq_jump_scaled`, `integrable_testGamma_jump_scaled`;
- `integrable_modulation_jump`, `jointPairRealCorr_eq`;
- `jointPairFullEnergy_sub_zero`, `jointPairFullEnergy_zero_le`, `jointPairFullEnergy_zero`.

All declarations are in `RHTower.WeilWorkPBAP`. The exact source hashes are
`3a3b73512735950623f8a07ffa8f4e92b0bcdfa6cc24707c1cb21cae9de08d17`
(JointJump) and `6ac94b5dfdcb3b1196d51ed689d6c89359ad412b96c4c68fb109860cd147ef29`
(JointModulation). Logs: `/tmp/wp01-kernel-final-WeilWorkPBAPJointJump.log`,
`/tmp/wp01-kernel-final-WeilWorkPBAPJointModulation.log`, `/tmp/wp01-kernel-axioms.log`;
stage results: `/tmp/wp01-joint-kernel-audit-state.json`.

Index exits 0. Global formal lint exits 1 on seven unrelated unreachable modules:
RHTower `WeilWorkHigherDenominatorInversionFourier`, `WeilWorkQuantizationLogarithmicSupport`;
HTGeometry `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`,
`ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. Neither new module occurs in
the errors. Existing large-file warnings remain. Unrelated shared-tree files were not changed.

Current searches are recorded in the working card. Energy-kernel search was complete at
68,597 files; jump-certificate search was partial at the same coverage; multiplicative-Hilbert
search complete at 68,599; cosine-dual-attainment search partial at 68,606. Background refresh
was incomplete and compiler metadata mostly pending/source-only. All displayed candidate and
source statements and ingredient sets were inspected. Generic positive-jump data, Hilbert
moment positivity and Riesz duality do not supply the missing actual null-cone sign. No absence
or scientific-novelty claim follows. The exact signed kernel and restricted minimum are now
formalized; full PBAP and the all-height arithmetic cosine certificate remain open.

### 8 October 2026 — uniform high-frequency estimates

`WeilWorkPBAPJointHighFrequency` is wired. Targeted `lake build --old
+GaloisForLFunctions.RHTower.WeilWorkPBAPJointHighFrequency` passed (148.0s).
Final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointHighFrequency.lean`
passed (31.6s), empty diagnostics. Seven named `#print axioms` checks passed
(5.7s), each only `[propext, Classical.choice, Quot.sound]`:
`joint_pair_gamma_eq_integral`, `joint_pair_gamma_central_loss`,
`joint_pair_gamma_high_lower`, `joint_paperFT_real_decay`,
`joint_pair_poles_high_abs`, `joint_pair_full_energy_high_lower`,
`jointPairFullEnergy_neg`. Logs: `/tmp/wp01-high-{build,final,axioms}.log`;
state: `/tmp/wp01-high-audit-state.json`. No umbrella/full build.

The exact bound retains leading Gamma coefficient 2 times base mass, with
inverse-cubic central Fourier mass loss, and controls the absolute contribution
of both signed poles by inverse-quartic modulation decay. It has domain/support
conditions only, no energy-sign premise. The actual width-sector theorem in
`JOINT-WIDTH-SECTOR.md` is still paper-only and being formalized.

`JointHighFrequency` source SHA-256:
`36ae3f774880b38b7f43ef782e1b7e60405277b8d4131e68f9b583b042f9a037`.

`WeilWorkPBAPJointScale` is wired. Targeted --old build passed (112.3s), final
direct source audit passed (34.8s; empty diagnostics), and eleven named axiom
checks passed (178.9s; standard axioms only). These cover smoothness, compact
support, interval support, physical mass, full complex autocorrelation, first
and second derivatives, the exact derivative norm cost, real autocorrelation,
its nonnegativity for actual nonnegative profiles, and complex Fourier scaling.
Source SHA-256:
`304cab39320ec541af0bfb592b729de4bb91966e3cc98b7e758167ce56fdfc6c`.
Logs: `/tmp/wp01-scale-{build,final,axioms}.log`;
state: `/tmp/wp01-scale-audit-state.json`.

Process incident: the next scratch `lake env lean` command was launched before
the scale audit wrapper returned its confirmed exit. Wrapper overlap was at
most 3.464s by audit-state modification time versus new log creation time.
Both have been reconciled; only the new scratch remains running. Subsequent
Lean commands must wait for an explicit completed tool result, not infer exit
from empty diagnostics or elapsed time. No mathematical check is claimed from
an unfinished command.

`WeilWorkPBAPJointSeedGamma` is wired and audited: targeted --old build 25.9s,
final direct-source audit 5.0s (empty diagnostics), nine named axiom checks 4.5s,
all standard axioms only. SHA-256:
`9001bbe731da8f84d8d409693b170c5bc1204f5bed95e201c076fb1f43b02b50`.
Logs `/tmp/wp01-seed-gamma-{build,final,axioms}.log`; audit state
`/tmp/wp01-seed-gamma-audit-state.json`.

Its principal theorem is the actual uniform estimate
`|Gamma(cluster(beta_W,L))+mass(cluster(beta_W,L))*log W| <= W*C(phi)`
for every separation L and 0<W<=1. The source-defined finite C(phi) is proved
integrable, including the logarithmic singularity at Fourier frequency zero.
`joint_cluster_gamma_scale_mass_bound` identifies the exact mass coefficient
for the disjoint unit-profile family. No sign assumption, producer or RH enters.
The negative full-energy seed and all-height cosine certificate are still being
assembled; this estimate alone is not the width-sector theorem.

### 8 October 2026 — exact seed pole scaling

`WeilWorkPBAPJointSeedPole` wired; targeted `lake build --old` passed (40.2s),
final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointSeedPole.lean`
passed (5.6s), empty final diagnostics. Seven named axiom checks passed (5.0s),
all `[propext, Classical.choice, Quot.sound]`. Guarded sequential audit exit 0.
SHA256 d70cd9428e6425354886743a5e8c2c901a4a0a9f5ec9fb94aa146551aed9acad.
Exact cluster pole factor, width-squared scaling and continuous profile value
at zero retain both signed poles. No seed energy sign assumed. Next scratch
`/tmp/wp01-seed-limit.lean` assembles the actual normalized seed limit.

### 8 October 2026 — literal balanced seed limit

`WeilWorkPBAPJointSeedLimit` wired; targeted `lake build --old` passed (107.1s),
final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointSeedLimit.lean`
passed (64.5s), empty final diagnostics. Eleven named axiom checks passed
(6.1s), all standard-only. Guarded sequential audit exit 0.
SHA256 7d45feeae4df90a894c7ffc20fe7de239ca81e520c970afcdf1e89073a8d7f35.
For every smooth complex unit-supported nondegenerate source, the actual
source-defined balanced width gives full energy/(base mass*width*L) -> -1,
and eventually -9mL/8<=E0<0. No negative energy, producer, or RH premise.
This closes the seed component; actual all-height correction positivity still
requires the uniform high estimate and actual active-node phase certificate.

### 8 October 2026 — uniform high-frequency width sector

`WeilWorkPBAPJointWidthHigh` wired; targeted `lake build --old` passed (63.0s),
final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointWidthHigh.lean`
passed (133.4s), empty final diagnostics. Eight named axiom checks passed
(84.7s), all standard-only; guarded chain exit 0.
SHA256 e11b4cb088df049ce6f13a4b21f6597d4dfa3a8e60c34ac16538070454106bc3.
One eventual threshold controls EVERY signed height |T|>=exp(7L/8), with
actual paired full energy >=13mL/8. Uniform remainder is explicit and uses
both signed poles, with no source sign, correction or producer premise.

### 8 October 2026 — actual integer phase in the width sector

`WeilWorkPBAPJointWidthPhase` wired; targeted `lake build --old` passed (152.7s),
final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointWidthPhase.lean`
passed (31.4s), empty final diagnostics. Five named axiom checks passed (89.5s),
all standard-only; guarded chain exit 0.
SHA256 18a5f33908b9470f03142a3e6b3a8d1222b6b619b86d2dd41b15cdb7785bc2d2.
The chosen actual integer is at least two, its lag is <=2exp(-L), its real
correlation is eventually positive, and its cosine is >=11/12 uniformly below
exp(7L/8). Activity and phase control are conclusions, never supplied premises.

### 8 October 2026 — concrete negative-seed positive sector completed

`WeilWorkPBAPJointWidthSector` wired; targeted `lake build --old` passed (43.9s),
final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointWidthSector.lean`
passed (70.2s), empty final diagnostics. Eight named axiom checks passed
(33.5s), all standard-only; guarded sequential chain exit 0.
SHA256 4e7abc165ffb97fb3b4f80b7f5b182e80187beb35f9829f8392d833d2fa55a0f.
All eight new leaves and all 66 named checks are complete. No full/umbrella
build, numerical experiment, added axiom or heartbeat increase. All owned
Lean jobs exited. `scripts/formal_tools.py index` exits 0. Scoped diff-check
passed before final report updates; final lint/diff results follow below.

The concrete source capstones assume no source sign, energy sign, active
node, crossing, cosine certificate, RH or positivity producer. Their proofs
construct/pay each fact. Real nullness and nonnegative finite correction
weights are the actual target-domain constraints. The sector does not span
arbitrary profiles or the full null cone.

Latest next-boundary search `/tmp/wp01-one-node-boundary-20261008.json` has
partial=false, 68,685 indexed files, refresh incomplete/compiler metadata
mostly pending/source-only. All20candidate/all20source statements, both proof
ideas and ingredient set inspected; the truncated source-head statement was
read directly. RH-dependent negative witnesses and a nonpositive-source-head
decomposition do not supply the actual upper-energy estimate for the next
one-node boundary. Exact cosine correction still needs its phase-closure
input. No absence or novelty inference is made from this search.

Final integration checks: index exit0; scoped `git diff --check` exit0.
Global formal lint exit1 reports unrelated HTGeometry reachability errors:
`ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`,
`ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. No new WP01 module
error. Existing unrelated large-file warnings remain; all eight new leaves
are below 500 lines. No repair or rewiring of unrelated modules attempted.

### 8 October 2026 — exact-mass modulated upper bound

`WeilWorkPBAPJointUpper` wired; targeted `lake build --old` passed (25.4s),
final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointUpper.lean`
passed (6.3s), empty final diagnostics. Six named axiom checks passed
(10.6s), all `[propext, Classical.choice, Quot.sound]`; guarded sequential
chain exit0. The repaired API probe also passed (189.8s). No overlapping
owned Lean processes, full build, numerical experiment or heartbeat change.
SHA256 b7895a07238b4397cd8ca34181305c40f44271e0cf4e3ef7724d0e56d0cfccc1.

The exact Gamma main coefficient is 2m. Its remainder is the actual first
Fourier moment divided by 1+T, and that moment is invariant under physical
dilation. The full upper bound retains both signed poles. This verifies
equations (1)--(2) of JOINT-ONE-NODE-BOUNDARY; the boundary and positive
survivor capstones are still unformalized. Novelty unestablished.

Additional corpus searches: first-moment partial=false68,700files; three-band
boundary partial=true68,705files; prime-lag lower bound partial=true68,711files.
All20candidate/all20source results and all ingredient sets inspected in each.
Refresh incomplete, compiler metadata mostly pending/source-only. Existing
linear-weight Fourier integrability was reused. Generic prime-log bounds,
nearest-integer definitions and conditional RH identities do not supply the
needed quantitative prime half-log lag lower bound.

### 8 October 2026 — quantitative actual seed poles

`WeilWorkPBAPJointPoleBounds` wired; targeted `lake build --old` passed
(240.2s), final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointPoleBounds.lean`
passed (64.4s), empty diagnostics. Six named axiom checks passed (4.9s),
all standard-only; guarded sequential chain exit0.
SHA256 3c093d8a7d5e01b6fd4e4f61e3b196005c7e6344e67c398d6cefbd9df1036119.
The actual pole profile has explicit error <=norm(sourceIntegral)^2*W^2/2
for 0<W<=1. Concrete unit-bump capstones pay correlation nonnegativity;
no energy-sign or rate premise is supplied. This closes the quantitative
pole obligation in equation (6), but not the boundary classification itself.

### 8 October 2026 — uniform full seed expansion

`WeilWorkPBAPJointSeedExpansion` wired; targeted `lake build --old` passed
(167.8s), final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointSeedExpansion.lean`
passed (174.8s), empty diagnostics. Three named axiom checks passed (21.0s),
standard-only; guarded sequential chain exit0.
SHA256 5c389245b817c5fa085bea989404b239c6cb4f0e2b2c4fe819ea0fedd9f291d3.
The literal full seed has explicit error <=W*C_gamma+(cosh(L/2)-1)*W^4*B^2
after subtracting its logarithmic Gamma and signed pole leading terms.
The bound is uniform in width and separation, including the actual unit bump.
No continuity-rate or energy-sign premise is added. The three new leaves
and fifteen public axiom checks are complete; boundary classification OPEN.

### 8 October 2026 — actual prime half-log phase scale

`WeilWorkPBAPJointPrimeLag` wired; targeted `lake build --old` passed (53.2s),
final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointPrimeLag.lean`
passed (6.8s), empty diagnostics. Five named axiom checks passed (6.4s),
standard-only; guarded sequential chain exit0.
SHA256 599f0faa32878bce7826331701650bcb53ed10cdf5034cee81e60676acc4af0b.
Prime nonsquareness gives the literal nearest lag lower bound1/(2p), strict
negative sign and the matching logarithmic scale bounds L-log2 and2L+log2.
All four new leaves, four final source audits and twenty public axiom checks
are complete. No numerical experiment, full/umbrella build or added axiom.

Current integration checks: `scripts/formal_tools.py index` exits0;
scoped `git diff --check` exits0. `scripts/formal_tools.py lint` exits1 on
eight unrelated umbrella reachability errors: RHTower
`WeilWorkQuantizationRadicalMass`, `WeilWorkSettledPhaseLocalPolynomialModels`,
`WeilWorkSettledPhaseLocalPolynomialPeriods`; HTGeometry
`ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`,
`ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. No new WP01 leaf
is flagged. Unrelated large-file warnings remain. Every owned Lean, build,
search, index and lint command has exited. No commit or push.

### 8 October 2026 — uniform sharp high-frequency bridge

`WeilWorkPBAPJointUniformHigh` wired. Targeted `lake build --old +...` passed
(37.0s); final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointUniformHigh.lean`
passed (7.4s), empty diagnostics. All seven public theorem axiom checks passed
(5.1s), using only `propext`, `Classical.choice`, `Quot.sound`; sequential
chain exit0. SHA256 cf2375c6afe9f44e8f3716b48cc44d93e16bc26daecde93e6927b2ee345573b0.
The literal unit-bump capstone pays all source hypotheses. One threshold
controls every width in `[κL exp(-L/2),1]` and every signed height at least
`exp(7L/8)`. Exact logarithmic coefficient 2 survives both bounds.
This is a BRIDGE for conjecture C, not full PBAP or a novelty claim.

### 8 October 2026 — uniform logarithmic seed expansion at actual primes

`WeilWorkPBAPJointBoundarySeed` wired. Targeted `lake build --old +...` passed
(63.2s), final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointBoundarySeed.lean`
passed (18.3s), empty diagnostics. All eight public theorem axiom checks
passed (56.6s), standard-only; sequential chain exit0.
SHA256 6bf9a1d7dd8b3eb3f2e3deab7d0a9618c41ccc6686b1fccd7dfb0183234d844f.
The normalized literal seed differs from `-2s+2(d-1)log L` by a single
source-defined bound, uniform over the complete permitted lag range.
An actual-prime capstone derives that range and small separated width.
No phase-scale, source-sign, or energy estimate is supplied as a premise.

### 8 October 2026 — opposite-phase obstruction at d<1

`WeilWorkPBAPJointBoundaryObstruction` wired. Targeted build passed160.7s;
final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointBoundaryObstruction.lean`
passed25.6s, empty diagnostics. Both public theorem axiom checks passed5.9s,
standard-only; chain exit0.
SHA256 4c7bea07919b193a412b3023beba162f4bf48a53430d395d2db17e5c47bc0fdf.
Uniformly throughout the allowed lag range, the two literal energies at
0 and pi*exp(s) have negative sum for d<1. Hence no real coefficient supplies
a global cosine certificate with phase exp(-s). This is not a negative
all-integer-null mixture and does not refute PBAP. Positive d>1 survivor
and actual-prime/null transfer remain under implementation.

### 8 October 2026 — positive three-band survivor at d>1

`WeilWorkPBAPJointBoundaryCertificate` wired. Targeted build passed94.1s;
final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointBoundaryCertificate.lean`
passed10.2s, empty diagnostics. Its public capstone axiom check passed4.8s,
standard-only; chain exit0.
SHA256 57846612416c0f8e91464f8758d2444046c4ba92673de1a5d53fd4ad34f14cf8.
The explicit positive normalized coefficient `2s-(d-1)log L` gives margin
`(d-1)log L/2` at every real frequency, uniformly over the permitted lag range.
Low frequencies use the literal seed minimum and quadratic phase defect;
middle frequencies use nonnegative cosine; the final band retains `2log|T|`.
All four new leaves and eighteen public checks are now audited. The analytic
classification for d≠1 is formalized; actual-prime/null-mixture transfer is
under implementation. The d=1 case and full PBAP remain OPEN.

### 8 October 2026 — actual-prime boundary capstones

`WeilWorkPBAPJointBoundaryPrime` wired. Targeted build passed29.8s;
final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointBoundaryPrime.lean`
passed68.2s, empty diagnostics. All six public theorem axiom checks passed
146.1s, standard-only; chain exit0.
SHA256 bba6ce1fb0712a32640444f24fd2b9d6a9d81eabdb54fbf206c6f9752bb825e6.
The actual prime lag is exactly exp(-s) up to the harmless cosine sign.
Nearest-node activity is uniform over all widths above the balanced lower
width. The actual source seed is negative. At every sufficiently large prime,
no coefficient works for d<1, while the explicit positive coefficient works
at every real frequency for d>1. No source-sign, phase-scale or energy premise
is supplied. Null-mixture transfer is the remaining C implementation step.

### 8 October 2026 — full null-mixture boundary margin and nonemptiness

`WeilWorkPBAPJointBoundaryNull` wired. Targeted build passed156.0s;
final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointBoundaryNull.lean`
passed158.3s, empty diagnostics. Both public capstone axiom checks passed17.1s,
using only `propext`, `Classical.choice`, `Quot.sound`; chain exit0.
SHA256 73afc90b86fcaadf68573dac348304a2f619e2c9dc5e57798b861209a6da8235.
`exists_jointPrimeBoundary_null_energy` proves the literal physical-mass
margin `(d-1)log L/4` for every real integer-null correction. The sector
capstone constructs such corrections at every prescribed M>1, with positive
physical mass and negative actual seed. Source data and phase activity are
proved, not supplied. Conjecture C is complete for d≠1: six new leaves,
26 public theorem axiom checks, six targeted builds and six final source
audits. Every owned audit process has exited; no full or umbrella build.
The exact d=1 point and full PBAP remain OPEN.

Final six-leaf integration: `scripts/formal_tools.py index` exits0. Scoped
`git diff --check` exits0; all six new Lean leaves and the new boundary paper
have empty no-index whitespace diagnostics. All six hashes still match their
final source audits. `scripts/formal_tools.py lint` exits1 on twelve unrelated
umbrella reachability errors: RHTower `WeilWorkHigherDenominatorReciprocalCutoff`,
`WeilWorkQuantizationResonanceEnergy`, `WeilWorkQuantizationResonanceMean`,
`WeilWorkSettledPhaseCoprimeVariance`, `WeilWorkSettledPhasePrimeDeletionSummability`,
`WeilWorkSettledPhasePrimeDeletionVariance`, `WeilWorkSingularArithmeticNotchLocalization`;
HTGeometry `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`,
`ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. No WP01 leaf is flagged.
Existing large-file warnings remain. These replace the earlier eight-error
snapshot; unrelated concurrent work is outside this task's write scope.

## Many-node continuous component — 8 October

`WeilWorkPBAPJointContinuousCertificate`: targeted `lake build --old +<leaf>`
passed79.05s; final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPJointContinuousCertificate.lean`
passed93.31s with no source diagnostics; nine public axiom checks passed227.82s,
using only `propext`, `Classical.choice`, `Quot.sound`. The sequential audit
chain exited0 and the leaf is wired. SHA256
`b547a8fe23ac6664b134dc43f61fc4cd21e05485daf4eea9d47fc55545140849`.
Audited declarations: `jointCosineIntegral_zero`, `jointCosineIntegral_eq_pair`,
`jointCosineIntegral_nonneg`, `jointCosineIntegral_le_zero`,
`jointModulationKernel_pole_le`, `jointPairFullEnergy_continuous_certificate`,
`jointCosineIntegral_dilate`, `joint_dilated_continuous_certificate`,
`jointUnitBump_continuous_certificate`.

This is the continuous MC2/MC3 component only. MC2/MC3 discrete certificates
and the arbitrary-complex-profile MC4 capstone are paper proved, Lean OPEN.
Search coverage, primary-parent audit and the repaired foreground-process
overlap are recorded in `JOINT-MANY-NODE-CERTIFICATE.md`. No numerical
experiment, full/umbrella build, new axiom or heartbeat increase was used.

`WeilWorkPBAPJointShortPrefix`: targeted `--old` build passed125.40s;
final direct `lake env lean <leaf>` source audit passed100.73s with no source
diagnostics; `joint_short_phase_prefix` and `joint_short_phase_weighted`
axiom checks passed11.04s, standard axioms only. Sequential chain exited0;
import wired. SHA256
`0168884c2438170221f674809c825165593319f9df64aaf06e5f6a2dac0d5f98`.
The actual short length and derivative order remain explicit; signed Abel
weights cost finite total variation. This is a classical-mechanism bridge.
The displayed phase-budget inequalities still need proof on the actual
logarithmic integer intervals before applying it to MC2/MC3/MC4.

`WeilWorkPBAPJointGammaFloor`: targeted `--old` build passed67.36s;
final direct `lake env lean <leaf>` audit passed25.16s, no source diagnostics;
six named axiom checks passed96.68s, standard axioms only. Import wired.
SHA256 `bcb1998787b36b0de2838a1784e93480967f22a016f83b5248322c756700c8db`.
Audited: `jointLogDeficit_nonneg`, `jointLogDeficit_integrable`,
`joint_gamma_width_lower`, `jointPairDensity_le_l1`,
`joint_pair_gamma_width_floor`, `joint_dilated_gamma_floor`.
This is the modulation-uniform Gamma component for arbitrary complex
profiles; the exact paired mass retains coefficient two. The finite fixed
log-deficit integral is left symbolic, so no integral evaluation or numerical
experiment is required. Both the actual density and its integrability are
proved from the existing Fourier-square interface.

`WeilWorkPBAPJointSignedCertificate`: final optimized-source targeted
`--old` build passed77.82s; final direct `lake env lean <leaf>` audit
passed63.46s with no source diagnostics; seven public axiom checks
passed65.09s, standard axioms only. Chain exited0 and import is wired.
SHA256 `cb5fa935f1f761066aede0ab7ccd7f41e0d362bda7b16a6ce6e38c486f72c5dc`.
Audited: `jointAbsCorrMass_nonneg`, `jointAbsCorrMass_pos`,
`jointAbsCorrMass_dilate`, `joint_pair_pole_eq_cosine_integral`,
`joint_pair_pole_cosine_error`, `joint_dilated_pole_cosine_error`,
`joint_dilated_signed_certificate`. The earlier passing source emitted
a redundant ring suggestion; an explicit power identity and associativity
removed it, followed by all three final audits again.

These four new leaves have 24 standard-only public theorem audits, four
targeted `--old` builds and four final direct-source checks. No full or
umbrella build. The actual discrete MC2--MC5 capstones and the stronger
source-uniform two-window MC6 remain Lean OPEN.

Integration: index exited0 (15.91s); global lint exited1 (17.70s) on five
unrelated HTGeometry umbrella-reachability errors: `ApertureConeCalculus`,
`ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
`BoundaryCoronaCStarAlgebra`. No WP01 finding. This replaces the earlier
twelve-error snapshot; other concurrent research files were not modified.

## Source-uniform two-window components — 8 October

`WeilWorkPBAPJointSourceBudget`: targeted `lake build --old +<leaf>`
PASS88.71s; final `lake env lean <leaf>` PASS54.16s, empty source log;
eight public axiom checks PASS12.91s, only propext/Classical.choice/Quot.sound.
Import wired. SHA256
`719e958d2a8b0c61801b2e43d60239374dce7b0f2f27875a658730cc9f2db96a`.
Audited declarations: `joint_l1_sq_le_width_mass`,
`joint_fourier_sq_le_width_mass`, `joint_source_fourier_integrable`,
`joint_source_gamma_integrable`, `joint_source_log_deficit_integrable`,
`joint_source_log_deficit_le`, `joint_source_gamma_width_floor`,
`joint_two_source_gamma_width_floor`. The fixed log-deficit integral remains
symbolic. No profile derivative norm or nonzero source integral is assumed.

Development diagnostics isolated a default-heartbeat timeout in compact
support inference for the squared norm. An explicit support-subset proof
and typed integrands removed the issue; no heartbeat option was changed.
The completed scratch passed20.86s before production promotion. Audit chain
12142 then passed all three production steps and exited1 only on the
independent complex-quadrature development scratch, whose errors remain
under repair. That scratch is not a production module or capstone.

Source-uniform Gamma search: partial=false,68,819 indexed files; all twenty
candidate lemmas and twenty source arguments inspected, no proof ideas or
ingredient sets returned. Complex quadrature search: partial=false,68,820
files, all twenty candidates and twenty arguments inspected; background
refresh active, compiler metadata mostly pending. The existing complex BV
quadrature and elementary interval FTC machinery were inspected. MC6 and
its MC7 sparse-many-window extension remain paper proved, Lean OPEN.

`WeilWorkPBAPJointLogQuadrature`: targeted `--old` build PASS87.11s;
final direct `lake env lean <leaf>` PASS80.17s with empty diagnostics;
seven public axiom checks PASS6.64s, standard three axioms only. Import
wired. SHA256
`f20797bd05d04901187efdb75fe151459c84c135e10cbc0a4bd6cb36928f70f0`.
Audited: `jointLogGridIntegrand_hasDerivAt`, `jointLogGridIntegrand_deriv_le`,
`jointLogGridIntegrand_quadrature`, `jointLogGridIntegrand_integral`,
`joint_log_fourier_quadrature`, `joint_log_cutoff_variation`,
`joint_log_short_phase_weighted`. Every derivative falls on the auxiliary
cutoff. The explicit short-phase numerical budgets still require proof
on the actual growing-order logarithmic intervals.

All six new supporting leaves: 39 standard-only public audits, six targeted
builds, six final direct-source checks, imports verified, no umbrella build.
All nine new owned files passed whitespace checks; the two latest hashes
were rechecked. Scratch failures were confined to typing, conversion,
set/finset membership and one missing argument; the final source has no
diagnostics or heartbeat overrides.

Latest index PASS16.29s; lint EXIT1 21.60s. Exact eight unrelated
reachability errors: `RHTower.WeilPaperCompletedLogMoment`,
`RHTower.WeilWorkQuantizationHarmonicFinitePart`,
`RHTower.WeilWorkQuantizationLaurentFinitePart`,
`HTGeometry.ApertureConeCalculus`, `HTGeometry.ApertureConeWinding`,
`HTGeometry.ApertureLogTranslation`, `HTGeometry.ApertureOpenHistoryIdeal`,
`HTGeometry.BoundaryCoronaCStarAlgebra`. No WP01 finding. This supersedes
the earlier five-error snapshot. Audit chain9967 has exited1 only at lint;
all three Lean steps and index passed. No owned build process remains.
MC6 and its sharper MC8 geometric-row extension remain Lean OPEN.

## Literal uniform cutoff — 8 October

`WeilWorkPBAPJointFixedCutoff`: targeted `lake build --old +<leaf>`
PASS226.30s; final `lake env lean <leaf>` PASS116.70s, empty source log;
all 28 public theorem axiom checks PASS80.67s. Every printed dependency is
one of propext/Classical.choice/Quot.sound. Import wired. SHA256
`3c8ea12453c2b4883d64fc75c2b79a32a7c6b005caff939e54d7a8c6e3902525`.
All six preceding supporting-leaf hashes are unchanged. The seven leaves
now have 67 public audits, with no full/umbrella build or heartbeat change.

The leaf constructs psi(y)=plateauBump(4,y+2), proves its evenness,
plateau, compact support, smoothness and `2<=integral psi<=4`, and bounds
v(y)=psi(y/W)cosh((L+y)/2)/cosh(L/2) uniformly in every real L, `0<W<=1`.
One constant controls v, W v', and W^2 v''. The exact integral differs
from W*integral(psi) by at most `4e W^2`; the complex Fourier integral
satisfies `|Fourier(v)(t)| t^2<=C/W`. Derivatives belong solely to the
fixed auxiliary cutoff. These are technical MC6 components, not positivity
capstones or an independent scientific novelty claim.

Development repairs: use the additive bounded-range API, the correct
absolute-value triangle name, explicit real-to-complex derivative casts,
and the verified finite-order-to-infinity comparison for ContDiff.
The complete scratch passed110.85s before promotion. No proof hole or
heartbeat override was introduced. New source and owned tracked diff pass
whitespace checks.

Searches: growing derivative order partial=false,68,839 files; Fourier
decay partial=false,68,843; interval geometry partial=false,68,847. All
20 candidate lemmas and 20 source arguments from each were inspected;
no proof ideas/ingredient sets returned. Background refresh/compiler
freshness remain pending. The narrower lexical Sieve search found nine
ranked declarations, including `log_factorial_le` and blockLambda schedule
interfaces. Source inspection reused the existing exact two-IBP bound and
ratio-bounded window-landing theorem. The latter gives a shorter paper
schedule proof with three uniform inequalities; it does not itself pay
those inequalities on the actual intervals. Geometry scratch is now active.

Index PASS15.40s; global lint EXIT1 19.10s on nine unrelated reachability
errors: RHTower `WeilWorkSettledPhaseDiskHurwitz`,
`WeilWorkSettledPhaseLogSquareEnergy`, `WeilWorkSettledPhaseValuationAnalytic`,
`WeilWorkSettledPhaseValuationTwist`; HTGeometry `ApertureConeCalculus`,
`ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
`BoundaryCoronaCStarAlgebra`. No WP01 finding. This supersedes the prior
eight-error snapshot; unrelated files were preserved. Audit chain27582
has closed with exit1 solely from lint. MC6, MC8 and full PBAP remain OPEN.

## Actual growing-width interval geometry — 8 October

`WeilWorkPBAPJointGridGeometry`: targeted `--old` build PASS8.18s;
final direct `lake env lean <leaf>` PASS4.39s, empty log; all six public
axiom checks PASS2.04s, only propext/Classical.choice/Quot.sound. Import wired.
SHA256 `0605374cc514f3df13873bda2ceef89d6528e2dadde0a3d1bbae377898194cff`.
The eventual conclusions discharge every generic geometry condition for
W=b L log log L exp(-L/2), b>0. Actual floor/ceiling endpoints have
2<=n, N/2<=n<=N, n<m<=2n+1 and 2NW<=H<=(4e+3)NW; their logarithms enclose
[-2W,2W]. Both rounding errors and the extra endpoint are explicit.

Audited declarations: `joint_grid_geometry`, `jointUniformWidth_grid_scale`,
`tendsto_jointUniformWidth_zero`, `eventually_jointUniformWidth_grid_bounds`,
`eventually_jointUniformWidth_grid_geometry`,
`eventually_jointUniformWidth_log_cover`. The complete scratch passed9.55s.
Imports were reduced to the four required mathlib modules. Development
repairs were a root-namespace API, a zero-limit multiplication conversion,
and explicit multiplication of positive inequalities instead of asking
nonlinear automation to invent those products. No heartbeat changes.
Eight supporting leaves now have 73 public audits. MC6/MC8 remain Lean OPEN.

Index PASS15.94s; lint EXIT1 12.21s on eleven unrelated reachability errors:
RHTower `WeilWorkQuantizationCenteredSource`, `WeilWorkSettledPhaseDiskHurwitz`,
`WeilWorkSettledPhaseLogSquareEnergy`, `WeilWorkSettledPhaseValuationAbsolute`,
`WeilWorkSettledPhaseValuationTwistSummability`,
`WeilWorkSettledPhaseValuationZeroFree`; HTGeometry `ApertureConeCalculus`,
`ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
`BoundaryCoronaCStarAlgebra`. No WP01 finding. This supersedes the preceding
nine-error snapshot. Chain60738 closed with exit1 solely from lint. The
next growing-order scratch is active; no second owned Lean process runs.

## Actual growing-order phase schedule — 8 October

`WeilWorkPBAPJointGrowingOrder`: targeted `--old` build PASS80.70s;
final `lake env lean <leaf>` PASS10.48s, empty diagnostics; all nine public
axiom checks PASS30.31s, only propext/Classical.choice/Quot.sound. Import
wired. SHA256 `8b2dade143b3447a3f1991daf4dd9153cca234d91322be9c46bef5abfa08cb61`.
The complete scratch passed24.65s before promotion. The literal order cap
pays both power costs and the factorial endpoint cost. The three actual
landing-window inequalities are discharged uniformly in the full stated
middle range; the every-prefix saving has explicit exponent and constant.
No numerical side-budget or heartbeat override remains. This is a bridge,
not a positivity capstone or independent scientific novelty claim.
Nine supporting leaves now have 82 public theorem audits.

Fresh cutoff/Abel search `/tmp/wp01-actual-middle-cutoff-search.json`:
partial=false,68,870 files, stale coverage snapshot, background refresh
incomplete and compiler metadata pending. All20 candidates and all20 source
arguments inspected; no proof ideas/ingredient sets. Existing log-cutoff
variation and complex quadrature remain the applicable components. No
absence or novelty inference is drawn from retrieval.

Index PASS17.04s; lint EXIT1 19.67s on seven unrelated umbrella errors:
RHTower `WeilWorkQuantizationGaussianRecovery`,
`WeilWorkSingularArithmeticPoissonEuler`; HTGeometry `ApertureConeCalculus`,
`ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
`BoundaryCoronaCStarAlgebra`. No WP01 finding. This supersedes the eleven-error
snapshot. Audit chain16016 closed with exit1 solely from lint. Current
scratch `/tmp/wp01-middle-cutoff.lean` pays actual cutoff Abel weights and
the logarithmic saving cost; MC6, MC8 and full PBAP remain OPEN.

## Literal complex middle-frequency discrepancy — 8 October

`WeilWorkPBAPJointMiddleCutoff`: targeted `--old` build PASS112.29s;
final `lake env lean <leaf>` PASS93.66s, zero-byte diagnostics; eleven
public axiom checks PASS41.38s, only propext/Classical.choice/Quot.sound.
Import wired. SHA256
`9b36807287880bec95fdf6b22b9f194073df752d8e7ff82bee1b3cb512c5235e`.
The complete scratch passed66.03s before promotion. Ten supporting leaves
now have 93 public theorem audits. No full build or heartbeat change.

The leaf pays actual fixed-cutoff Abel variation, exact phase conjugacy,
both frequency signs, the continuous Fourier term and the literal complex
grid-minus-integral error. For eta=c log2<1 its exact `2 cosh(L/2)` factor
is bounded by an eventually nonnegative o(L) function, independent of source
profiles. The Fourier tail bound follows from the paid inequality Wt^2>=N.
This closes the middle-band estimate, not MC6, MC8 or full PBAP. Development
repairs were explicit positive product inequalities, exposing a composed
logarithm, and normalizing rational exponents before limit congruence.

Index PASS15.01s; lint EXIT1 23.50s on five unrelated HTGeometry umbrella
errors: `ApertureConeCalculus`, `ApertureConeWinding`,
`ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
`BoundaryCoronaCStarAlgebra`. No WP01 finding. This supersedes the seven-error
snapshot. Audit chain56663 CLOSEDexit1 solely from lint. Owned scoped and
new-file whitespace checks are clean. Active scratch
`/tmp/wp01-grid-frequency.lean` handles full cutoff quadrature, low-band
sublinear loss and exact leading high-frequency mass. MC6/MC8 remain OPEN.

## Actual low/high frequency estimates — 8 October

`WeilWorkPBAPJointGridFrequency`: targeted `--old` build PASS196.55s;
final `lake env lean <leaf>` PASS156.47s, empty diagnostics; twelve public
axiom checks PASS156.63s, only propext/Classical.choice/Quot.sound.
Import wired. SHA256
`8a6514877d9407680ac750df738b47c7fb396a2857ae865e3bb15108209ee69e`.
The complete scratch passed55.66s. Eleven supporting leaves now have105
public theorem audits. No full/umbrella build or heartbeat change.

Full complex quadrature pays actual endpoints and cutoff derivatives.
The low error has a nonnegative o(L) majorant under the exact pole factor.
The high envelope retains Apsi W and pays both W² and exponential errors;
above the growing ceiling it leaves3L/4 against log|t|. A finite bound at
all frequencies supplies the source-density integrability budget. Repair
history: stop monotonicity automation before it splits a sum incorrectly;
force the real integral before casting to complex; remove redundant ring
steps after field_simp. Five new-file whitespace checks are clean.

Index PASS17.10s; lint EXIT1 29.59s on eleven unrelated umbrella errors:
RHTower `WeilWorkDeficitCriticalMellin`,
`WeilWorkSettledPhaseCenteredContour`, `WeilWorkSettledPhaseCenteredConvolution`,
`WeilWorkSettledPhaseCenteredEnergy`, `WeilWorkSettledPhaseCenteredMellin`,
`WeilWorkSettledPhaseCenteredPhaseCost`; HTGeometry `ApertureConeCalculus`,
`ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
`BoundaryCoronaCStarAlgebra`. No WP01 finding. This supersedes the five-error
snapshot. Audit19927 CLOSEDexit1 solely from lint.

Gamma join search partial=false,68,882 files; Fourier-continuity search
partial=false,68,885. All20 candidates/all20 source arguments from each
were inspected; no proof ideas/ingredient sets. Background refresh and
compiler metadata remain pending; the latter search had a stale coverage
snapshot. Continuity hits included three temporary copies; the inspected
production `WeilHerglotz.continuous_paperFT_real` is reused. Circular
positive-Weil statements are inapplicable. No novelty inference.
Active `/tmp/wp01-symbol-floor.lean` joins all bands and integrates the
actual corrected symbol against arbitrary narrow-source Fourier densities;
its L/3 mass target remains under Lean verification. MC6/MC8/full PBAP OPEN.

## Corrected-symbol coercivity — 8 October

`WeilWorkPBAPJointSymbolFloor`: targeted `--old` build PASS48.98s;
final `lake env lean <leaf>` PASS84.00s, empty diagnostics; nine public
axiom checks PASS11.03s, only propext/Classical.choice/Quot.sound. Wired.
SHA256 `0296bfa01280831c3750eb329d2e7a1dbf907b02c1d880a98eec0170305730e0`.
Complete scratch PASS6.38s after the core PASS100.68s. Twelve supporting
leaves now have 114 public theorem audits. No full or umbrella build.

All three frequency bands join the same integrable Gamma deficit. The
actual corrected symbol is integrable against every narrow-source Fourier
density and leaves L/3 times physical mass. The two-source statement pays
b=1/(8 log2), using the proved bound Apsi<=4. No arbitrary numerical
schedule or source-derivative hypothesis is supplied. Repairs: use an
explicit function equality for Fourier continuity; expose Pi subtraction
before ring normalization. Actual source-energy identities and MC6/MC8
remain OPEN. This is a BRIDGE, with no scientific novelty claim.

Index PASS16.15s; lint EXIT1 21.51s on thirteen unrelated umbrella errors:
RHTower `WeilWorkExposingRayCriticalSeries`, `WeilWorkQuantizationGaussianGram`,
`WeilWorkSettledPhaseCenteredContour`, `WeilWorkSettledPhaseCenteredConvolution`,
`WeilWorkSettledPhaseCenteredEnergy`, `WeilWorkSettledPhaseCenteredMellin`,
`WeilWorkSettledPhaseCenteredPhaseCost`, `WeilWorkSettledPhasePhaseCostDichotomy`;
HTGeometry `ApertureConeCalculus`, `ApertureConeWinding`,
`ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`.
No WP01 finding. Audit87474 CLOSEDexit1 solely from lint. This supersedes
the eleven-error snapshot; unrelated work is preserved.

Two-source Gamma/pole hybrid searches hit their deadlines with partial
coverage (68,893 and 68,891 files) and no returned candidates/arguments.
Lexical fallbacks find the actual `testGamma_eq_jump_scaled` and
`testPole_eq_integral_cosh` declarations in `JointJump`; both inspected.
The production polarized-convolution expansion and translation identities
provide unconditional source algebra. Its positive-Weil spectral theorems
are inapplicable. Active scratch `/tmp/wp01-two-source.lean` handles exact
cross-correlation, support, mass and source-uniform bounds.
