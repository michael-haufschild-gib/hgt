# CHMD local compactness proposal: existing-result audit (2026-10-16)

User PAUSED the main RH goal, then explicitly requested a Lean corpus search to check overlap. This was a read-only mathematical audit, not resumed implementation. Do not infer permission to resume the paused goal from this memory.

## Finding
The proposed local-compactness-via-normalized-singular-Levy-averages work would DUPLICATE its stated spectral payoff. The current Lean corpus already contains the actual arithmetic resolvent results:
- `RHTower.CHMDPolar.no_weakly_null_weyl_above_half` (`CHMDNoWeylAboveThreshold.lean:258`): no unit weakly-null approximate eigenvector sequence for actual R at mu > 1/2.
- `exists_eigenvector_of_mem_spectrum_above_half` (`CHMDPurePointAboveThreshold.lean:169`): all actual spectral points above 1/2 are eigenvalues.
- `finite_eigenvalues_above` (same :194): finitely many eigenvalues >= 1/2 + epsilon for every positive epsilon.
- `finiteDimensional_eigenspace_above_half` (same :251): finite multiplicities.
- `riemannHypothesis_iff_no_primitive_bound_state` (`CHMDSpectralRiemannCriterion.lean:372`): RH iff no nonzero eigenvector of R above 1/2 orthogonal to oneL. This is an equivalence, not RH proof.

## Already available compactness ingredients
- `CHMDWindowLocalization.exists_window_levyForm_bound` (:173) controls the flat Levy energy of windowed compact C2 tests by actual Doob archimedean energy plus mass.
- `CHMDWindowFourierTail.levyForm_eq_fourier` (:143) and `fourier_tail_le` (:191).
- `RHTower.totallyBounded_of_centralSupport_of_uniformFourierTail` (`SuzukiHlogCompactEmbedding.lean:256`) gives actual precompactness for bounded, spatially supported, uniformly Fourier-tight L2 sets.
- `RHTower.totallyBounded_ccmFourierWeightUnitBall` (`CCMGeneralFourierWeightCompactEmbedding.lean:157`), plus compact closure :170, for every increasing divergent Fourier weight on a bounded interval.
- `HTGeometry.SqIntKernel.isHilbertSchmidt_op` (`SquareIntegrableKernelOperator.lean:300`) covers complex square-integrable kernels; generic Hilbert-Schmidt => compact exists.

No literal theorem `IsCompactOperator (nearMul R composed with resolvent)` or compact localized CHMD source map was found in focused corpus searches and exhaustive CHMD compactness/source-name rg searches. This is a search outcome, not proof of absence. Its spectral consequence is already established through localization + Fourier tails + weak convergence, without the recent operator core or singular averages.

## Verification
Used documented research tool directly: two deep mechanism queries, then focused lexical --any symbol queries. Broad deep results were mostly irrelevant, CHMD deep result partial (budget); exact-symbol searches found the relevant existing results. Snapshot inventory 72857/72857, no pending source inventory, but compiler metadata largely pending/stale: never equate index coverage with Lean verification. Inspected actual theorem statements/proofs and root imports. Ran `lake env lean /tmp/chmd_existing_results_audit_20261016.lean` importing CHMDSpectralRiemannCriterion and CCMGeneralFourierWeightCompactEmbedding, auditing all five spectral results and both generic compactness results with #print axioms: exit 0, only propext/Classical.choice/Quot.sound. Actual spectral module oleans newer than source at audit. No source modifications or builds; owned temporary files removed.

## Resume caution
The earlier newly-created in-progress card `docs/drafts/pipeline/1-in-progress/chmd-local-compactness-levy-averages-2026-10-16.md` predates discovery of these completed concurrent results. Do not pursue its spectral target as new frontier. Re-audit current corpus on any authorized resume. Excluding actual primitive bound states is still unproved by the results inspected; discreteness alone does not exclude them.
