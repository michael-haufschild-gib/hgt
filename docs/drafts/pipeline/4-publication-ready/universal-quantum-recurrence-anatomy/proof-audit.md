# Proof audit

Date: 2026-08-24

Scope: internal verification ledger. Not part of submitted manuscript.

## Admission rule

Every mathematical result stated in `main.tex` and `body.tex` must be an exact specialization or direct composition of closed declarations in `claim-trace-localization.md`. Definitions, interpretations, literature summaries, and explicit nonclaims are not theorem claims.

## Headline closure

Local load-bearing result is `exists_quditPath_everyChart_sameDraw_recurrenceCollisionLaw` in `formal/GaloisForLFunctions/HTGeometry/QuditPathRecurrenceCollisionCapstone.lean`. For every `n,q >= 2`, it provides exact Hermitian onsite-plus-nearest-neighbour path coordinates, proves a nonempty simple chart exists, and quantifies over every nonempty preconnected open simple-spectrum chart. One conull set in that chart simultaneously has:

- maximal balanced projective rank `D - 1`, `D = q^n`;
- stroboscopic anchored-gap first-hit exponent `D - 1`;
- first-gap-clock winding exponent `D - 2`;
- every positive-weight collision floor, every order;
- every corresponding long-time symmetric survival-moment floor;
- no nonzero exact anchored projective return.

No qubit-only restriction remains.

Four-law factorization is closed independently at each exact reduction:

1. `finiteContraction_returnThreshold_dichotomy` selects the persistent carrier and exact late-return ceiling.
2. `projectiveTemporalRank_add_relationRank`, `spectralRelationLattice_eq_iff_phaseEnsemble_eq`, first-hit laws, and replica-collision equivalence close relation-hull geometry.
3. Reverse-water target/deadline declarations and `finite_quantum_observer_coherence_law` close weighted and observable geometry.
4. `exists_lbitEnergy_maximal_uniformly_close` plus `selfAdjoint_heisenbergEvolution_norm_sub_le` close finite-horizon arithmetic ambiguity; the countable relation-metric theorem closes the pure-point extension.

Commuting-local boundary is closed by l-bit temporal-rank, geometric-locality, and uniform-state declarations listed in `claim-trace-localization.md`.

## Local proof closure

Manuscript local proof now follows actual checked route:

1. `exists_quditPathChain_spectrumEscapes` identifies exact open-path locality and affine spectral escape.
2. `hermitianLocalExtensionSlice_spectrumEscapesAffineRelations` is one-leaf engine.
3. `crossLayer_eq_of_selectedLayerAnalyticBranchConstantAction` derives cross-layer coefficient equality from exact second-order response and simple-pole rigidity.
4. `hermitianLocalExtension_constantAction_coefficients_constant` propagates equality across connected lift.
5. `crossLayerLiftGraph_preconnected_of_two_le_card` proves lift connectivity from connected nonbipartite endpoint transition support for every local dimension at least two.
6. `exists_codedIntegerLayerShift_injective` supplies simple product spectrum.
7. Physical leaf conjugation preserves exact old-local plus new-onsite plus single-new-edge support.

Old informal Pauli endpoint argument was removed.

## Universal and thermodynamic closure

Closed sources cover persistent-carrier selection; rank conservation and exact relation hull; reverse-water target and deadline bounds; observer graph capacity; finite-horizon ambiguity; countable pure-point recurrence; l-bit classification; Dirichlet bound; non-VWA first-hit exponent; exact replica expansion; long-time collision identity; all-order floor equivalence; exact chord-return density; no exact nonzero return; and thermodynamic extinction/rates. Exact mappings are in `claim-trace-localization.md`.

## Quantifier and limit-order audit

- Loss law is only for finite-dimensional contractions; manuscript does not universalize Hilbert--Schmidt contractivity to every channel.
- Full Hermitian path-local subspace is used. Scalar identity direction is retained.
- One coefficient draw satisfies all headline clauses.
- Collision statements require strictly positive spectral weights; manuscript normalizes them to sum one for survival fidelity.
- `D - 1` exponent is discrete/stroboscopic.
- `D - 2` exponent is first-gap-clock normalized.
- Completed-time density and moments are taken at fixed finite size before `n -> infinity`.
- Countable extension assumes normalized summable pure-point weights and states a covering-number deadline, not finite temporal rank.
- No finite-time convergence rate for completed density or infinite-volume global recurrence is asserted.

## Kernel checks

- Unified targeted audit of 42 load-bearing declarations: passed; each depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- Direct capstone file elaboration: passed.
- Named capstone target build: passed. No umbrella target built.
- `#print axioms` for both new declarations: only `propext`, `Classical.choice`, `Quot.sound`.
- New capstone module: no `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration.
- Project-wide lint retains unrelated pre-existing reachability errors; paper does not treat global lint as clean.

## Manuscript independence

Publication files must contain no mention of formal tooling, internal corpus, HGT, Riemann-hypothesis work, black holes, or circuit complexity. Loss, contractive channels, and finite-horizon inference are included only through the exact standalone four-law factorization.
