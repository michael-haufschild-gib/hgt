# GTA structural obstruction removal

Status: IN PROGRESS. No qualifying contribution established.

Objective: prove an unconditional structural theorem removing a hard obstruction in GTA; no improved bound, RH equivalence, or conditional receiver.

Constraints: Lean corpus only; no web or external novelty audit; no numerical experiments; no additional axioms or unproved analytic premises. Foreground targeted Lean checks, one owned build at a time; no umbrella builds; finish with `lake env lean` and formal lint.

Plan:
1. Read current GTA entry and inspect actual Lean source and corpus search coverage.
2. Identify exact source obstruction; iterate falsifiable conjectures and record failures.
3. Complete dependency-closed mathematical proof before implementing a survivor.
4. Formalize, audit axioms, wire umbrella, run targeted checks and lint, assess significance honestly.

Initial frontier: the map records transverse charge decay as RH-equivalent. Positive quartic charge, compact corrections, fixed-history convergence, bare Hankel positivity, and eventual paired symmetrization do not supply source control. Finite parity feedback has a square factorization, but signed cross-residue leakage remains open there.

Tool limitations: no `update_plan` or `multi_tool_use.parallel` exposed; plan tracked here and independent reads batched through `Promise.allSettled`. Serena supports Python only and rejects Lean symbol extraction; use `rg` and direct source reads for Lean.

Working tree contained unrelated edits at start, including the RHTower umbrella and several PaperThetaNative modules. Preserve those changes.

## Conjecture ledger

1. Constant-row quotient eliminates directed feedback. REJECTED as a route step: `ThetaQuotientParityFeedback` gives `P-1rᵀ`, but the sine/frequency factor in the squared operator need not preserve constants. A quotient of only one factor does not define a quotient of the coupled product.
2. Nonnegative mixed spectral residues. REJECTED: existing reference divergence plus exterior determinant positivity exposes alternating exterior residues; prior work already identified the mechanism. Do not rename this old conjecture or claim a new obstruction removal.
3. Remove the score kernel and its derivative chains. ALREADY IN CORPUS: `HedenmalmThetaDerivativeHistoryQuotient` constructs the closed history quotient, proves quasinilpotence of history and preserves every nonzero generalized root space and Xi multiplicity. This is not a new contribution.

Corpus searches run: `theta parity feedback`; deep `remove singular boundary directed rank one feedback positive sine cosine Gram source coupling`; `theta source arithmetic positivity oscillation determinant total positivity`; `theta quotient score generalized zero Jordan derivative chain`. All completed, `partial=false`; compiler applicability generally source-only and semantic-coverage warnings prevent treating search silence as exhaustive absence. Broad deep query had poor relevance; exact source searches and narrower followups used.

Next investigation: actual arithmetic/source identities on the history quotient and whether its spectral synthesis or boundary form admits a new unconditional structural reduction.

4. Literal prime-translation anomalies are bounded feedback vectors on the original source Hilbert space. FALSE by `HedenmalmThetaPrimeTranslationFixedFibre.integerAnomaly_not_memLp_fixedSource`: every integer shift at least two fails the reciprocal-theta L² admission test. Pointwise identities cannot be promoted to bounded operator identities there.
5. Weaken the theta weight to admit prime translations, then obtain a selector by quotienting derivative history. BRIDGE, not a qualifying result. `ThetaInterWeightTranslation` already constructs the literal maps with exact threshold `q' < q/p²`; `ThetaPrimeDeletionDerivativeHistory` places every admitted finite Euler deletion in derivative history. A coherent quotient construction would address domains but does not distinguish on-line and off-line roots. It must not be presented as transverse-energy production.
6. The derivative-history quotient has no additional quasinilpotent remainder (spectral synthesis). OPEN, not proved or refuted. Existing Riesz projections and Fourier functionals identify each nonzero block, but do not establish their collective completeness. A proof would need an actual weighted source division/closure theorem. Assuming completeness would introduce an unproved premise; even completeness alone would not orient nonreal eigenvalues.

## Honest assessment

No new structural producer or qualifying obstacle removal established. No new Lean theorem or conditional interface added. The investigations above either revisit existing corpus results, fail domain/invariance checks, or reach an unproved source-closure problem. Source-specific transverse control remains open in this work. This card is a failed-to-complete investigation record, not a completed contribution and not a retirement of GTA.

External literature and novelty were not checked, as requested. Source searches covered the corpus snapshot but generally did not provide current compiled metadata. The exact declarations used for the main rejections are undergoing a targeted Lean import/name/axiom audit; audit status will be recorded below.

## Further conjecture attacks

7. **Replace the divergent positive reference by its energy completion.**
   Rejected as an obstruction removal. `ThetaQuantileTwoEndedSelector.lean`
   explicitly constructs off-axis flat modes in ordinary L2. Restoring the
   original reciprocal-density domain admits them exactly at Xi zeros; it does
   not prove those zeros real. `HedenmalmThetaResolventMetricPlancherel.lean`
   also identifies determinant-weighted resolvent synthesis with the singular
   source metric. Such synthesis loses the orientation information at issue.

8. **Transfer global Meyer synthesis to the theta history quotient.**
   Open, not a theorem from this investigation. The actual corpus theorem
   `deningerMeyerXiSpectralSynthesis` in
   `DeningerMeyerGlobalXiSynthesis.lean` removes the invisible sector in the
   literal Meyer source using entire division, Gaussian regularization, and
   closed Poisson range. These are not a proof of closure of the span of theta
   derivatives in L2(k^-1 dx). No continuous comparison identifying these two
   closed ranges was established. Assuming that comparison would insert the
   missing premise. Individual theta Riesz-block identifications do not supply
   collective completeness.

9. **Use a coherent family of weaker theta weights for prime translation.**
   No qualifying survivor. The exact inter-weight translation criterion makes
   individual maps possible, but no source-side transverse cancellation follows.
   The existing critical rigging also admits literal prime shifts and anomalies;
   `HedenmalmThetaPrimeCriticalRiggingReflectionNoGo.lean` rules out contracting
   both reflected directions in that rigging. A new map or quotient alone would
   not meet the requested contribution standard.

Additional corpus searches used reference/Volterra renormalization, mean-periodic
spectral synthesis, Meyer/history comparison, and power-weighted source inverse
translation. Each returned `partial=false`; compiler coverage remained largely
source-only/pending or stale. Ranked hits were used as leads, not as proofs of
absence. No external search or novelty claim was made.

## Verification and outcome

- `lake --old env lean /tmp/gta-frontier-audit-20261016.lean`: **passed**.
  This checked existing compiled declarations, not a new theorem or a rebuild
  of their current source files. Names audited:
  `thetaQuotient_even_odd_stochastic_feedback`,
  `thetaParityFeedbackSquare_charpoly_pos`,
  `thetaDerivativeHistoryInverse_spectrum`,
  `finrank_genEigenspace_thetaDerivativeHistoryQuotientInverse`, and
  `integerAnomaly_not_memLp_fixedSource`.
  Their printed axiom sets were exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- `scripts/formal_tools.py lint`: **failed** on unrelated/concurrent
  `MobiusDivisor*` and `PaperTheta*` modules unreachable from the RHTower umbrella.
  Those files and their umbrella edits were not changed by this investigation.
- No Lean module was added or modified. No theorem was claimed as a new
  contribution. No full build, numerical mathematical experiment, heartbeat
  increase, commit, or push was performed.
- Owned scratch audit and search-result files were removed after their jobs
  exited. The research card is retained as the continuation checkpoint.

**Requested obstacle removal was not achieved.** GTA remains active; this card
is not a route retirement. The unresolved mathematical work is a source-specific
mechanism controlling transverse feedback, or a proved structural reduction
that materially eliminates part of that mechanism. Neither was established.
