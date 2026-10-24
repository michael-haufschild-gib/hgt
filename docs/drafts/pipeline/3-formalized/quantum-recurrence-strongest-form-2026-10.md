# Strongest current theorem of quantum recurrence

- **ID:** quantum-recurrence-strongest-form-2026-10
- **Stage:** 3-formalized
- **Type:** COMPLETED RESEARCH SYNTHESIS
- **Source:** User-requested full research and replacement of `../4-publication-ready/universal-quantum-recurrence-anatomy/`.
- **Statement:** Identify and write the strongest scientifically meaningful recurrence paper supported by the current Lean corpus; prove any new load-bearing results before admitting them to the manuscript.

## Goal

Replace the 24 August 2026 manuscript with a stronger, coherent paper grounded in current corpus results and checked against primary scientific literature through 24 October 2026. Strength means a more universal law, a consequential scientific question, resistance to hostile review, and defensible novelty and significance. Formalization alone earns no novelty credit.

## Requirements and gates

- [x] Read attached request and project instructions; inspect current worktree.
- [x] Audit all existing manuscript variants, proof traces, scope boundaries, and relevant newer corpus results through the required research tool.
- [x] Audit primary literature, ancestry, equivalent formulations, and stronger adjacent results.
- [x] State exact competing conjectures; attack falsity, circularity, rediscovery, and significance.
- [x] Complete dependency-closed paper proofs for any new claims before Lean work.
- [x] Formalize exact new results without unproved inputs, custom axioms, computation shortcuts, or raised limits; wire completed modules into their owning umbrella.
- [x] Check every admitted mathematical statement against actual Lean signatures and transitive axioms. Compile targeted source files using `lake --old env lean`, one process at a time. Never run `lake build` or compile an umbrella.
- [x] Produce replacement manuscript, current references, precise claim trace, proof audit, novelty audit, hostile review, and verified PDF.
- [x] Final requirement-by-requirement audit; do not claim novelty or publication readiness beyond evidence.

## Starting evidence

The previous canonical `main.tex` included `body.tex` and `references.tex`; dated 24 August 2026, titled *Persistent phase geometry of quantum recurrence*. Its headline was generic maximal projective spectral rank, two recurrence exponents, and all-order collision floors for finite open qudit paths. General supporting laws addressed contractions, relation hulls, weighted deadlines, observer graphs, finite-horizon instability, and countable pure point spectra. Earlier localization and observer manuscripts remain in the directory as historical variants.

Existing ledgers report past compilation but are not current verification. Some log entries use the now-forbidden `lake build`; those commands will not be repeated. Existing manuscripts claim no generic continuous-time first-return distribution and no finite-time equidistribution rate. A separate autonomous circuit-complexity programme was explicitly rejected by prior hostile review; its open claims must not be imported as recurrence conclusions.

Worktree already contains unrelated research edits in Goldbach, signed incidence, arithmetic orientation, square-root thresholds, and trans-threshold pair correlation. Preserve all such work.

## Research state

Corpus search findings and exact source dispositions are retained in the manuscript's corpus-disposition.md, claim-trace.md and novelty-audit.md. Temporary search outputs were removed after those records were complete. Selected new theorem and complete paper proof: `connected-network-all-observer-recurrence.md`. New Lean leaves extend real affine spectral escape and simultaneous observer laws to arbitrary connected graphs/hypergraphs with heterogeneous local dimensions. Canonical manuscript and all audit documents are complete.

### Stronger corpus results verified by reading source

- `HTGeometry/AllStateSpectralSupportRecurrenceLaw.lean`: one conull local-path event classifies **all** normalized pure states by exact support, with continuous-time fidelity-deficit exponent `max(s-2,0)/2`.
- `RHTower/FiniteQuantumObserverGraphExtremalityLaw.lean`: `ae_hasUniversalFiniteObserverFirstReturnLaw_simpleLocus` gives one conull event for **every** finite matrix observer family. Squared Hilbert--Schmidt exponent is `max(D-c(G)-1,0)/2`.
- `RHTower/StaticLocalAllObserverFirstReturnLaw.lean`: local path instantiation, pure-projector support specialization, and nuclear/trace-radius transfer. **Audit correction:** `HasUnitNoncommutingOnsiteEdgePresentation` introduces a noncommuting pair and compensates it in the remaining coordinates; it does not prove intrinsic noncommutation or nonintegrability of the selected dynamics. Do not use it for that claim.
- `RHTower/StationaryRecurrencePointSpectrumScalingLaw.lean`: every probability energy law has stationary fidelity distribution equal to the normalized atomic part's stationary law scaled by total atomic mass squared. Includes singular continuous spectra; no pointwise-decay conclusion.
- `RHTower/UniversalStationaryRecurrenceLaw.lean` and `StationaryRecurrenceSupportIntervalLaw.lean` strengthen scaling: for **every** probability energy law the stationary survival distribution has interval support `[lower,p²]`, so its upper support edge recovers total point-spectrum mass exactly. This is the strongest admitted statistical counterpart; direct source and transitive axiom checks passed. The August 28 card explicitly credits Wiener--Eberlein and treats priority as open; do not claim pure-point selection itself is new.
- `HTGeometry/UniversalRecurrenceOccupationConservationLaw.lean`: arbitrary finite spectra have occupation exponent equal to rational projective rank. Existing card correctly classifies this as dimension theory/rank--nullity, not standalone scientific novelty.
- `RHTower/CoherenceGraphVolumeLaw.lean` and `CoherenceGraphRecurrenceExponent.lean`: exact weighted forest bounds and discrete-time graph exponents. Existing card classifies abstract mechanism as a classical bridge.

### Decisive external-priority correction

Lee, Pilatowsky-Cameo, Choi, *Sustained growth of quantum circuit complexity in many-body Hamiltonian dynamics*, arXiv:2609.26885 (22 September; v2 28 September 2026), Proposition S2, proves all-order spectral nonresonance for generic local qubit Hamiltonians, including nearest-neighbour paths. Corollary S4 bounds **average** recurrence intervals for typical high-temperature product states. The August novelty claim that generic local all-order nonresonance is absent from the literature is obsolete. Primary sources: https://arxiv.org/abs/2609.26885 and https://arxiv.org/html/2609.26885v2 . Replacement must explicitly credit this result and distinguish exact small-tolerance first-return exponents, simultaneous observer quantifiers, and arbitrary local dimension.

Kotowski--Oszmaniec v3 (https://arxiv.org/html/2601.10409v3) asks for extensions to mixed states, observables, and physical local Hamiltonians. Gupta--Short (https://arxiv.org/html/2604.14995v1) already treats simultaneous pure/mixed-state uniform recurrence upper bounds. Merely adding mixed states is not a novelty claim.

### Current verification state

Initial scratch `/tmp/quantum_recurrence_frontier_audit.lean` failed before checking declarations: missing `QuantumAlg/Primitives/QNN/Algebras/OrthogonalDLA.ir`, despite an existing `.olean`. No existing olean rebuilt. Source import-path audit traces this through incidental Pauli/source-memory dependencies of `AllStateSpectralSupportRecurrenceLaw`; the observer, stationary-scaling, and occupation modules have no source dependency on this vendor module.

Reduced audit `/tmp/quantum_recurrence_core_audit.lean` completed successfully: the generic all-observer theorem, path capstone, nuclear-norm transfer, stationary atomic-scaling theorem, and occupation conservation theorem depend only on `propext`, `Classical.choice`, and `Quot.sound`.

`ConnectedGraphSpectralAffineEscape.lean` passed its direct source check and targeted olean creation with no warnings. Olean exists solely because `ConnectedNetworkAllObserverRecurrenceLaw.lean` imports it. The latter source also passed, including its final fidelity specialization. All compilations used `lake --old env lean` from `formal/`, one live process at a time.

## Log

- 2026-10-24 — Opened full replacement audit from current repository state.

### Replacement and current final checks

Both new graph/hypergraph capstones passed direct Lean source checks. Added exact normalized pure-state fidelity transfer (including sign and threshold conversion) and checked the updated capstone. Refactored PhysicalTwoQubitGraphSeed to remove its existing 1,000,000-heartbeat override; default-limit source check passed. UniversalStationaryRecurrenceLaw passed a current direct source check. Both new modules are wired into HTGeometry; other agents' imports preserved.

Canonical manuscript is now *Exact observable recurrence on connected quantum networks*. All nine final PDF pages were visually inspected; Tectonic completed without warnings. Current source includes corrected cutoff/clock conventions, a complete leaf-witness mechanism, and accurate scope boundaries. Human author retained; earlier AI author labels moved to disclosure. Final source-based axiom audit passed for all 31 declaration roots; only propext, Classical.choice and Quot.sound occur. All audit ledgers are complete. No claim of independent peer review or absolute priority is made.

Reproduction and claim documents: canonical directory README.md, claim-trace.md, proof-audit.md, novelty-audit.md, hostile-review.md, corpus-disposition.md, reference-audit.md; audit/check-axioms.sh and audit/declarations.txt.

### Final requirement audit

1. Universal laws: full connected graph/hypergraph coefficient spaces, arbitrary local dimensions, one conull event for every matrix observer; stationary law for every probability energy measure.
2. Scientific question: exact accuracy dependence is classified by visible phase connectivity, and limiting survival support identifies total atomic spectral weight. Limits and experimental interpretation are explicit.
3. Hostile review: counterexamples, rational/real nondegeneracy, physical locality, cutoff conventions, simultaneous quantifiers and stationary/pointwise distinctions are addressed.
4. Novelty: September 2026 prior work is credited; generic nonresonance is no longer advertised as new. The exact connected-network all-observer classification is the candidate contribution; priority remains provisional.
5. Proof integrity: admitted statements mapped to Lean, four targeted source files checked, 31 transitive roots audited, no unproved analytic assumptions or custom axioms, and prior seed heartbeat override removed.
6. Delivery: replacement TeX/PDF, complete review materials, formalized theorem card, umbrella imports, and reproducible audit retained. Temporary jobs and own scratch files cleaned; unrelated and historical work preserved.
