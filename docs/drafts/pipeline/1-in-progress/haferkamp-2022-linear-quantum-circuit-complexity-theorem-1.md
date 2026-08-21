# Haferkamp et al. 2022: probability-one linear unitary-complexity growth

- **ID:** haferkamp-2022-linear-quantum-circuit-complexity-theorem-1
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** Attached `s41567-022-01539-6.pdf`, Theorem 1; attached supplement `41567_2022_1539_MOESM1_ESM.pdf`, Appendices A--B
- **Statement:** For every positive qubit count `n`, every fixed `n`-qubit architecture obtained by concatenating `T` blocks of at most `L` two-qubit gates, each with a backwards light cone, and independent Haar-random `SU(4)` gate choices, the implemented unitary has exact two-qubit circuit complexity at least `R / (9 L) - n / 3` almost surely throughout the paper's pre-saturation range `T < 4^n - 1`.

## Goal

Construct the exact theorem in Lean with its paper definitions of architecture, backwards light cone, contraction map, accessible dimension, Haar-random gates, and exact circuit complexity; prove it without axioms, placeholders, or hypotheses not present in the paper.

## Gates

- [x] 0 -> 1 in-progress: source-pure statement extracted; internal-corpus and literature audit completed; exact formal surface absent.
- [ ] 1 -> 2 fully-proven: complete dependency-closed paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, targeted `lake build` green, formal lint and axiom audit pass.
- [ ] 3 -> 4 publication-ready: standalone paper (theorem + proof + Lean certificate + source audit).

## Internal and external frontier

- `[LITERATURE]` Haferkamp--Faist--Kothakonda--Eisert--Yunger Halpern, *Linear growth of quantum circuit complexity*, Nature Physics 18 (2022), 528--532, proves the stated random-circuit result by accessible dimension, real algebraic geometry, and a Clifford induction.
- `[LOCAL-RESEARCH]` `docs/drafts/pipeline/2-fully-proven/algebraic-two-local-instant-exact-complexity.md` develops a different autonomous exact-state-complexity theorem. Its separating-polynomial route deliberately avoids semialgebraic geometry and does not formalize this result.
- `[CORPUS]` `formal` has related finite-unitary Haar and circuit-complexity interfaces, but `formal_tools.py research` found no exact formalization of the contraction map, accessible dimension, backwards-light-cone induction, low-rank locus, or Theorem 1.

## Paper-proof audit

The paper's route is: low-rank locus is a proper algebraic measure-zero set -> maximal rank equals accessible dimension -> Clifford light-cone induction supplies rank at least `T` -> a parameter-count upper bound gives every shorter architecture smaller accessible dimension -> constant-rank local normal form and compactness make its image probability zero.

`[OPEN CORE]` The attached paper cites, rather than proves, the needed real-algebraic/semialgebraic foundation: Tarski--Seidenberg, finite smooth stratification with correct dimension, image-dimension monotonicity, and the measure-zero conclusion for a lower-dimensional image. These must be stated at the exact strength required, paper-proved from first principles or audited primary sources, before Lean infrastructure begins.

## Hostile verdict

`SURVIVES PRELIMINARY ATTACK`: the theorem is a published exact result and the proof mechanism is non-circular. The displayed prose says “until ... `T >= 4^n - 1`”; Appendix B's Lemma 4 proves the operative range `T < 4^n - 1`, which is the precise range recorded here. Formalization must preserve the latter, proof-supported inequality rather than encode the ambiguous typography.

## Approach

1. Dependency-close Appendix A and its measure/dimension consequences on paper.
2. Define finite qubit architectures and prove the Clifford backwards-light-cone rank induction.
3. Prove the parameter bound, constant-rank/null-image bridge, and exact Haar almost-everywhere lower bound.
4. Formalize each closed layer in narrow modules and wire only completed modules into `HTGeometry`.

## Verified alternate bridge

The main probability conclusion need not wait for a full implementation of Tarski--Seidenberg.  Mathlib's verified
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` proves the equal-dimensional Sard lemma for a map
whose derivative is singular everywhere.  A paper-proof route is therefore to construct finite smooth gauge charts for each
short architecture in which its contraction map factors through fewer than `rmax` coordinates, pad its local output map to an
equal-dimensional map, and apply that theorem.  Finite chart covers and the product with the deep map's kernel coordinates
then yield the null preimage needed for Theorem 1.  This replaces only the semialgebraic-image use in the main proof: the
attached supplement's Theorems 2--3 remain independent required formalizations.

## Log

- 2026-08-21 -- Created in 1-in-progress after attached-source extraction, visual verification, custom corpus search, prior-research audit, and primary-source audit.
- 2026-08-21 -- Closed the gate-law prerequisite in `formal/GaloisForLFunctions/HTGeometry/FiniteSpecialUnitaryHaarMeasure.lean`: finite-dimensional `SU(d)` is a compact topological group with normalized Haar probability `finiteSpecialUnitaryHaar`; target build, project lint, and `#print axioms` audits passed. Imported into `GaloisForLFunctions/HTGeometry.lean` without building that umbrella.
- 2026-08-21 -- Closed independent gate sampling in `formal/GaloisForLFunctions/HTGeometry/FiniteSpecialUnitaryHaarProduct.lean`: `Measure.pi` of the normalized `SU(d)` Haar factors is a probability measure, exactly expressing the fixed-architecture independent-gate law. Target build and axiom audit passed; imported into the umbrella without building it.
- 2026-08-21 -- Closed the paper-specific finite architecture core in `formal/GaloisForLFunctions/HTGeometry/HaferkampTwoQubitArchitecture.lean`: ordered distinct two-qubit locations, a verified `SU(4)`-to-register unitary lift, time-ordered contraction, and normalized independent gate law. Target build and `#print axioms` audit passed; imported into the umbrella without building it.
- 2026-08-21 -- Closed exact circuit-complexity definitions and their universal witness/lower-bound equivalence in `formal/GaloisForLFunctions/HTGeometry/HaferkampExactCircuitComplexity.lean`. Target build and `#print axioms` audit passed; imported into the umbrella without building it.
- 2026-08-21 -- Closed paper-specific Pauli labels and linear fresh-direction selection in `formal/GaloisForLFunctions/HTGeometry/HaferkampPauliDirectionSelection.lean`: the literal nonidentity Pauli set has cardinality `4^n - 1`, and every proper finite span omits a selected label. Target build and axiom audit passed.
- 2026-08-21 -- Closed scalar phase normalization, exact two-qubit Clifford seed conjugations, local nonidentity-Pauli transport, and their full-register lift in `HaferkampSpecialUnitaryPhase.lean`, `HaferkampTwoQubitCliffordSeeds.lean`, `HaferkampTwoQubitPauliTransport.lean`, and `HaferkampLiftedPauliTransport.lean`. Each target build and axiom audit passed; all modules are wired into `HTGeometry`.
- 2026-08-21 -- Closed ordered edge-list architectures and certified single-path Pauli transport in `HaferkampEdgeListArchitecture.lean`, `HaferkampPauliMergeSchedule.lean`, and `HaferkampQubitPathTransport.lean`. A schedule’s gates are exact lifted `SU(4)` transports and its literal edge word is retained. Target builds and axiom audits passed.
- 2026-08-21 -- Closed `HaferkampPauliMergeWord.lean`: an arbitrary ordered word of distinct two-qubit locations emits a certified schedule only at locally nonidentity pairs, with emitted edge word an ordered sublist of the supplied word. Target build and axiom audit passed; module wired into `HTGeometry`.
- 2026-08-21 -- Closed the Appendix-B backwards-light-cone Pauli transport in `HaferkampBackwardLightCone.lean`. For every nonidentity finite Pauli label and every BLC block on `n > 1` qubits, a certified schedule embedded in that block maps the label to one with `Z` at its root. Non-root support uses its path; root-only support uses a path’s final edge. Target build and axiom audit passed. This corrects the local merge invariant to Eq. (B7): either endpoint, not only the nominal source, may carry nonidentity support.
- 2026-08-21 -- Closed the algebraic Jacobian of an ordered ambient matrix word in `HaferkampAmbientProductDerivative.lean`. Its exact one-coordinate formula is prefix--variation--suffix, and it specializes definitionally to the fixed-architecture contraction after coercion. This is the rank-induction’s matrix-calculus core; the still-open next bridge is its identification with derivatives in explicit finite `SU(4)` charts. Target build and axiom audit passed; module wired into `HTGeometry`.
- 2026-08-21 -- Corrected the fixed-architecture contraction order: list order is physical execution order, so its matrix contraction is the reverse list product. Updated edge-list and ambient-Jacobian formulas consistently; targeted builds and axiom audits passed. The prior forward product placed the first acted gate on the wrong side and could not realize a source-to-root merge schedule.
- 2026-08-21 -- Closed full BLC gate-word realization in `HaferkampSublistGateEmbedding.lean`, `HaferkampTotalTwoQubitLift.lean`, `HaferkampPauliMergeGateWord.lean`, and `HaferkampBlockPauliTransport.lean`. A certified schedule now exposes aligned local `SU(4)` gates; any omitted block locations receive identity gates; the full block’s reverse-chronological contraction exactly transports every nonidentity Pauli direction to `Z` on its root. Target builds and axiom audits passed; all modules wired into `HTGeometry`.
- 2026-08-21 -- Closed the missing Clifford invariant in `HaferkampTwoQubitCliffordAction.lean` and `HaferkampLiftedCliffordAction.lean`: H, HS, SWAP, and CNOT have compact symbolic Boolean-Pauli action tables; the explicit local transport and determinant-one representative normalize every local Pauli label; this lifts to arbitrary finite registers and is preserved by each schedule and completed BLC gate word. Target builds and `#print axioms` audits passed, with only `propext`, `Classical.choice`, and `Quot.sound`; both modules are wired into `HTGeometry`.
- 2026-08-21 -- Extended `HaferkampLiftedCliffordAction.lean` with trace-preserving finite-register unitary conjugation and the resulting support invariant: an exact Pauli-Clifford transport cannot map a nonidentity Pauli label to identity. This supplies the nonidentity condition required when each rank-induction block is constructed after a prefix Clifford transport. Target build and axiom audit passed.
- 2026-08-21 -- Closed two algebraic rank-induction bridges: `reverse_unitary_conjugation_of_smul_finitePauli` strips a prefix unitary from a nonzero Clifford Pauli transport, and `linearIndependent_smul_of_ne_zero` preserves an independent finite family under its nonzero scalar phases. Target builds and axiom audits passed. Next core is the finite block-prefix induction that chooses an independent nonidentity Pauli family, transports each through the current prefix, builds its BLC block, and identifies the resulting terminal-gate directions with the ambient-product derivative.
- 2026-08-21 -- Closed the finite fresh-family and reverse-product rank bridge in `HaferkampBlockRankInduction.lean`: the exact threshold `T < 4^n - 1` selects an injective independent nonidentity Pauli family; a reverse-time unitary word factors at each coordinate; and any prefix-conjugated Pauli identities give linearly independent ambient coordinate outputs after total-unitary stripping. The proofs use explicit list splitting and unitary cancellation, remain under the default heartbeat, and have passed a source check. Next core is recursive BLC-block assembly plus its embedding into the actual `SU(4)` coordinate derivative.
- 2026-08-21 -- Repaired and closed the full single-block Pauli-collapse layer. `HaferkampTemporalMergePlan.lean` formalizes the paper’s coalescing-path condition as a time-compatible rooted merge plan, proves by ordered induction that all non-root support is cleared while nonidentity support survives, proves the terminal label is exactly root-only `Z`, and realizes that execution as an embedded certified local `SU(4)` schedule. `BackwardsLightCone` now carries this structural merge-plan certificate; `HaferkampLiftedCliffordAction.lean` consequently proves a full block maps every nonidentity Pauli matrix to the literal root-only `Z` through local and global Pauli Cliffords. Target builds, axiom audits, `git diff --check`, and formal lint passed; no heartbeat limit was raised.
- 2026-08-21 -- Added `HaferkampTerminalPauliCoordinate.lean`: an arbitrary ambient two-qubit lift respects right gate multiplication; lifted `I ⊗ Z` is the literal root-only finite Pauli matrix; hence the terminal local `I ⊗ Z` variation equals global root-Pauli multiplication immediately after its root-targeting gate. The temporal plan also now names the final root-targeting merge and proves it is locally nontrivial for every nonidentity input. Target builds and axiom audits passed under default heartbeat. Remaining rank core: retain this terminal edge when embedding the certified schedule into the complete physical block word, then compose block prefixes and the true `SU(4)` chart derivative.
