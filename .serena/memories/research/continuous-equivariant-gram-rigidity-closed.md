# Continuous equivariant Gram-rigidity bridge closed

Date: 2026-07-29.

Paper theorem: for general n≥k, every continuous Hermitian-valued F:M_{n,k}(C)→Herm_k invariant under left U(n) and congruence-covariant under right GL(k,C) is F(X)=c X†X. Positivity iff c≥0; nonzero positivity gives c>0. This is classical/rediscovered bridge, not physics.

Exact physical 3×2 specialization is unconditionally Lean-proved in `formal/GaloisForLFunctions/HTGeometry/ContinuousEquivariantGramRigidity.lean`. Proof includes 2×2 centralizer, unitary completion, CFC polar factorization, symbolic quadratic determinant proof that full-rank events are dense, continuity extension, positivity iff and strict sign.

Audits: `lake env lean` pass; focused `lake build GaloisForLFunctions.HTGeometry.ContinuousEquivariantGramRigidity` pass; `scripts/formal_tools.py lint --check-generated` pass; capstone axiom audit only propext/Classical.choice/Quot.sound. Card promoted to `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/continuous-equivariant-gram-record-rigidity.md`.

F11 Causalization Law remains conjectural. Local Gram-map ambiguity is closed. Decisive open core: source-selected physical transfer into the Gram record, converse origin of every causal distinction, record composition into 3+1 continuum, and one exceptional connection yielding gravity + exact GSM + prediction.

Related: `mem:research/causalization-conservation-one-law`.