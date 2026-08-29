Completed and promoted Stage-2 card unitary-pair-twist-hardy-exponential-bound.

New Lean module:
formal/GaloisForLFunctions/HTGeometry/UnitaryPairTwistHardyBound.lean

Exact content:
- Banach-valued horizontal Hadamard three-lines: norm_le_rpow_abs_im_div_of_horizontal_threeLines.
- Ordered noncommutative products and reverse pointwise-inverse word, with both inverse identities.
- General O(n^2)-word/O(1/n)-factor theorem: norm_orderedWordProduct_le_of_quadratic_length.
- Exact increasing-pair set/cardinality and PairWord.length_le_of_pairMultiplicity = m * n.choose 2.
- Exact Alazzawi–Lechner shrinking tube and pair difference bound.
- Pair-word forward/inverse norm exponents m*kappa*(n-1)/(2*rho).
- pairWordHardyBase and gamma^n bounds.
- unitaryPairWord_hardy_exponential_bound and continuous-linear-operator specialization with LinearIsometryEquiv real-axis unitaries.
- exact central-boundary forward/inverse norms = 1.

Verification:
- Direct lake env lean passed clean.
- Targeted leaf build passed: 2761 jobs, 2.6s.
- Axiom audit of six capstones: only propext, Classical.choice, Quot.sound.
- Wired import into HTGeometry.lean; no umbrella build.
- git diff --check passed.
- Global lint only reported unrelated shared-worktree unreachable modules and existing large-file warnings.
- /tmp scratch and axiom files deleted.
Do not rebuild or re-audit this module.

Card moved to:
docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/06-integrable-qft-yang-baxter/unitary-pair-twist-hardy-exponential-bound.md
and updated with exact Lean coverage. Remaining corrective Brauer twist/O(N) conjecture gates are explicitly future research, not proved statements of this bridge card.

Continue recursive Stage-2 sweep. Lean corpus search only via scripts/formal_tools.py research; preserve concurrent changes.