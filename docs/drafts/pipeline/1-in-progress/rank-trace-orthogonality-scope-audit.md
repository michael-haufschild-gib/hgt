# Rank–trace sharpness: abstract frames versus arithmetic evaluations

- **ID:** rank-trace-orthogonality-scope-audit
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review of `rankTrace_tight_at_two_thirds`
- **Statement:** Exact coalescence of abstract reflection blocks persists for arbitrary real
  evaluation families; the orthogonal extremizer does not establish sharpness for zeta evaluations.

## Goal
Separate validity of finite block identities from realization by the prescribed arithmetic
evaluation family. Preserve the valid rank–trace inequality and repair overbroad barrier claims.

## Gates
- [x] 0 → 1: inspected constructors, consumers, and actual `evalVec`/`blockData` definitions.
- [ ] 1 → 2: dependency-closed paper proof of arbitrary-frame coalescence and explicit example.
- [ ] 2 → 3: Lean compilation and transitive `#print axioms` audit.

## Findings
`ZeroBlockData` stores multiplicities, vectors, and a conjugation-compatible involution. It has no
orthogonality field and no arithmetic-realization field. `coalescedPairBlockData` chooses coordinate
vectors explicitly; reflected labels share a vector. `rankTrace_tight_at_two_thirds` proves exact
equalities for these chosen data, with no orthogonality hypothesis about genuine zeros.

The universal functional barrier quantifies over **all** normalized `ZeroBlockData` at a fixed
grid. A functional valid only for actual zeta evaluations need not satisfy that premise.
`Zeta23.ZeroSide.ZeroBlockData.mult_two` uses individual norm bounds, not pairwise orthogonality.
The imported density theorem is proved through `Zeta23.thmB₀_mult_cumulative`, independently of
these extremal constructors. Its broader analytic proof is outside this scope review.

## Approach and paper proof
For arbitrary real families `u : α → d → ℝ`, `w : β → d → ℝ`, compare:

1. fixed labels `α ⊕ β`, with multiplicities one and two;
2. fixed labels `α` and swapped pairs `β ⊕ β`, all multiplicities one, each pair assigned `w b`.

Reality gives conjugation compatibility. Both matrices are exactly
`Σ a, uₐuₐᵀ + 2 Σ b, w_bw_bᵀ`, with total count `#α + 2#β`. Fixed-label counts are respectively
`#α + 2#β` and `#α`. No orthogonality or normalization is used.

For `u₀=(1,0)`, `u₁=(3/5,4/5)`, `w=(0,1)`, all vectors have unit norm and
`⟨u₀,u₁⟩=3/5`. Both matrices are `[[34,12],[12,66]]/25`, with trace `4` and squared
Frobenius norm `232/25`. Counts differ (`4` versus `2`); correlations remain in the second moment.

## No-go closure
- **Rejected inference:** abstract orthogonal extremizers imply an arithmetic sharpness barrier
  for the prescribed zeta evaluation family. No realization theorem establishes that transfer.
- **Strongest positive survivor:** equality of the full Gram matrices and total counts, with
  different fixed-label counts, for every real family, including nonorthogonal normalized families.
- **New insight:** coalescence indistinguishability is independent of orthogonality; the specific
  trace/Frobenius extremal values are a separate property of the coordinate frame.
- **Status:** elementary finite-sum proof above; Lean implementation and axiom audit pending.

## Log
- 2026-10-28 — audit opened; retain finite model theorem, correct arithmetic scope, formalize survivor.
