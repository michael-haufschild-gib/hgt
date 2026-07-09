# All-`N` Hurwitz independence without the order-two exclusion

- **ID:** hurwitz-alln-order-two-closure
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Grade:** BRIDGE / formal execution
- **Source:** `formal/GaloisForLFunctions/Hurwitz/AllNHalfInteger.lean` · `AllNRelationClose.lean` · `MixedClose.lean`
- **Statement:** For `Re(s) > 1` and `s ∉ ℤ`, every eventual symmetric degree-`≤ 2` relation among all shifted Hurwitz model values has zero quadratic, linear, and constant coefficients, including the branch `2s ∈ ℤ`.

## Goal

Remove the obsolete hypothesis `2s ∉ ℤ` from the named all-`N` capstone.  The result exposes the actual parameter boundary: nonintegrality of `s` alone.

## Gates

- [x] 0 → 1  in-progress: the generic/order-two branch split and tail interface are explicit
- [x] 1 → 2  fully-proven: `all_coefficients_close_of_genuine_relation_poleRootInput` plus the proven harmonic pole-root provider
- [x] 2 → 3  formalized: `HurwitzAllNComplete.hurwitz_allN_independence_all_noninteger`; Hurwitz area build green; axioms `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready: not a standalone publication claim

## Proof

Convert `∀ k : ℤ, (k : ℂ) ≠ s` to the orientation expected by the relation-level theorem.  Apply `HurwitzAllNRelationClose.all_coefficients_close_of_genuine_relation_poleRootInput`; discharge its sole tail hypothesis with `HurwitzMixedClose.harmonicPoleRootInput_proved`.  The relation-level theorem already combines the generic monodromy split with the half-integer order-two split.

## Dual gate

- **Novel:** no.  The theorem is a direct composition of established in-tree results.
- **Significant:** yes as formal API consolidation: it removes a false boundary from the capstone and its `FullyProvenNewTargets` interface.
- **Disposition:** ships as formal execution, not as a claim of new mathematical knowledge.
