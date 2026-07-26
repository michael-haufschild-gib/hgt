# Xi Taylor primitive/product-fibre completion law

- **ID:** xi-taylor-primitive-product-fiber-completion-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** whole-corpus closure of `XiCTaylorThetaTailPrimitiveRayGlobalReassembly` and `XiCTaylorThetaTailProductFiberFiniteCoreGlobalBridge`
- **Statement:** The global sum of completion-scaled product-fibre currents equals four times the squared radial scale times the complete coprime-direction reflected seam sum, minus the single exact completion norm-square term.

## Goal

Identify the exact interaction between multiplicative product-fibre regrouping, primitive-direction
radial reassembly, and polynomial completion.

## Gates

- [x] 0 → 1  in-progress: shared finite-core current identified from Lean theorem conclusions
- [x] 1 → 2  fully-proven: exact substitution proof closed
- [ ] 2 → 3  formalized: exact Lean theorem and final formal gates pending
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

The product-fibre bridge states
`Σ completed = 16‖z‖⁴ J - 32‖z‖² Im(z) ‖P(z)‖²`.
The primitive-direction theorem states `J = (1/4) Σ primitiveGlobalJoint`.  Substitute the second
identity into the first and normalize the scalar coefficient.  Absolute convergence and both
reindexings are already proved by the two source theorems; no interchange remains.

## Audit

- **[CORPUS]:** exact completion/product-fibre bridge
- **[CORPUS]:** exact coprime-direction global reflected-ray reassembly
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; neither module connects the two arithmetic decompositions
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`

## Log

- 2026-07-22 — theorem-conclusion closure found and exact paper proof completed
