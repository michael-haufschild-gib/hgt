# Xi Taylor primitive/product-fibre completion law

- **ID:** xi-taylor-primitive-product-fiber-completion-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** whole-corpus closure of `XiCTaylorThetaTailPrimitiveRayGlobalReassembly` and `XiCTaylorThetaTailProductFiberFiniteCoreGlobalBridge`
- **Statement:** The global sum of completion-scaled product-fibre currents equals four times the squared radial scale times the complete coprime-direction reflected seam sum, minus the single exact completion norm-square term.

## Goal

Identify the exact interaction between multiplicative product-fibre regrouping, primitive-direction
radial reassembly, and polynomial completion.

## Gates

- [x] 0 → 1  in-progress: shared finite-core current identified from Lean theorem conclusions
- [x] 1 → 2  fully-proven: exact substitution proof closed
- [x] 2 → 3  formalized: `tsum_xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent_eq_primitiveDirection`
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

## Lean certificate

File: `formal/GaloisForLFunctions/RHTower/XiCTaylorPrimitiveProductFiberCompletion.lean`
(imported by `GaloisForLFunctions.RHTower`).

```lean
theorem RHTower.tsum_xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent_eq_primitiveDirection
    (d : ℕ) (z : ℂ) :
    (∑' k : ℕ, xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent d z k) =
      4 * Complex.normSq z ^ 2 *
          (∑' q : ThetaCuspPrimitiveDirection,
            ∫ r in Ici (thetaCuspPrimitiveRayRadialLog q.1.1 q.1.2 0 0),
              (8 * Real.exp (-(Real.log q.1.1 + Real.log q.1.2) / 2)) *
              thetaCuspPrimitiveRayJointSeamIntegrand d z r
                (-Real.log q.1.1) (-Real.log q.1.2)) -
        32 * Complex.normSq z * z.im *
          Complex.normSq ((xiCTaylorThetaTailCorePolynomial d).eval z)
```

The proof is the exact substitution of the card's Approach and nothing else: rewrite with
`tsum_xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent_eq`
(`XiCTaylorThetaTailProductFiberFiniteCoreGlobalBridge`, giving
`Σ completed = 16‖z‖⁴ J − 32‖z‖² Im z ‖P(z)‖²`), then with
`xiCTaylorThetaTailCore_current_eq_tsum_primitiveDirectionGlobalJoint`
(`XiCTaylorThetaTailPrimitiveRayGlobalReassembly`, giving `J = (1/4) Σ primitiveGlobalJoint`), and
close by `ring` — `16 · (1/4) = 4`.  Both source theorems carry their own absolute convergence, so
no interchange or new summability is introduced.

`#print axioms` returns exactly `propext, Classical.choice, Quot.sound`; the targeted module build
is green.

## Log

- 2026-07-22 — theorem-conclusion closure found and exact paper proof completed
- 2026-07-26 — formalized as the exact substitution of the two source theorems; card moved to
  `3-formalized`
