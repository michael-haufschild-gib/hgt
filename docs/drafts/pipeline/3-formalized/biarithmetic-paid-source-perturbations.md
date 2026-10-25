# Paid perturbations preserve the complete repairing ideal

- **ID:** biarithmetic-paid-source-perturbations
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** Adding any paid source with absolutely convergent mean leaves the full complex repairing ideal unchanged. In particular, adding a critical Wiener source does so. Nonzero scalar multiplication also preserves this ideal.

## Proof

Let `c,d` have absolutely convergent means and suppose `d` is paid. Every critical Wiener
kernel `k` sends `d` to a paid source by the proved convolution stability theorem. Linearity
of convolution and of the centered prefix then shows that `k*(c+d)` is paid exactly when
`k*c` is paid: add `k*d` in one direction and subtract it in the other. Apply this separately
to the real and imaginary kernel components. Thus `P(c+d)=P(c)`, with equality of the
actual ideals, not merely their closures or hulls.

For a critical Wiener source `d`, the corpus uniformly bounds its centered prefix norm by
`(sqrt(2)+1) sum_n |d(n)| n^(-1/2)`. Squaring gives payment directly. This discharges the
special case used to remove the secondary golden tower; no payment hypothesis is added
to that application. Combining with the existing nonzero scalar law gives
`P(t*c+d)=P(c)` whenever `t` is nonzero and `d` is critical Wiener.

## Scope

This is the elementary linear stability underlying the golden-source reduction. It does
not prove that its primary tower is paid, identify its ideal, or assert that payment is
closed in the Wiener norm. Those are separate analytic questions.

- [x] Dependency-closed paper argument.
- [x] Lean proof and direct repository check of `PaidSourcePerturbations.lean`; umbrella import.
- [x] Five public declarations transitively audited: only `propext`, `Classical.choice`, and `Quot.sound`.

Lean declarations: `receiverBounded_of_criticalWiener`, `mem_paidIdeal_of_receiverBounded`,
`paidIdeal_add_paid`, `paidIdeal_add_criticalWiener`, and
`paidIdeal_smul_add_criticalWiener`, all in
`GaloisForLFunctions.BiarithmeticGeometry.PaidSourcePerturbations`.
