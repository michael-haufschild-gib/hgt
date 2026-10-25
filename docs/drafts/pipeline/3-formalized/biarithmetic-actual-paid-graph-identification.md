# The complete actual-source graph realizes the paid ideal

- **ID:** biarithmetic-actual-paid-graph-identification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Payment graph norm](../1-in-progress/biarithmetic-payment-graph-norm.md)
- **Statement:** For every real arithmetic source with absolutely convergent mean, the Wiener image of its complete cofactor graph is exactly its actual complex paid ideal. Every paid kernel has a unique square-summable graph output.

The graph uses the actual centered prefix of the source. Its complex
square energy splits into real and imaginary energies. The checked
source convolution identity and the uniformly paid critical-Wiener
mean correction identify those two energy conditions with the two
components of actual complex payment. Injectivity of the graph input
map gives uniqueness of the output.

Lean: `BiarithmeticGeometry/PaidGraphIdentification.lean`.
Audited declarations: `mem_range_actualSourceCofactorGraphInput_iff` and
`paidIdeal_iff_existsUnique_cofactorGraph`.

- [x] Direct repository check with `lake --old env lean`.
- [x] Umbrella import wired; umbrella not compiled.
- [x] Both transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.

The complete graph norm is available from `CofactorGraphDomain`.
Its Wiener ideal action and the criterion for ambient closedness remain
separate verification obligations.
