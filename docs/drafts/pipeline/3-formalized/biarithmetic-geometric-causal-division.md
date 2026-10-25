# Expanding causal division is an exact evaluation kernel

- **ID:** biarithmetic-geometric-causal-division
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [One-prime Fredholm phase](../1-in-progress/biarithmetic-one-prime-payment-fredholm-phase.md)
- **Statement:** For `0<b<1` and absolutely summable complex input `g`, the causal response at ratio `1/b` has finite square energy exactly when `Σ b^r g_r=0`. On this kernel it is the negative geometric future tail and has absolute sum at most `b/(1-b) Σ|g_r|`.

Square summability makes the causal response tend to zero. Multiplication
by `b^M` gives exactly the finite evaluation sum, whose limit therefore
vanishes. Conversely, zero evaluation supplies the future tail's initial
value, and its recurrence identifies it with the negative causal response.
The checked absolute-sum estimate then implies square summability.

Lean: `BiarithmeticGeometry/GeometricCausalDivision.lean`.
Audited declarations: `geometricEvaluation_eq_initial_add_tail`,
`geometricCausalResponse_eq_neg_futureTail`,
`geometricEvaluation_zero_of_summable_response`,
`summable_sq_geometricCausalResponse_iff`, and `tsum_norm_geometricCausalResponse_le`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/GeometricCausalDivision.lean`.
- [x] All five transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Default proof limits; umbrella import wired; umbrella not compiled.

This establishes the sequence-domain statement. Actual source-domain
identification and Fredholm indices remain separate obligations.
