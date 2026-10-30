# The matched prime form has one positive direction uniformly in the sieve

- **ID:** MATCHED-PRIME-SIEVE-HODGE
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [O2](../1-in-progress/weil-positivity-five-structural-mechanisms.md)
- **Statement:** For `0 < η < 2 log 2`, eventually in `N`, the matched prime form `P_N − (log N − γ − η)I` is hyperbolic on every finite family of vectors. On the full class partition of any finite prime sieve it has exactly one positive direction. The horizon is independent of the sieve and its size.

## Proof [PROVED HERE]

Put `ε = (2 log 2 − η)/2 > 0`. The existing all-vector spectral gap gives, for every vector orthogonal to `n⁻¹ᐟ²`,

`P_N(x) − (log N − γ − η)‖x‖² ≤ −ε‖x‖²`

beyond a horizon depending only on `η`. Pulling this hyperplane back through any finite synthesis map proves hyperbolicity of its Gram matrix.

The existing pole estimate with error `η/2` makes the matched form strictly positive on the truncated pole, whose squared norm is at least one for `N ≥ 1`. Unique supported/coprime factorization partitions the positive integers into the classes of any finite sieve. Summing all class pole vectors of supported order at most `N` equals the truncated pole on `[1,N]`. Thus the full finite-sieve class Gram has a positive vector as well as at most one positive direction.

Dependencies: `eventually_atomicWeilForm_le_two_log_two`, `eventually_atomicWeilForm_truncPole_ge`, `exists_sieveFactorization`, `sieveClassPole_mul_eq_zero`, and the hyperplane criterion for real symmetric forms. No analytic input is added.

## Scope

This settles the finite-sieve first test A6 using a stronger existing all-vector theorem. It does not identify this matched prime Gram with the complete prime/Gamma/polar Weil form, and does not prove O2's global index formula. Fixed depth truncations can omit the pole; only an upper bound on their positive index follows.

## Verification

- [x] Dependency-closed paper proof.
- [x] Lean module and axiom audit.

Module: `RenormalizedArithmeticPotentialTheory/Signature/TheMatchedPrimeFormHasOnePositiveDirection.lean`.

- `eventually_isHyperbolic_matchedPrimeProfileGram`: one horizon for every finite family.
- `eventually_sieveHodgeGram_one_positive_direction`: at most one positive direction and a strictly positive pole on every full sieve partition.
- Both declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The module passed `lake --old env lean` and is imported by its programme umbrella.
