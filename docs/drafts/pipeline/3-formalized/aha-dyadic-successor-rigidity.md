# Dyadic successor rigidity

- **ID:** AHA-SUCCESSOR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/arithmetic-harmonic-analysis-programme.md; additive resolution question
- **Statement:** The largest successor defect through integer cutoff `N` controls every observed gauge value with logarithmic loss.

## Exact inequality and fibre

Put `D_N(x)=max_{1≤m<N}|χ_x(m+1)−χ_x(m)|`, with empty maximum zero.
For `1≤n≤N` and `n≤2^k`,

`|χ_x(n)−1| ≤ 2k D_N(x)`.

Both sides use the actual gauge twist. The defect is an explicitly defined
finite maximum; there is no assumed cancellation or asymptotic estimate.

Moreover, `D_N(x)=0` if and only if `χ_x(p)=1` for every prime `p≤N`.
For two gauges, the same inequality reads
`|χ_x(n)−χ_y(n)|≤2k D_N(x−y)`; its zero fibre is exact agreement of
their prime values through `N`.

## Mechanism

Write `n=2m+ε`, `ε∈{0,1}`. Multiplicativity gives `χ(2m)=χ(2)χ(m)`.
The passage from `2m` to `n` costs at most one successor defect, and
`|χ(2)−1|≤D_N`. Thus each binary digit costs at most `2D_N`.
Induction on `k` gives the displayed bound. Consecutive telescoping would
lose `N`; multiplicative dilation reduces this to binary depth.

## Scope

This is finite-resolution rigidity, not a bound at every prime or an exponent
estimate. Primes above `N` remain invisible, as the exact fibre theorem records.
The logarithmic scale is consistent with the vertical twists `n^(it)` near
the identity. A sharp constant and that calibration require their own proofs.

## Lean

Module `ArithmeticHarmonicAnalysis/DyadicSuccessorRigidity.lean`;
namespace `GaloisForLFunctions.ArithmeticHarmonicAnalysis`:

- `norm_twist_sub_one_le_dyadic_radius`;
- `successorRadius_eq_zero_iff_prime`;
- `norm_twist_sub_twist_le_dyadic_radius`;
- `successorRadius_sub_eq_zero_iff_prime`.

The source passed `lake --old env lean`; transitive axiom checks contain
only `propext`, `Classical.choice`, `Quot.sound`.

The zero fibre follows by successor induction and prime factorization.
The two-point statements divide by the unit value `χ_y(n)`, preserving
the norm. Existing successor cocycles in `SignedSuccessorArithmetic`
characterize multiplicativity; this theorem supplies an explicit quantitative
inverse for finite complex-gauge observations. No priority claim is made
over classical stability results.
