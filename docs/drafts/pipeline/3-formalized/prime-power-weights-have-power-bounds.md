# Prime-power weights have power bounds

- **ID:** prime-power-weights-have-power-bounds
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke Mertens programme](../1-in-progress/hecke-character-mertens-via-ideal-hyperbola.md)
- **Lean:** `GaloisForLFunctions/ArtinMertens/PrimePowerWeightsHavePowerBounds.lean`
- **Statement:** For every number field and `0<sigma<1`, there is `B>=0` such that `sum_(N(p)^k<=N) log N(p)*(N(p)^k)^(-sigma) <= B*N^(1-sigma)` for every integer `N>=1`.

## Proof

The existing `sum_log_mul_rpow_neg_le` compares the weighted prime-power
sum with `D*sum_(1<=n<=N) n^(-sigma)`, using the actual prime-power
Chebyshev bound. The existing integer power-sum estimate bounds the
latter sum by `(2+1/(1-sigma))*N^(1-sigma)` for `N>=2`.
The cutoff `N=1` follows directly. This exposes the reusable quantitative
bound `exists_sum_primePowersLe_log_rpow_le` without duplicating either
Abel summation or prime-power regrouping.

## Audit

The complete scratch passes without warnings. The new theorem and the
existing `exists_abs_primeMertens_sub_log_le` both have transitive axiom
sets `[propext, Classical.choice, Quot.sound]`.
The module is wired into the ArtinMertens umbrella. Its final direct
source audit is pending. The Hecke Mertens consumer is written.
