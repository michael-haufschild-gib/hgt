# Unshifted comb index at its own aperture

- **Stage:** 1-in-progress
- **Type:** CONJECTURE; full Lean draft, final check pending.
- **Target:** A94; Σ154/Σ165.

## Statement

For every integer `Q≥2`, put `a=log Q/2`. Eventually in `N`,

`negativeRank(a,0) ≤ robustCombIndex((N,QN],0) ≤ negativeRank(a,0)+weilNullity(a,0)`.

Thus the unshifted comb index eventually equals the exact restricted Weil
index whenever `weilNullity(a,0)=0`. The bracket has no RH or nonresonance
premise. B152's independent arithmetic sign producer remains open.

## Connection and proof

1. Full form-core density captures the native negative space in a finite
   smooth Gram. Realification preserves support and cannot decrease its index.
2. Translate that family into `(log 3,log(3Q))`. Sampling at `⌊N/3⌋`
   fits the original window `(N,QN]`; strict support margins remove the
   discarded samples. Finite Gram convergence gives the lower bound.
3. Padding into `(Q−1)R+1` complete blocks loses only `1/R` in ratio.
   Both Schur and packet approximation errors charge only block means.
   Their squared coefficient mass is exactly physical packet mass.
4. Simultaneous smoothing of Weil energy and mass transfers every negative
   comb subspace into a positively shifted form on any wider aperture.
5. The exact right-hand aperture jump equals nullity. A small positive
   energy shift then captures precisely the original rank plus nullity,
   proving the upper bound.

## Lean

Capstone draft:
`HodgeTheoryOfAFixedPart/TheUnshiftedCombIndexAtItsOwnAperture`:
`eventually_unshiftedCombIndex_between`,
`eventually_unshiftedCombIndex_eq_of_nullity_zero`.

Passed bridges: exact aperture jump and positive-energy stability;
finite operator Grams; smooth form-core index capture; smooth and bounded
mass-shifted packet Grams; exact nested-packet physical mass; tight block
transfer; unconditional aperture upper bound.

Remaining checks: smooth zero-Gram identification, support-preserving
realification, original-ratio sampling, and capstone.
Support modules are one contribution with this theorem.
