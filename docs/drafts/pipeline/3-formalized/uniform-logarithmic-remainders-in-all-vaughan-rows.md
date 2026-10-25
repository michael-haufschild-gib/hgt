# Uniform logarithmic remainders in all Vaughan rows

- **ID:** uniform-logarithmic-remainders-in-all-vaughan-rows
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** All five actual Vaughan rows, after centering and removing their common smooth direction, have every logarithmic pronic norm saving uniformly in both cutoffs.

## Exact result

Write `H_U=Σ_(a≤U) μ(a)/a`, `K=c_ε H_U H_V`,
`s=(0,0,-1,1,0)`, and
`R_i(n)=p_iᶜ(n)-K s_i n^(1-ε)`.
For every `0<ε<1/2` and integer `q≥0`, there is `C≥0` and one
eventual horizon threshold such that, for every `U,V` and all five rows,

`‖R_i‖_T ≤ C sqrt(T^(1-2ε))/(log T)^q`.

The convolution remainder is exactly
`R_2=-H_U H_V subHalfRemainder_ε-A_(r,ε)`, where `r` is the actual
convolution coefficient fluctuation. The unit-pattern correction has bounded
pronic norm, and the actual fluctuation has the checked uniform logarithmic
norm bounds. The opposite smooth terms cancel in the five-row sum:
`Σ_i R_i=I_ε`. Thus the both-large row is controlled by the other four
remainders and the actual Bézout interior. All analytic inputs are discharged.

## Lean audit

Module: [UniformLogarithmicRemaindersInAllVaughanRows.lean](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformLogarithmicRemaindersInAllVaughanRows.lean).

Six public theorems:

- `pronicNorm_subHalfRemainder_le`
- `pmPronicVaughanSmoothRemainder_smallSmall_eq`
- `exists_uniform_pmPronicVaughanSmoothRemainder_smallSmall_log_rate`
- `sum_pmPronicVaughanSmoothRemainder`
- `pronicNorm_pmPronicVaughanSmoothRemainder_large_le`
- `exists_uniform_pmPronicVaughanSmoothRemainder_log_rate`

Corrected scratch, producing, and final direct `lake --old env lean` checks
passed. Every transitive axiom report contains only `propext`,
`Classical.choice`, and `Quot.sound`. The module is wired into the BVI
umbrella; its scratch file was removed. No limits were raised.

This strengthens the positive survivor of the absolute atom-budget obstruction:
the actual smooth-subtracted rows save every logarithm despite that absolute
budget's exact trivial power. It supplies no fixed power gain or bounded
small-damping receiver. Full Q-I and the complete uniform Gram verification
remain open.
