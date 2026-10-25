# Uniform logarithmic laws for Vaughan superpositions

- **ID:** uniform-logarithmic-laws-for-vaughan-superpositions
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** Every centered Vaughan packet has uniform logarithmic norm and energy errors, homogeneous in its absolute coefficient sum.

Let `0<ε<1/2`, `β=1-2ε`, `c=subHalfZetaCoeff ε`,
`H_U=Σ_(d≤U)μ(d)/d`, and `L(w)=Σ_i|w_i|`. The packet remainder is
exactly the weighted sum of the five smooth row remainders. For every `q∈ℕ`,
one nonnegative constant and one eventual horizon threshold work for every
cutoff pair and every real coefficient vector:

`‖P_wᶜ−c H_U H_V (w_3−w_2)n^(1−ε)‖_T ≤ C L(w) sqrt(T^β)/(log T)^q`.

The reverse triangle inequality gives the same bound for the absolute
difference between the packet norm and its explicit smooth norm. Equal
convolution coefficients remove the smooth term completely. The exact Gram
quadratic form also gives

`|‖P_wᶜ‖_T²/T^β−(c H_U H_V)²(w_3−w_2)²/β| ≤ C L(w)²/(log T)^q`.

Every centered row norm tends to zero after division by `sqrt(H(t)^β)` when
the horizon and cutoff product diverge independently. Arbitrary bounded moving
coefficient vectors preserve this zero normalized packet-norm limit. Finite-set
induction combines the component limits without assumptions on coefficient
convergence.

## Lean audit

Module: [UniformLogarithmicLawsForVaughanSuperpositions.lean](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformLogarithmicLawsForVaughanSuperpositions.lean).

- `pmPronicVaughanCentredPacket_sub_smooth_eq`
- `exists_uniform_pmPronicVaughanPacket_smoothRemainder_log_rate`
- `exists_uniform_pmPronicVaughanPacket_norm_smooth_log_rate`
- `exists_uniform_pmPronicVaughanPacket_log_rate_of_equal_convolution_coefficients`
- `exists_uniform_pmPronicVaughanPacket_energy_log_rate`
- `tendsto_pronicNorm_pmPronicVaughanCentredPiece_of_horizon_and_product`
- `tendsto_pronicNorm_pmPronicVaughanCentredPacket_of_horizon_and_product`

Corrected producing and final direct `lake --old env lean` checks passed.
All seven transitive axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. Required mathlib APIs were checked in scratch before use.
The BVI umbrella import is present; the owned scratch was removed. No limits
were raised. These logarithmic laws provide no fixed power gain or fixed strip;
full Q-I remains open.
