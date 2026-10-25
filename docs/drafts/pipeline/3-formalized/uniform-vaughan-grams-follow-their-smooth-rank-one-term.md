# Uniform Vaughan Grams follow their smooth rank-one term

- **ID:** uniform-vaughan-grams-follow-their-smooth-rank-one-term
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../2-fully-proven/uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** Below half damping, the complete centered Vaughan Gram has every logarithmic error rate around its smooth rank-one term, uniformly over both cutoffs.

For `0<ε<1/2`, put `β=1-2ε`, `c=subHalfZetaCoeff ε`,
`H_U=Σ_(d≤U)μ(d)/d`, and `s=(0,0,-1,1,0)`. For every `q∈ℕ`,
one `C≥0` and one eventual horizon threshold work for all `U,V,i,j`:

`|G^c_ij(T;U,V)−(c H_U H_V)² s_i s_j T^β/β| ≤ C T^β/(log T)^q`.

Division by `T^β` gives the corresponding common normalized error.
The proof expands each row into its smooth term and checked logarithmic
remainder. Finite weighted Cauchy–Schwarz bounds the three residual pairings;
the bounded smooth-energy error is absorbed by the same logarithmic rate.

For any divergent horizon schedule `H(t)` and arbitrary cutoff schedules,
the normalized Gram minus its moving smooth term tends to zero. If the
cutoff product also diverges, every normalized Gram entry tends to zero.
Horizon and cutoff-product divergence require no relation to each other.

## Lean audit

Module: [UniformVaughanGramsFollowTheirSmoothRankOneTerm.lean](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformVaughanGramsFollowTheirSmoothRankOneTerm.lean).

- `exists_uniform_pmPronicVaughanCentredGram_smooth_log_rate`
- `exists_uniform_pmPronicVaughanCentredGram_normalized_log_rate`
- `tendsto_pmPronicVaughanCentredGram_sub_moving_smooth_term`
- `tendsto_pmPronicVaughanCentredGram_div_of_horizon_and_product`

Scratch, producing, and final direct `lake --old env lean` checks passed.
All four transitive axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. The BVI umbrella import is present; the scratch was removed.
No limits were raised. Packet, classification, and endpoint consequences
remain in the existing formalization queue. No fixed power gain is proved;
full Q-I remains open.
