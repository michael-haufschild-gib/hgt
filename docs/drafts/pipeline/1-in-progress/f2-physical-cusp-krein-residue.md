# F2 — physical cusp energy and the Krein residue

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** Realize the finite PM Krein form as the linear term of a renormalized, positive physical cusp-energy integral.

## Exact proposed identity

Write `w_s=2s`, `b_s=2ζ(w_s−1)/(w_s−1)≠0`, and normalize the actual resonant core by `κ_s=−core_s/b_s`. For a finitely supported coefficient family `c_s`, with support `S`, put

`Ψ(x)=exp(x/2) Σ_(s∈S) c_s κ_s(exp(−x))`,

`λ_st=2s+2 conjugate(t)−1`.

The proposed physical formula is

`lim_(T→∞) [∫_0^T |Ψ(x)|² dx − Σ_(s,t∈S, λ_st≠0) c_s conjugate(c_t)(exp(λ_st T)−1)/λ_st]/T`

`= Σ_(s∈S) c_s conjugate(c_(s♯))`, where `s♯=1/2−conjugate(s)` and coefficients outside `S` are zero. Reflection closure of `S` is unnecessary.

The right side is the existing PM Krein form on the packet with coefficients `c_s`. The left side uses the actual cores and explicit scattering-charge normalization. No positivity follows after subtracting the growing terms.

## Analytic gate

Prove, for every upper resonance and every `0<ε<Re w_s`,

`core_s(a)=−b_s/a + O(a^(−1−Re w_s+ε))` as `a→∞`.

Inversion gives `κ_s(a)=a^(1−w_s)+O(a^(1−ε))` as `a→0+`. For finite `S`, choose `ε<min(1/2,1−max_(s∈S) Re w_s)`. Then the difference between actual and exponential-model energy densities is integrable on the logarithmic half-line. Integrating the finite exponential model gives the proposed identity; `λ_st=0` exactly when `t=s♯`.

The exact field decomposition gives `fieldCore_w(a)+B_w/a=normalizedTail_w(a)` at resonance. The existing bound `norm_cuspTailPart_le_exp` bounds this tail by `C a^(−Re w/2) exp(−2πa)` for `a≥1`. For `0<a≤1`, the audited resonant field bound gives `|fieldCore_w(a)+B_w/a|≤C/a`. Consequently, for every `0<δ<Re w`, the corrected field has a global bound `C a^(−1−δ)`.

The absolute Cauchy moment of order `1+δ` exists because `1+δ<1+Re w`. Its power-convolution identity sends `B_w/a` to `b_s/a`, by `scatteringCoefficient_mul_symbol_one`. Integrating the global field bound proves the required outgoing remainder with `δ=Re w−ε`. This uses the actual kernel and its actual field, without an asymptotic premise.

The empty packet gives zero. For a nonempty finite packet, also choose `ε<min_(s∈S) Re w_s`. The normalized error is `O(exp(−(1/2−ε)x))`, while the exponential model is `O(exp((max Re w_s−1/2)x))`. Their cross term and the error square are integrable. The actual packet is measurable and its energy differs from the continuous model by an integrable function. Hence physical energy is integrable on each finite positive interval. The integrated error converges to its half-line integral, and division by `T` removes it.

## Relation to the positivity problem

This would supply a literal physical realization of the signed form and identify its explicit divergent cusp terms. Passing from finite packets to complete Weil energy, and controlling those terms from arithmetic, remain separate problems. Gaussian compactness alone does not obstruct the intended metric: its damping occurs in both physical synthesis and the corresponding signed energy.

## Status

Corpus novelty audit found no physical cusp-energy realization of the PM coefficient form. Paper proof is dependency-closed using the exact exponential tail and Cauchy moment inputs above.

The analytic gate is formalized in `MayerScattering/CoreScatteringAsymptotics`: `fieldCore_scattering_remainder_bound`, `mayerPeriodCore_scattering_remainder_bound`, `mayerPeriodCore_scattering_lower_bound`. Individual `lake --old env lean` audit passes without warnings; all three axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Umbrella import wired.

The physical energy formula remains under Lean verification.
