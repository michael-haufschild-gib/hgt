# F2 — physical cusp energy and the Krein residue

- **Stage:** 3-formalized
- **Result [K]:** The existing finite PM Krein form is the linear term of actual charge-normalized physical cusp energy after explicit exponential counterterms.

## Exact physical formula

For `v∈mayerPeriodKreinSpace`, let `c_s` be its existing basis coordinates and `S` their finite support. Set

`b_s=2ζ(2s−1)/(2s−1)≠0`, `κ_s(a)=−core_s(a)/b_s`,

`Ψ_v(x)=exp(x/2) Σ_(s∈S)c_s κ_s(exp(−x))`, `λ_st=2s+2 conjugate(t)−1`.

Then

`lim_(T→∞) [∫_0^T |Ψ_v(x)|²dx − Re Σ_(s,t∈S, λ_st≠0)c_s conjugate(c_t)(exp(λ_st T)−1)/λ_st]/T`

`= Re [v,v]_PM = Re Σ_(s∈S)c_s conjugate(c_(s♯))`, where `s♯=1/2−conjugate(s)`.

Coefficients outside `S` are zero; reflection closure is unnecessary. The integral uses the literal PM cores and their actual nonzero scattering charges. Subtracting growing terms supplies no positivity.

## Proof

At resonance, `fieldCore_w(a)+B_w/a=normalizedTail_w(a)`. Its exponential upper tail and the resonant lower bound give a global estimate `C a^(−1−δ)` for every `0<δ<Re w`. The actual absolute Cauchy moment of order `1+δ` is finite. Its power-convolution identity sends `B_w/a` to `b_s/a`, proving

`|core_s(a)+b_s/a|≤C a^(−1−δ)` for every `a>0`.

Inversion gives `|core_s(a)+b_s a^(1−2s)|≤C a^(1−ε)` for every `0<ε<2 Re s`. On finite support, choose `0<ε≤1/4` with `ε<2 Re s≤1−2ε` for every active mode. The normalized logarithmic error is `O(exp(−(1/2−ε)x))`, and the model is `O(exp((1/2−2ε)x))`. The difference of their square-energy densities is integrable on `(0,∞)`.

Integrating the finite exponential model yields the displayed counterterm plus `T` times the zero-exponent sum. Since `λ_st=0` iff `t=s♯`, that sum is exactly the existing Krein square. The physical error integral converges; division by `T` removes it.

## Lean

`MayerScattering/CoreScatteringAsymptotics`:

- `fieldCore_scattering_remainder_bound`
- `mayerPeriodCore_scattering_remainder_bound`
- `mayerPeriodCore_scattering_lower_bound`

`MayerScattering/PhysicalCuspKreinResidue`:

- `mayerCuspCharge_ne_zero`
- `mayerCuspEnergy_renormalized_mean`

Both individual `lake --old env lean` audits pass without warnings. All five transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Both umbrella imports are wired.

## Remaining bridge

[Gaussian physical residue](f2-gaussian-physical-krein-residue.md) and [height-uniform normalized cusp bounds](f2-uniform-normalized-cusp-remainder.md) are formalized. The existing infinite zero coordinates recover complete Weil energy through the iterated physical cusp limit. Arithmetic control of the counterterms and complete Weil positivity remain open.
