# Full-field ringdown on the modular horizon

- **ID:** modular-horizon-full-field-ringdown
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** follow-up to `3-formalized/ringdown-reads-the-horizon-spectrum.md`: close its "Not formalized" items on the AdS black hole with modular horizon
- **Statement:** On the massless topological AdS₄ black hole with horizon `PSL₂(ℤ)\ℍ`, an Eisenstein wave packet is an exact solution whose reflected constant term is the pulse convolved with the echo train minus its mean, and whose late-time field is a sum of exactly one damped mode per zeta zero.

## Goal
Replace the paper sketch "the full field carries the causal symbol" by theorems about an actual solution of the wave equation on the metric. Not an RH route: universal damping stays RH-equivalent.

## Gates
- [x] 0 → 1 in-progress: corpus read (`lineModel`, `D4BMBackground`, residue theorem, inner bound, good heights)
- [ ] 1 → 2 fully-proven
- [ ] 2 → 3 formalized

## Claims
1. **Metric reduction.** On `D4BMBackground.metric`, the operator `□ + 2` (`R = -12`, conformal coupling) applied to `F = ψ(t, x_*(r), x, y)/r` equals `(r f)⁻¹ (ψ_{**} - ψ_tt + sech²x_* y²(ψ_xx + ψ_yy))`.
2. **Exact lift.** If `𝓕_ττ = Δ𝓕 + 𝓕/4` on the horizon and `τ = t - log(2 cosh x_*)`, then `e^{-τ/2}𝓕` and `tanh(x_*) e^{-3τ/2}𝓕` solve the radial equation of claim 1. The first has Neumann data at the AdS boundary, the second Dirichlet. Both are regular on the future horizon, since `τ = v - log(2r/(r+1))`.
3. **Vertical bounds.** The Whittaker tail of `lineModel u` and its first and second jets are bounded uniformly in `Im u`, locally uniformly in `(x, Y)`, for bounded `Re u`.
4. **Packet.** For a Gaussian amplitude `a`, `𝓕_a(τ, z) = ∫ a(ξ) E(z, ½+iξ) e^{iξτ} dξ` is `SL₂(ℤ)`-invariant and solves the modular wave equation.
5. **Constant term.** `∫₀¹ 𝓕_a dx = Y^{1/2}(g(τ + log Y) + 𝒮_a(τ - log Y))`, where `g` is the pulse and `𝒮_a(T) = ∫ a φ(½+iξ) e^{iξT} dξ`.
6. **Echo identity.** `𝒮_a = g ∗ (K - (3/π) e^{·/2})`.
7. **Ringdown expansion.** For every `A > 0`, `𝓕_a(τ, z) = 2π lim_k Σ_{|γ|<T_k} Res_{u=(ρ-1)/2} + O_{A,z}(e^{-Aτ})`. Only the branch `ω₋` occurs.

## Paper proofs

**Claim 1.** With `f = r²-1`, `∂_r x_* = 1/f`, `F = ψ/r`: `r² f ∂_r F = r ψ_* - f ψ`, whose `r` derivative is `r ψ_{**}/f - 2rψ`. Dividing by `r²` and adding the time and angular terms and `2F = 2ψ/r` cancels the `ψ/r` terms.

**Claim 2.** Put `T = tanh x`, `S = 1-T²`, `H' = T`, so `T' = S`, `S' = -2TS`. For `Ψ = e^{-τ/2}𝓕`: `Ψ_x = -TΨ_τ`, `Ψ_xx = -SΨ_τ + T²Ψ_ττ`, so `Ψ_tt - Ψ_xx = S(Ψ_ττ + Ψ_τ) = S e^{-τ/2}(𝓕_ττ - 𝓕/4)`. For `Ψ = T A`, `A = e^{-3τ/2}𝓕`: `Ψ_tt - Ψ_xx = TS(A_ττ + 3A_τ + 2A) = TS e^{-3τ/2}(𝓕_ττ - 𝓕/4)`. Horizon regularity: `H = -x + log(1+e^{2x})` and `e^{2x} = (r-1)/(r+1)`.

**Claim 3.** `|cosh((η+iξ)t)| ≤ cosh(ηt)` gives `‖K_s(ν)‖ ≤ K_s(Re ν)`. The jets are combinations of `K(ν+k)`, `|k| ≤ 2`, with coefficients free of `ν`. The arithmetic coefficient obeys `‖c_n(u)‖ ≤ n^{3|Re u|+1}`.

**Claim 4.** Differentiate under the integral using claim 3, `‖1/Λ(1+2iξ)‖ ≤ C e^{2|ξ|}` and Gaussian decay; then use `Δ E = -(ξ²+¼)E`. Invariance is termwise, using `E*(u) = E*(-u)` for `ξ < 0`.

**Claim 5.** Fubini with the zero mean of the tail in `x`.

**Claim 6.** For `Re w = c > ½`, `φ(½+w) = ∫ e^{-wτ}K(τ)dτ` and Fubini give `g∗K = (1/i)∫_{Re w=c} a(-iw) φ(½+w) e^{wT} dw`. Moving to `Re w = 0` crosses the pole at `w = ½`, of residue `3/π`. The edges vanish because `‖ξ(2w)‖ ≤ ‖ξ(2w+1)‖` for `Re w > 0`, the limit `c ↓ ½` of `norm_XiC_vertical_shift_lt_of_halfPlaneBound`.

**Claim 7.** Write `E(z, ½+u) = N(u)/ξ(1+2u)` with `N` analytic on `Re u ≤ 0`, and shift to `Re u = -A`. On the good heights `T_k` of `exists_seq_zeta_inv_horizontal`, `1/ζ` is polynomially bounded, `1/Γ` is exponentially bounded, and the Gaussian wins. The poles in the strip are exactly `(ρ-1)/2`. At `u = 0` and `u = -½` the expression `N/ξ` is regular, as `E(z,½) = 0` and `E(z,0) = 1`. The residue theorem applies at any multiplicity.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** pending

## Log
