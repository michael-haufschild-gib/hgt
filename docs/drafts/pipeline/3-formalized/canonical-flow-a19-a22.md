# Canonical flow of the Weil chain (A19–A22)

- **ID:** canonical-flow-a19-a22
- **Stage:** 3-formalized (A19, A20, A22); A21 not done
- **Type:** THEOREM (Lean), in parts
- **Source:** docs/reports/review-0611/obstacles-summary.md §2.1 "Canonical flow"
- **Statement:** Scalar flow `r,m,q` of the anchor at `z=i`; limit-circle transfer; contact scaling; Gelfand–Levitan formula for `q` with its singular terms at `2a=log n`; curve chain.

## Notation
`K=K_a(i,i)`, `u=τ_L(a,i)`, `v=τ_R(a,i)` (real), `u²−v²=2K`.
`r=v/u∈(−1,1)`, `m=(1+r²)/(1−r²)`. Mass `p=(u²+v²)/(2K)=m`; drift `s=uv/K=2r/(1−r²)`; `θ=∫s`.
`H₁=(p+s)e^{2θ}=((1+r)/(1−r))e^{2θ}`, `H₂=1/H₁`. `Ψ=½log H₁=θ+artanh r`. `q=Ψ′` (distributional).

## A19 — paper proof
1. `K′=u²+v²` from the right everywhere, so `(log K)′=(u²+v²)/K=2(u²+v²)/(u²−v²)=2m`.
2. Integrated Riccati: `artanh r(b)−artanh r(a)=Ψ(b)−Ψ(a)−∫_a^b 2r/(1−r²)`. Pointwise form `r′=(1−r²)q−2r` wherever one of `r,Ψ` is differentiable.
3. Pair energy `n_z=‖e(z)‖²+‖e(z̄)‖²` of the normalized Hermite–Biehler function: `n_z′≤(4|z|+2)m n_z` a.e., so `n_z(b)≤n_z(a)(K(b)/K(a))^{2|z|+1}`. With `D_z≤m n_z`, a bounded anchor kernel bounds every kernel (limit-circle transfer). With `riemannHypothesis_or_kernel_tends_to_top_at_contact`: at finite contact `K(i,i)→∞`, hence `∫^{a*}dx/(1−r²)=∞`.
4. `q∈L¹` up to `b`: `L′=q−sinh 2L` is restoring, so `|L|` grows by at most `∫|q|`. Then `m` and `K` stay bounded and contact is excluded there.
5. Contact scaling at order `γ`: `(c−x)m→γ/2`, `r→σ`, so on blocks `[c−d,c−λd]`: `Δlog K→γ log(1/λ)`, `ΔΨ→σ((γ+1)/2)log(1/λ)`, i.e. `|q|≈(1+1/γ)m`.

Lean: `CanonicalSystemOfTheWindowTower/AHyperbolicFlowIsRestoring`, `TheWeilChainIsOneScalarFlow`.

## A22 — paper proof
Lattice anchor flow at real `s`, `s²<1`: `L_{n+1}=L_n−γ_n s R_n`, `R_{n+1}=sR_n−γ_nL_n`, flux `L(s)L(t)−R(s)R(t)=(1−st)E_nK_n(s,t)`, `K_n(s,s)` the sharp constant of evaluation. `r=R/L`: `r_{n+1}=(sr_n−γ_n)/(1−γ_n s r_n)`, `artanh r_{n+1}=artanh(s r_n)−artanh γ_n`. Curve: purity iff first `R` margins positive iff `γ_0..γ_{R−2}∈(−1,1)` iff flow admitted; `r_R=−γ_{R−1}=B(0)`; kick at step `n` is `N_{n+1}q^{−(n+1)/2}`; Li form on primitives is `−2T`.
Lean: `GrowingWindowsOfSpecZ/TheLatticeAnchorFlow`, `TheCanonicalFlowOfACurve`.

## A21
Numerical task; no computation per user instruction. Not done.

## A20 — paper proof

### Singular terms (soft kick)
Half-line coordinate `s_a(t)=U_a(t−a)`. Fix bounded Lipschitz cutoff `χ` supported in `[0,2a)`, `χ=1` near 0. Then `χ s_a=Green[F_a]`, `F_a=χ(p_a e⁰+𝒜 s_a)+K_χ s_a`, `𝒜 S=κS+R*S−polar(S)+Σ_n w_n(S(·+ℓ_n)+S(·−ℓ_n))`, `ℓ_n=log n`, `p_a=e^{i z̄ a}`, and `τ_L(a,z)=∫vF_a`.
1. Modulus: `‖v(·−x)−v‖₁=2V(x)`, so `|W*F(x)−W*F(0)|≤2‖F‖_∞V(x)` and `|s(t)−τV(t)|≤2‖F‖_∞V(t)²`.
2. Split: `|∫v(y−x)f|≤‖f‖_∞V(ρ)+‖f‖₁/ρ`.
3. Uniform bound: `M=sup|s^{±z}|` satisfies `M≤C₂MV(ρ)+C(ρ,η)(1+‖s‖₁)`; absorb, using `‖s_a‖₂²≤K_{a₂}(z,z)/μ(a₂)`. Reflection covers the right part.
4. Increment: `Δ=s_b−ρ s_a`, `ρ=e^{iz̄(b−a)}`, `‖Δ‖₂²≤‖R‖²/μ=(K_b−|ρ|²K_a)/μ≤Ch`, `F_b−ρF_a=χ𝒜Δ+K_χΔ`.
5. Interior: `D_η=sup_{[0,2a−2η]}|Δ|≤C₂(D_η+CV(3η))V(h^{1/4})+C_ηh^{1/4}`, so `D_η√log(1/h)→0` for each fixed `η`.
6. Trace increment `τ_L(b,z)−ρτ_L(a,z)=Σ_m w_m∫v(y)χ(y)Δ(y+ℓ_m)dy+O(√h)`. Terms `ℓ_m<2a` are `o(1/log(1/h))` by 5. Terms `ℓ_m>2b` vanish. If `ℓ_n=2a`, `b=a+ε/2`: the term is `∫_0^εv(y)s^{−z}_b(ε−y)dy=τ_R(b,z)J(ε)+O(V(ε)J(ε))`.

Result: `(τ_L(b,z)−τ_L(a,z))log(1/(b−a))→w(a)τ_R(a,z)` as `b↓a`, and `→0` as `a↑b`; `w(a)=Λ(n)/√n` if `2a=log n`, else 0. Hence the traces, `r` and `Ψ` are continuous before contact, and `(Ψ(x)−Ψ(a))log(1/(x−a))→w(a)`: the singular term of `q` is `2w_nJ′(2a−log n)`, one-sided.

Lean: `CanonicalSystemOfTheWindowTower/TheRenewalReadoutHasAnExplicitModulus`, `TheWeilRieszVectorsHaveGeneralCharts`, `TheWeilChartsAreUniformlyBounded`, `TheWeilTracesHaveTheirSoftKick` (`tendsto_leftTrace_right_kick`, `tendsto_leftTrace_left_kick`, `continuousAt_anchorReflection`, `tendsto_canonicalPotential_right_kick`, `tendsto_canonicalPotential_left_kick`).

### The formula (Abel limit of the Green corner)
At `z=iy` the source `e^{−y(t+x)}` concentrates at the left endpoint, so `τ_R(x,iy)` is the Green corner at scale `1/y` and `τ_L(x,iy)` its normalization. Both are real and `τ_L²−τ_R²=2yK_x(iy,iy)`. Put `r_y=τ_R/τ_L`, `q_y=2y r_y/(1−r_y²)=τ_Lτ_R/K(x,iy)`.
1. `E(iy)=i(τ_L(iy)u−τ_R(iy)v)/√K`, `E^#(iy)=i(τ_L(iy)v−τ_R(iy)u)/√K` by the flux identity.
2. With `P=Im E+Im E^#`, `Q=Im E−Im E^#`: `P′=y(m+s)Q−sP`, `Q′=y(m−s)P+sQ` from the right, and `artanh r−artanh r_y=½(log P−log Q)`. So `(artanh r−artanh r_y)′=q_y−s`.
3. Universality: `artanh r_y(b)−artanh r_y(a)=Ψ(b)−Ψ(a)−∫_a^b q_y` for every `y>0`.
4. Coming down from infinity: `D′=−y sinh 2(D+ω)`, `ω≥−ε`, gives `D(x)≤2ε+artanh e^{−2y(x−x₀)}` for any initial value. `Ψ` is continuous, so `r_y(x)→0` as `y→∞`.
5. Formula: `Ψ(b)−Ψ(a)=lim_{y→∞}∫_a^b τ_Lτ_R/K(x,iy)dx`.

Lean: `CanonicalSystemOfTheWindowTower/TheGreenCornerReadsThePotential`.

## Open: `q∈L¹_loc`
The distribution `q=dΨ` has not been shown to be a function. Reduction: let `φ_x` be the right-edge response, `τ_R^x[G_xf]=∫φ_xf`. Then `G_L=𝒯*𝒯` with `(𝒯f)(x)=∫φ_xf`, and the chart readout gives `∫|q|≲sup_t∫|φ_x(t)|dx`. So the input is the `L¹` boundedness of the triangular factor `𝒯`. For a form with nonpositive off-diagonal part, `φ_x≥0` by Beurling–Deny and the bound follows from `G_L:L^∞→L^∞`. The Weil form has the rank-two polar term, whose positive off-diagonal is frustrated and cannot be switched away. Singular support of `q` is dense for `2a≥log 6`: reflections translate by `log(m/n)`, and `±log 2, ±log 3` generate an orbit once the window has length `log 6`.

