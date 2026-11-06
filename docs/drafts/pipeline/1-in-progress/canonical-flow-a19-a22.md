# Canonical flow of the Weil chain (A19–A22)

- **ID:** canonical-flow-a19-a22
- **Stage:** 1-in-progress
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
3. `x=e^{−θ}√K`, `y=e^{θ}√K` are the anchor solution at `z=i`: `A(i)=x`, `B(i)=iy`, and `x′=H₂y`, `y′=H₁x`. Both increase and `xy=K`. If `K` stays bounded on `[base,b)`, then `x,y` are bounded and `∫H₂≤Δx/y(base)`, `∫H₁≤Δy/x(base)`. So `∫(H₁+H₂)<∞`, the limit-circle case.
4. Gronwall on `A′=−zH₂B`, `B′=zH₁A` bounds `A,B` at every `z`, hence every `K(z,z)`. With `riemannHypothesis_or_kernel_tends_to_top_at_contact`: at finite contact `K(i,i)→∞`, hence `∫^{a*}dx/(1−r²)=∞`.
5. `q∈L¹` up to `b`: `(log(1−r²))′=−2rq+4r²/(1−r²)≥−2|q|`, so `1−r²` stays bounded below, `m` bounded, `K` bounded. Contact excluded there.

Lean: `CanonicalSystemOfTheWindowTower/AHyperbolicFlowIsRestoring`, `TheWeilChainIsOneScalarFlow`.
Quantitative transfer: `n_z(b) ≤ n_z(a)(K(b)/K(a))^{2|z|+1}` for the pair energy of the normalized Hermite–Biehler function; `q` on blocks at order-`γ` contact is `σ(γ+1)/(2d)`, so `|q|≈(1+1/γ)m`.

## A22 — paper proof
Lattice anchor flow at real `s`, `s²<1`: `L_{n+1}=L_n−γ_n s R_n`, `R_{n+1}=sR_n−γ_nL_n`, flux `L(s)L(t)−R(s)R(t)=(1−st)E_nK_n(s,t)`, `K_n(s,s)` the sharp constant of evaluation. `r=R/L`: `r_{n+1}=(sr_n−γ_n)/(1−γ_n s r_n)`, `artanh r_{n+1}=artanh(s r_n)−artanh γ_n`. Curve: purity iff first `R` margins positive iff `γ_0..γ_{R−2}∈(−1,1)` iff flow admitted; `r_R=−γ_{R−1}=B(0)`; kick at step `n` is `N_{n+1}q^{−(n+1)/2}`; Li form on primitives is `−2T`.
Lean: `GrowingWindowsOfSpecZ/TheLatticeAnchorFlow`, `TheCanonicalFlowOfACurve`.

## A21
Numerical task; no computation per user instruction. Not done.

## A20 — paper proof (soft kick)
Half-line coordinate `s_a(t)=U_a(t−a)`. Fix bounded Lipschitz cutoff `χ` supported in `[0,2a)`, `χ=1` near 0. Then `χ s_a=Green[F_a]`, `F_a=χ(p_a e⁰+𝒜 s_a)+K_χ s_a`, `𝒜 S=κS+R*S−polar(S)+Σ_n w_n(S(·+ℓ_n)+S(·−ℓ_n))`, `ℓ_n=log n`, `p_a=e^{i z̄ a}`, and `τ_L(a,z)=∫vF_a`.
1. Modulus: `‖v(·−x)−v‖₁=2V(x)`, so `|W*F(x)−W*F(0)|≤2‖F‖_∞V(x)` and `|s(t)−τV(t)|≤2‖F‖_∞V(t)²`.
2. Split: `|∫v(y−x)f|≤‖f‖_∞V(ρ)+‖f‖₁/ρ`.
3. Uniform bound: `M=sup|s^{±z}|` satisfies `M≤C₂MV(ρ)+C(ρ,η)(1+‖s‖₁)`; absorb, using `‖s_a‖₂²≤K_{a₂}(z,z)/μ(a₂)`. Reflection covers the right part.
4. Increment: `Δ=s_b−ρ s_a`, `ρ=e^{iz̄(b−a)}`, `‖Δ‖₂²≤‖R‖²/μ=(K_b−|ρ|²K_a)/μ≤Ch`, `F_b−ρF_a=χ𝒜Δ+K_χΔ`.
5. Interior: `D_η=sup_{[0,2a−2η]}|Δ|≤C₂(D_η+CV(3η))V(h^{1/4})+C_ηh^{1/4}`, so `D_η√log(1/h)→0` for each fixed `η`.
6. Trace increment `τ_L(b,z)−ρτ_L(a,z)=Σ_m w_m∫v(y)χ(y)Δ(y+ℓ_m)dy+O(√h)`. Terms `ℓ_m<2a` are `o(1/log(1/h))` by 5. Terms `ℓ_m>2b` vanish. If `ℓ_n=2a`, `b=a+ε/2`: the term is `∫_0^εv(y)s^{−z}_b(ε−y)dy=τ_R(b,z)J(ε)+O(V(ε)J(ε))`.
Result: `(τ_L(a+ε/2,z)−τ_L(a,z))log(1/ε)→w(a)τ_R(a,z)`, `(τ_L(a,z)−τ_L(a−ε/2,z))log(1/ε)→0`, `w(a)=w_n` if `2a=log n`, else 0. So `Ψ(a+ε/2)−Ψ(a)~w_n/log(1/ε)`: the singular term of `q` is `2w_nJ′(2a−log n)`, one-sided.
Krein form (formal, not yet proved): `∂_aτ_R=−iz̄τ_R+qτ_L`, `∂_aτ_L=iz̄τ_L+qτ_R`, `q=2·corner of the Green function`. `q∈L¹_loc` before contact is open here.

## Log
- 2026-11-06 — created; A19 Lean started.
