# Review-0611 §2.1 Canonical flow and integration (A15–A18)

- **ID:** review-0611-a15-a18
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0611/obstacles-summary.md), table "Canonical flow and integration"
- **Statement:** A15 `Ψ∈AC_loc` before contact and `L¹` convergence `q_y→q`; A16 numerical `r,m,q` (no computations allowed); A17 weight-specific bounded window solutions; A18 integration of [S] modules.

## Status

| Task | Status | Note |
|---|---|---|
| A18 | in progress | AIF wired by its owner; HKT, AKLT umbrellas need their missing oleans checked and `MainTheorems` wiring |
| A17 | open | specialize `window_edge_law` to `W_λ` |
| A15 | proof below, formalization in progress | modules `TheWeilGreenOperatorIsBoundedOnBoundedForcing` … |
| A16 | not done | numerics; the user forbids computations |

## A15 — paper proof

Notation. Chart coordinate `t∈[0,2a]`, `s_a=chartSource a z`, `ρ=e^{iz̄h}`, `h=b−a`, `Δ=s_b−ρs_a` (`chartIncrement`). `v` causal kernel, `V=∫v`, `∫v=1`, `v(ρ)≤1/ρ`. `𝓡_F(p)=∫v(w−p)F(w)dw`, `Green[F](x)=∫_{Ioc 0 x}v(s)𝓡_F(x−s)ds`. `M[g](T)=‖chartMass‖g(T)+Σ_{n∈N}w_n(g(T+ℓ_n)+g(T−ℓ_n))`, `K=chartSupConstant N`.

**Step 1 (L^∞ bound of the Green operator).** For `g∈L²(window a)`, let `u=G_a g` be the Riesz vector: `Q_a(u,x)=⟨g,x⟩`. By `exists_ae_norm_le_of_window_equation` `u` is essentially bounded. In the endpoint chart the forcing is `C(g+chartMass S+chartBounded S+chartPrime S)+comm S`; the prime and mass terms have sup `≤K M`, `L¹ ≤K L`, so the readout is `≤(e+KM+BL)V(ρ)+(Re+KL+RBL)/ρ+(Lip/2)L`. Absorbing at `KV(ρ)≤½`: `‖u‖_∞≤C(a₁,a₂)‖g‖_∞` uniformly on `a∈[a₁,a₂]`. `‖u‖₁≤C‖g‖_∞` from `μ(a₂)>0`.

**Step 2 (L¹-Lipschitz increments).** `‖Δ‖₁≤Ch`. Take `f` with `|f|≤1`, `∫f̄Δ1_{[0,2a]}=∫_{[0,2a]}|Δ|`, `u=G_a f`, translate `T:H_a→H_b`. The residual `R` has `Q_b(Tx,R)=0`, and `R=w_b+𝐁`, `w_b=Tw`, `𝐁=s_b1_{(2a,2b]}` (sharp restriction preserves the domain). So
`∫_{[0,2a]}|Δ|=Q_a(u,w)=Q_b(Tu,w_b)=−Q_b(Tu,𝐁)=−E(Tu,𝐁)−⟨(B−Adj)Tu,𝐁⟩.`
The second term is `≤C‖𝐁‖₁≤Ch`. In the right chart, with reflected coordinates, `τ=2h`, `p=Green[F_U]`, `s=Green[F_b]`:
`E(S_τp,𝐁)=⟨S_τ p,F_b⟩−⟨F_U,S_τ^*s⟩=−∫_0^τ conj(𝓡_{F_U}(p−τ))𝓡_{F_b}(p)dp`
by `Green=AA*`: `S_τ Green f₁=A(S_τA*f₁)` and `A*S_τf₁(p)=𝓡_{f₁}(p−τ)`. So `|E(S_τp,𝐁)|≤τ‖F_U‖_∞‖F_b‖_∞`. Removing the cutoff costs the commutator, `≤‖𝐁‖₁(Lip/2)‖u‖₁`.

**Step 3 (partial variation is uniformly small).** For disjoint `(a_i,b_i)⊂[a₁,a₂]`, `i∈S`, put `Φ=Σ_i|Δ_i|`. With `c=a₁`:
- `t≤c`, left chart with a fixed cutoff: `Δ_i=Green[F_{b_i}−ρ_iF_{a_i}]`, and the forcing difference is `≤M[|Δ_i|]+c₁‖Δ_i‖₁`.
- `t≥c`, right chart with a cutoff fixed in physical coordinates: `y=2a_i−t`, `|Δ_i(t)|≤A(V(2b_i−t)−V(2a_i−t))+∫_{Ioc 0 y}v(s)|𝓡_{b_i}(y−s+2h_i)−ρ_i𝓡_{a_i}(y−s)|ds`, and `𝓡_b(p+2h)−ρ𝓡_a(p)=∫v(w−p)(F_b(w+2h)−ρF_a(w))dw`, where the forcing difference is again `≤M[|Δ_i|](2a_i−w)+c₁‖Δ_i‖₁`. The physical level is `P=2a_i−p=t+s`, independent of `i`.

Summing over `i`, for every `t`:
`Φ(t)≤A Σ_i(V(2b_i−t)−V(2a_i−t))+sup_P∫v(P−T)M[Φ](T)dT+c₁‖Φ‖₁≤A(V(η)+2|S|/η)+V(ε)K‖Φ‖_∞+(K/ε+c₁)‖Φ‖₁.`
`Φ` is bounded, so absorb at `V(ε)K≤½`: `‖Φ‖_∞≤2A(V(η)+2|S|/η)+C|S|` by Step 2. This tends to zero as `|S|→0`.

**Step 4 (traces).** `τ_L(b)−ρτ_L(a)=𝓡_{F_b}(0)−ρ𝓡_{F_a}(0)=∫v(w)(F_b−ρF_a)(w)dw`, so `Σ_i|τ_L(b_i)−ρ_iτ_L(a_i)|≤K‖Φ‖_∞+c₁‖Φ‖₁`, and `|ρ_i−1|≤Ch_i`. Thus `x↦τ_L(x,z)` is absolutely continuous on compact precontact intervals, for every `z`. So are `τ_R`, `r=τ_R/τ_L`, `artanh r`, and `Ψ=θ+artanh r`, as `θ` is `C¹`. `q=Ψ′∈L¹_loc`.

**Step 5 (`q_y→q` in `L¹`).** `L_y=artanh r_y` is absolutely continuous with `L_y′=q−y sinh 2L_y` (`artanh_spectralReflection_sub`), `q_y=y sinh 2L_y`. For a constant `c`, let `L*=½asinh(c/y)`, so `y sinh 2L*=c`. Kato's inequality for `D=L_y−L*` gives on an interval `I=[x₀,x₁]`:
`y∫_I|sinh 2L_y−sinh 2L*|≤∫_I|q−c|+|D(x₀)|`, i.e. `∫_I|q_y−c|≤∫_I|q−c|+|L_y(x₀)|+|L*|`.
Sum over a step function `q̃`: `‖q_y−q̃‖₁≤‖q−q̃‖₁+Σ_j(|L_y(x_j)|+|L*_j|)`. As `y→∞` the sum vanishes (`tendsto_artanh_spectralReflection_zero`), so `limsup‖q_y−q‖₁≤2‖q−q̃‖₁`, and step functions are dense in `L¹`.

## Log
