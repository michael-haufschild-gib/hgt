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

## Log
- 2026-11-06 — created; A19 Lean started.
