# MC: sign of the Liouville K-density — conjecture loop (Opus)

- **ID:** MC-KSIGN-LOOP-OPUS
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP on a stronger-than-RH sign
- **Parent:** `mc-scaled-liouville-density-cone.md` (MC-C12.93; that card proves the finite-prime cone is
  equivalent to the full sign by positive rough deletion). Formal side task: `mc-triangular-quadratic-pole-cancellation.md`.

## Target

`K(t) = Σ_n λ(n)(1/n + t)e^{−nt} ≥ 0` for every `t > 0`. Equivalently `J(t)/t` is nonincreasing,
`J(t) = Σ λ(n)e^{−nt}/n`, i.e. the Laplace transform of `x·T(x)`, `T(x) = Σ_{n≤x} λ(n)/n`, is ≥ 0.
`K ≥ 0 ⇒ J ≥ 0 ⇒ RH` (Landau on `Γ(s)ζ(2+2s)/ζ(1+s)`).

## Exact facts derived in this loop (paper)

- Mellin: `∫K t^{s−1}dt = Γ(s)(1+s)ζ(2+2s)/ζ(1+s)`; under RH
  `K(t) = (√π/2)|ζ(½)|^{−1}·t^{1/2} + Σ_ρ Γ(ρ+1)ζ(2ρ)/((ρ−1)ζ′(ρ))·t^{1−ρ} + Σ_{k even ≥2} C_k t^{k+1}`,
  `C_2 = −0.175…`, `C_4 = +0.069…` (trivial-zero terms; consistent with the direct value `K(1) ≈ 0.483`).
- Theta form: `K(t) = Σ_d μ(d)Φ(dt)/d`, `Φ(u) = Σ_m (1/m² + u)e^{−m²u} = ζ(2) − ½√(πu) + ε(u)`,
  `ε(u) = uR(u) − ∫_0^u R`, `R` the exponentially small Jacobi remainder; the linear terms cancel.
- Lambert positivity: `Σ_{k≥1} K(kt) = Σ_N c(N)(1+Nt)e^{−Nt}`, `c(N) = (λ*id)(N)/N > 0`; so `K` is the
  Möbius dilation of a strictly positive function.
- Residue squeeze: `K ≥ 0` forces RH, simplicity of every zero and
  `|Γ(ρ+1)ζ(2ρ)/((ρ−1)ζ′(ρ))| ≤ (√π/2)/|ζ(½)|` (Fejér bound for the almost-periodic `t^{−1/2}K` at `t→0`).
  Hence `K ≥ 0` is strictly beyond RH by a quantitative near-double-zero exclusion (CANNOT-471 type).

## Cycles

| # | conjecture | verdict | lesson |
|---|---|---|---|
| K1 | Lambert/theta cone: `g = Σ_k ψ(k·)`, `ψ ≥ 0`, contains the K-kernel | FALSE | `ψ` has Mellin `Γ(s+1)/((s−1)ζ(s))`; Landau ⇒ `ψ` changes sign. Any cone `{Σ a(k)ψ(k·)}` with `a ≥ 0`, `λ*a ≥ 0` collapses to `K` itself (`a = |μ|`) |
| K2 | zeta-mixture cone: weights CM in `log n` | FALSE | `e^{−y−te^y}` is log-concave in `y`, not CM; positive zeta mixtures never carry a dilation family with a Mellin strip |
| K3 | SOS via multiplicative Hankel `⟨λA_t, H_t λA_t⟩` with `A_t*A_t = g/h` | CIRCULAR | absolute convergence needs the support of `ν` beyond its own decay exponent; the continuation is a line mean square of `ζ(2s)/ζ(s)` (sign-blind wall) |
| K4 | a-family `f_a = (−a)^Ω`: `K_a ≥ 0` for all `a < 1`, then `a → 1` | CIRCULAR | `K_a ~ C_a(log 1/t)^{−a}` with `C_a → 0`; each fixed `a` only needs zeros below height `≈ (2/π)log(1/(1−a))`; uniformity in `a` is RH plus the squeeze |
| K5 | complete monotonicity of `J/t` to all orders | FALSE (Turán) | order `k` resolves zeros with `γ ≲ √k`; Turán's negative value forces failure at some finite order; `K` is order 1 |
| K6 | Bochner: `τ ↦ Γ(σ+iτ)(1+σ+iτ)ζ(2+2σ+2iτ)/ζ(1+σ+iτ)` positive-definite | REDISCOVERED | restatement of `K ≥ 0`; the factor `1/ζ` is not PD |

## Next

Attack through complete multiplicativity only (K1–K6 use none of it beyond Dirichlet algebra). Candidate
mechanisms: (i) Euler-product log-positivity in the dilation variable; (ii) parity rigidity `λ(p) = −1` for
all `p` as an extremal problem over `f(p) ∈ [−1,0]`; (iii) theta modularity of `Σλ(n)/(e^{nt}−1)` combined
with the dilation Möbius structure.
| K7 | Euler-product PD: `τ ↦ Π_p(1+p^{−1−σ−iτ})^{−1}` times the PD factor `Γ(σ+iτ)(1+σ+iτ)` is PD | FALSE | each Euler factor has alternating Fourier coefficients `(−p^{−1−σ})^k`; Schur products need both factors PD; complete multiplicativity enters only through these alternating local factors |
| K8 | extremal parity: `K_λ(t) = min` over completely multiplicative `f(p) ∈ [−1,0]` and the minimum is ≥ 0 | CIRCULAR | the minimum at fixed `t` is attained at sign patterns `f(p) = −1` for `p ≲ 1/t`, i.e. at `λ` restricted to small primes; its sign is the finite-prime cone, already equivalent to `K ≥ 0` (MC-C12.93) |
| K9 | positive real-`s` mixture `K(t) = ∫_{s>1} k_t(s) ζ(2s)/ζ(s) ds`, `k_t ≥ 0` | FALSE | same log-concavity obstruction as K2; on `(½,1)` the real values `ζ(2s)/ζ(s)` are negative, so the strip cannot be used either |

Formal side result this session: MC-C12.99-S2 (`LiouvilleTriangularHeadOscillation`), every uncancelled
short head `P + cA` oscillates at `x^{3/4−ε}`; see `../../../3-formalized/mc-triangular-head-supercritical-oscillation.md`.
