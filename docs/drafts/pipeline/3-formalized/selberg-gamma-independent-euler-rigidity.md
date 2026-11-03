# Euler rigidity with arbitrary Gamma products

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Γ15
- **Statement:** Two full Selberg functions whose Euler-log discrepancy converges absolutely at some `σ < 1/2` have identical Euler-log and Dirichlet coefficients, without identifying their Gamma presentations. Finite-prime discrepancies are included by the proved strict Euler bound.

## Proof

The completed quotient `T=(γ_F/γ_G) exp L(b_F−b_G)` is holomorphic and nonzero for `Re s > max(σ,0)`. The actual functional equations reflect it across the critical line. Their overlap gives an entire, nonvanishing continuation, including the common zeros and the poles at zero and one.

Let `A_F` be the entire pole regularization of `F`, with pole exponent `m_F`, and put `B_FG=A_F(s)(s−1)^{m_G}/γ_G(s)`. Reciprocal Gamma is entire of finite order, so both `B_FG` and `B_GF` are entire of finite order. Their quotient identity `B_FG=T B_GF`, first proved on `Re s>1`, extends everywhere. Finite order descends to a zero-free entire quotient. Zero-free Hadamard factorization gives `T=exp P` for a polynomial `P`.

Write `b=b_F−b_G`. On `Re s>1`, logarithmic differentiation gives
`L(b)' = P' − log(Q_F/Q_G) − Σ λ_F ψ(λ_F s+μ_F) + Σ λ_G ψ(λ_G s+μ_G)`.
Choose an integer `m≥1` with `m>deg P` and differentiate `m` more times. The polynomial and constant disappear. On any fixed line `Re s=τ>1`, every remaining affine polygamma term tends to zero as `Im s→+∞`; positive slopes and nonnegative real shifts ensure its argument stays in the right half-plane.

The left side is `(-1)^{m+1} L((log n)^{m+1}b(n))`. This Dirichlet series converges absolutely on that line and is Bohr almost periodic. A Bohr almost-periodic function tending to zero at one end is identically zero. Its distinct-frequency coefficients therefore vanish, giving `b(n)=0` for `n≥2`. The prime-power support axiom gives `b_F(1)=b_G(1)=0`. Thus the Euler quotients are one on `Re s>1`, the represented functions agree there, and Dirichlet-series uniqueness gives equality of every coefficient.

## Lean

Namespace `GaloisForLFunctions.SelbergClass`:

- `CompletedEulerQuotient.lean`: entire, nowhere-vanishing completed quotient.
- `CompletedEulerQuotientGrowth.lean`: `completedEulerQuotient_eq_exp_polynomial`.
- `GammaLogSlope.lean`: `iteratedDeriv_gammaLogSlope_vertical_tendsto_zero`.
- `DirichletVerticalDecay.lean`: `coeff_eq_zero_of_lSeries_vertical_tendsto_zero`.
- `GammaIndependentEulerRigidity.lean`: `eulerLogCoeff_eq_of_subcritical_discrepancy`, `coeff_eq_of_subcritical_discrepancy`.
- `FinitePrimeRigidity.lean`: `coeff_eq_of_finite_prime_discrepancy_arbitrary_gamma`.

All seven new or changed proof modules pass canonical `lake --old env lean` checks. Six transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. The modules are imported by `SelbergClass.lean`.

## Scope

Finite-prime changes between full Selberg functions are rigid for arbitrary Gamma presentations; subcritical convergence is derived from the strict Euler bound. More generally, any absolutely convergent subcritical Euler discrepancy vanishes. No Gamma-equality, growth, zero-free-region, or limiting premise is added. Equality of the displayed Gamma parameters is not asserted. General Γ15 remains partially solved.
