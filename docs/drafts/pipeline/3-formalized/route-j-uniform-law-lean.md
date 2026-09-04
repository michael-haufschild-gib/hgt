# The uniform law of the Route J residual: one theorem, two limits (Φ and the beat law)

**Stage:** 3 (formalized), 2026-09-03.  Closes MUST-170.  Five new modules, wired into
`RHTower.lean` after `RouteJBeatModeProfile`, axioms `[propext, Classical.choice, Quot.sound]`,
lint clean.  Continues `route-j-scaling-profile-lean.md` (Φ) and `route-j-beat-mode-profile-lean.md`
(the beat law).

**Main theorem** (`RHTower.RouteJUniform.abs_residual_sub_uniformMain_le`).  For every rapidity
`δ > 0` and every `k ≥ 2`, with `σ = sech δ`, `φ = arccos σ`, `θ_{k,j} = (4k + j + ½)φ − π/4`,

    |J_k(δ) − M_k(δ)| ≤ (cosh δ)^{-1/2} (|a(k,σ)| + |b(k,σ)|) · 400 / (sin φ · (4k + 3)),

    M_k(δ) = (cosh δ)^{-1/2} · 2 (2 sin φ)^{-1/2} · [ a(k,σ) C_{4k+3} cos θ_{k,3} + b(k,σ) C_{4k+4} cos θ_{k,4} ],

where `J_k(δ) = residualJetOf (cosineModeDeterminantJet δ) k` is the first-order response of the Route
J critical residual to the mode `cos(δ s)`, `C_N = binom(2N,N)/4^N`, and `a, b` are the explicit
coefficients of the **exact two-index identity**
(`residual_eq_twoIndex`)

    J_k(δ) = (cosh δ)^{-1/2} [ a(k,σ) P_{4k+3}(σ) + b(k,σ) P_{4k+4}(σ) ],
    a = R₁ a₁ + R₂ a₂ + a₀,  b = R₁ b₁ + R₂ b₂ + b₀,  R₁ = r_{2k} r_{2k+1},  R₂ = r_{2k+2} r_{2k+3},

`a_i, b_i` rational in `(k, σ)` (`LegendreShiftReduction`, `RouteJTwoIndexResidual`).

**The two limits** (`RouteJUniformLawLimits`).
1. `tendsto_beatMode_profile_of_uniform`: for fixed `δ > 0`,
   `J_k(δ)/k^{3/2} − 32√(2/π) σ^{3/2} τ^{5/2} sin((4k + 9/2)φ − π/4) → 0` — the beat law, now a
   corollary of the uniform law (`tendsto_uniformMain_beat` gives it for `M`, the error is `O(k)`).
2. `ScalingLimits.tendsto_residual_profile_of_uniform`: along scaling data `p_j → ∞`,
   `2k_j/p_j → X`, `δ_j = log p_j`: `J_{k_j}(δ_j) → Φ(X) = 4√(2/π)[√X cos 4X − 8X^{3/2} sin 4X]` —
   the scaling profile, now a corollary of the same theorem (`tendsto_uniformMain_scaling` gives
   `M → Φ(X)`, the error is `O(σ^{1/2})`).

**Coefficient asymptotics** (`RouteJUniformLawCoefficients`; each rational piece written as a
polynomial quotient in `u = 1/k`, resp. `(u, y = kσ)`, limits by continuity):

    a/k² → 64 σ(1−σ²),   b/k² → −64 σ²(1−σ²)          (fixed σ)
    a/k  → 64 X,         b/k  → 8                      (σ → 0, kσ → X)

and, from sympy (report `uniform_law_expand.log`),
`a = 64k²σ(1−σ²) + 136kσ(1−σ²) + 73σ(1−σ²) + O(σ/k)`,
`b = −64k²σ²(1−σ²) + 8k(1−σ²)(1−22σ²) + (1−σ²)(118σ²−9) + O(1/k)`:
the `k²` terms carry the beat law, the `k` terms carry `√X cos 4X` (`a₁(0) = 0`, `b₁(0) = 8`).

| module | content |
|---|---|
| `LegendreShiftReduction` | `P_{4k+j}(s) = A_j(k,s) P_{4k+3}(s) + B_j(k,s) P_{4k+4}(s)`, `j ∈ {0,1,2,5,6,7,8}`, explicit rational `A_j, B_j` from the three-term recurrence (`legendre_shift0` … `legendre_shift8`) |
| `RouteJTwoIndexResidual` | `coefAR1 = −A₀`, `coefAR2 = A₈`, `coefA0 = 4s(k+1)(8k+9)`, `coefBR1 = 1 − B₀`, `coefBR2 = B₈ − 1`, `coefB0 = −(8k+9)(8ks²+11s²−3)/2`; `residual_eq_twoIndex` |
| `RouteJUniformLaw` | `uniformMain`, `legendre_beat_err_le` (Laplace–Heine at `4k+j` in the beat variables), `abs_residual_sub_uniformMain_le` |
| `RouteJUniformLawCoefficients` | the `u`- and `(u,y)`-forms of the six pieces, `tendsto_num_div_den`, `tendsto_num_div_den₂`, the four coefficient limits |
| `RouteJUniformLawLimits` | `tendsto_wallis_shift`, `cos_beatPhase_three`, `tendsto_uniformMain_beat`, `tendsto_beatMode_profile_of_uniform`; `tendsto_arcsin_div` (from `Real.hasDerivAt_arcsin`), `tendsto_theta`, `tendsto_cos_beatPhase_{three,four}`, `tendsto_two_beatSfac`, `tendsto_cosh_rpow_mul_sqrt_k`, `tendsto_sqrt_k_mul_cb`, `tendsto_uniformMain_scaling`, `tendsto_residual_profile_of_uniform` |

**Why a second-order Laplace–Heine term is not needed.**  MUST-170 was posed as "the second-order
Laplace–Heine term with explicit error".  In the five-term Legendre form the coefficients are
`≈ 4k²` and the residual is `≈ k^{3/2}σ^{3/2}`, so in the scaling regime (`kσ → X`) the
first-order Laplace–Heine errors are amplified by `k²` and the true error `O(C_N/N)` per polynomial
already fails to be `o(1)`: a remainder `O(C_N/N²)` (the second Stieltjes term plus a sharp
bound) would be required, and the elementary Abel-summation proof of `legendre_laplaceHeine` gives
only the relative order `N^{-1/2}`.  The way out is to change the representation: the recurrence
performs the two cancellations exactly (a third difference in the index, `−P₀+2P₂−2P₆+P₈`, and the
`(1,2,1)` smoothing), leaving two Legendre values with small coefficients (`a ≈ 64k²στ²`,
`b ≈ −64k²σ²τ²`, `τ² = 1−σ²`).  With no cancellation left, the owned first-order estimate with its
explicit constant is uniform in both regimes: the error `(cosh δ)^{-1/2}(|a|+|b|)·400/(τ(4k+3))`
is `O(k)` (beat regime, against `k^{3/2}`) and `O(σ^{1/2}(1+X))` (scaling regime, against `Φ = O(1)`).

**Numerical pre-certification** (`2-fully-proven/computations/routej-semilocal-scale/uniform_law_*.py`,
logs alongside): the two-index identity to `10⁻²⁵`; `|J − M|/|J| = 1.3·10⁻⁴` at `k = 3200`,
`δ = log 2`; `M − Φ(X) = −5·10⁻⁴` and `|J − M| = 6·10⁻⁴` at `p = 40000`, `X = 1.3`; the shift
chain, the coefficient pieces and all twelve limit forms verified symbolically
(`uniform_law_leanforms.log`).  The proven bound is valid but loose (`≈ 17|J|` at `k = 3200`):
its constant is the `400` of the Laplace–Heine estimate.
