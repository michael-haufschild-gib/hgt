# T6 Lean programme: nuclear Ruelle zeta functions are zero-free on Re s > 0

- **ID:** t6-nuclear-ruelle-zeta-lean-programme-2026-10-17
- **Stage:** 3-formalized (formalization programme for card 4 item T6)
- **Type:** THEOREM (Lean programme)
- **Source:** `2-fully-proven/route TT/route-tt-structural-theorems-2026-10-14.md`, T6
- **Statement:** For an analytic Markov system (holomorphic inverse branches φ_e mapping a closed disc
  D_{src e} into the θ-subdisc of D_{tgt e}, θ < 1, real and orientation-preserving, expanding on the
  real line) with dynamical zeta ζ_R(s) = exp Σ_n n⁻¹ Σ_{cycles γ, |γ|=n} λ_γ^s (λ_γ = Φ_γ'(x_γ) ∈ (0,1)),
  absolutely convergent for Re s > σ₀: there is an entire D with ζ_R(s) D(s) = D(s+1) and D(s+1) ≠ 0
  on Re s > σ₀ − 1, so the continuation D(s+1)/D(s) is zero-free on Re s > σ₀ − 1 (= 0 when h = 1);
  riemannZeta is not such a zeta function.

## Plan (modules)
1. `HTGeometry/DiscHolomorphicFixedPoint` — Möbius maps of the unit disc, two-point Schwarz–Pick,
   scaling contraction ρ(θa,θb) ≤ 2θ/(1+θ²) ρ(a,b), unique fixed point of a holomorphic
   ψ : D̄(c,R) → D̄(c,θR) (iteration + Cauchy sequence), |ψ'(p)| < 1.
2. `HTGeometry/DiscCoefficientExpansion` — coefficient functional by Cauchy integrals on the circle,
   geometric bounds, expansion, substitution lemma Σ_j coeff_i(w((φ−c)/ρ)^j) coeff_j(g) = coeff_i(w g∘φ).
3. `HTGeometry/WeightedCompositionTrace` — Σ_i coeff_i(w((Φ−c)/ρ)^i) = w(p)/(1 − Φ'(p)) by residues.
4. `HTGeometry/GeometricDecayFredholmDeterminant` — ℕ×ℕ matrices with |M_mn| ≤ C η^{m+n}:
   det(1 − λM) as a limit of truncations (column-ℓ¹ Leibniz bound, column/row update increments),
   entire in λ, holomorphic in parameters; = exp(−Σ λ^n Tr M^n/n) near 0 (corpus Schur/det₂ identity).
5. `RHTower/AnalyticMarkovTransferMatrix` — the system, transfer matrix M(s), trace formula
   Tr M(s)^n = Σ_γ λ_γ^s/(1 − λ_γ) = Σ_k Z_n(s+k).
6. `RHTower/RuelleZetaNuclearZeroFree` — ζ_R(s) D(s) = D(s+1), zero-freeness, riemannZeta corollary.

## Log
- 2026-10-17 — programme created; corpus has det₂ (HTGeometry/FiniteRegularizedDeterminant, Schur
  triangulation, `exp_neg_traceSeries_eq_finiteDet2_neg`) but no parameter-holomorphic determinant and
  no Schwarz–Pick; module 1 started.
- 2026-10-17 — modules 1–4 DONE (standard axioms, oleans built, wired into HTGeometry):
  `DiscHolomorphicFixedPoint` (`exists_unique_fixedPoint`: Möbius/Schwarz–Pick contraction κ(θ) =
  2θ'/(1+θ'²), unique fixed point in D̄(c,θR), |ψ'(p)| ≤ κ < 1); `DiscCoefficientExpansion`
  (`coeff`, `norm_coeff_le`, `hasSum_coeff`, `hasSum_circleIntegral_of_dominated`, `hasSum_coeff_comp`
  substitution); `WeightedCompositionTrace` (`hasSum_coeff_diag`: Σ_i coeff_i(w((Φ−c)/ρ)^i) =
  w(p)/(1−Φ'(p))); `GeometricDecayMatrixPowers` (`GeomDecay`, `fpow`, `ipow`, `itrace`,
  `tendsto_trace_trunc_pow`, `norm_itrace_succ_le`); `GeometricDecayFredholmDeterminant` (`fdet`,
  `norm_det_le_prod_colSum`, `norm_truncDet_succ_sub_le`, `differentiableOn_fdet` (parameters),
  `differentiable_fdet` (entire in λ), `fdet_eq_exp_of_small`, `fdet_one_eq_exp`).
  Next: module 5 (analytic Markov system: paths, composites, real fixed points, chain rule; transfer
  matrix with ℕ-encoding (a,i) ↦ p·i + a, path expansion of powers, trace formula) and module 6.
- 2026-10-17 — modules 5–6 DONE: HTGeometry `AnalyticMarkovSystem`, `AnalyticMarkovTransferMatrix`;
  RHTower `RuelleZetaNuclearZeroFree` (`ruelleZeta_continuation`, `not_riemannZeta_eq_ruelleZeta`).
  All standard axioms, compiled with `lake env lean`, wired. Programme complete → 3-formalized.
