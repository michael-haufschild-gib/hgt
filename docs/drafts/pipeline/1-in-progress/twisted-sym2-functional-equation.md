# Functional equation of the twisted symmetric square via Rankin–Selberg

- **ID:** SYM2-FE
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper, classical) → THEOREM (Lean)
- **Source:** selberg-quarter-conjecturing-loop.md cycles 71–75; shimura-sym2-holomorphy.md
- **Statement:** For u a Maass cusp form on Γ₀(N+1) and χ an even primitive character mod an odd prime q ∤ N+1,
  Λ(s, sym²u ⊗ χ) = L_∞(s) q^{3s/2} L(s, sym²u ⊗ χ) (up to fixed Euler factors at p | N+1) satisfies
  Λ(s, sym²u ⊗ χ) = ε(χ) Λ(1 − s, sym²ū ⊗ χ̄) with ε(χ) = ε₀ χ(N') τ(χ)³ q^{−3/2}.

## Goal
Every GL₂ family argument for Selberg's eigenvalue problem (Duke–Iwaniec (1.7), Iwaniec 10/49, Luo–Rudnick–Sarnak
nonvanishing) uses the forced zero L(2τ, sym²u⊗χ) = 0 (closed in Lean: `shimura_forced_zero_tw`) together with this
functional equation and its root number. Without the root-number phases only ν ≤ 3/10 follows (cycle 73a).

## Approach (weight-0 route, reusing the Γ(N) Eisenstein modules)
1. Scattering matrix of the Γ(N) Eisenstein series: continue φ_{∞σ}(s) = C(s) Σ_u L_u(2s) L(Φ_σ(u ·), 2s − 1)
   (`SelbergEisensteinCriticalLine.phiExt`) to all s via completed Dirichlet L-functions; prove Φ(s)Φ(1 − s) = I.
2. E(1 − s) = Φ(1 − s) E(s): the difference is cuspidal (constant terms cancel by step 1), a Δ-eigenfunction with
   eigenvalue s(1 − s), of moderate growth; for s(1 − s) ∉ ℝ it vanishes (Green's identity on Γ(N)\ℍ, corpus
   `SelbergMaassCoreGreen`); identity theorem.
3. Rankin–Selberg R(s) = ∫_{Γ(Nq²)\ℍ} u ū_χ E(z, s): unfolding at every cusp σ gives the constant term of
   (u ū_χ)|σ; summing with φ_{∞σ} recovers the dual series with Gauss sums.
4. Divide by the functional equation of L(s, χ) (mathlib `completedLFunction_one_sub`) to isolate sym²u ⊗ χ.

## Log
- 2026-09-26 — created. Plan above; step 1 first (pure Dirichlet-L algebra on existing `phiσ`).
