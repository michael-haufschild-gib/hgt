# CHMD Phase 2: conjugated-Laplacian transport of the integrated deficit + Möbius injection (MUST-1569)

Module `RHTower/CHMDDeficitPrimitiveConjugatedTransportAndMobiusDilationInjection` (ns `RHTower.CHMDChebyshevTransport`), card `3-formalized/chmd-deficit-primitive-conjugated-transport-mobius-injection-2026-10-17.md`.

- Exact identity: `∫_0^∞ ∂_sK_y Δ = K_y(0) + ∫_0^∞ D(s) f_y''(s) ds`, `D = ccmLogChebyshevDeficitPrimitive`, `f_y = e^{−s/2}K_y`, `f_y'' = e^{−s/2}(∂²K − ∂K + K/4)` (`integral_kernelDeriv_mul_discrepancy_eq_conjugated`). The plan's §3.1 formula was wrong (missed the integral term of Δ).
- `|f_y''(s)| ≤ laplacianBound · e^{−s/2}` uniformly in `y` (`abs_conjugatedLaplacian_le`); `∂²_sK_y` Fourier form `−(1/π)∫ A_y(r) r² cos(rs)` (`kernelDeriv2_eq_kernelDeriv2Fourier`, `abs_kernelDeriv2_le`), `D''` explicit + decay.
- `D(s) = e^s − 1 − Σ' Λ(n) max(s − log n) 0` (`ccmLogChebyshevDeficitPrimitive_eq_tsum`), `|D(s)| ≤ (log 4 + 5)e^s`, continuity.
- Möbius: `mobiusDeficitRest = Explicit + ℓ·M + Tail`; head pairing `≤ laplacianBound * headBudget` uniformly (`abs_integral_head_mul_conjugatedLaplacian_le`); `riemannHypothesis_iff_integral_mobiusDeficitRest_mul_conjugatedLaplacian_bddAbove/_bddBelow`.
- Lean patterns: tent IBP via `integral_Ioi_of_hasDerivAt_of_tendsto` on `g = (s−ℓ)f' − f`; swap via `integral_tsum_of_summable_integral_norm` with `(s−ℓ)e^{−c(s−ℓ)} ≤ (2/c)e^{−c(s−ℓ)/2}`; `measurable_sum_Icc_floor` via `measurable_from_prod_countable_left` on `ℝ × ℕ` + `Nat.measurable_floor`; Pi-apply trap after `HasDerivAt.div/mul/sub` (simp `Pi.*_apply` before `ring`).
- Verdict: BRIDGE. Λ-free part = `Σ μ(n) Φ_y(log n)`, Wall 1 in Möbius coordinates. Observation for the next loop: mass `m² = ¼` makes the pole wave constant and the KG symbol `cos(y√(ρ(1−ρ)))` (Lax–Phillips parameter); the corpus choice `m² = 2` is generic.
