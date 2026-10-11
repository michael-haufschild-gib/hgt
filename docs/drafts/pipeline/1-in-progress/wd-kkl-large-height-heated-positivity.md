# WD-KKL: large-height heated slice positivity

**Route:** WD (heat lane). **Stage:** 1 (in progress). **Parents:** rows 266–275 of `wd-goal-loop-2026-10-09.md`; corpus KKL (`KiKimLeeLargeHeightReality`, `KiKimLeeFiniteness`).

## Claim
For every λ > 0 there is T such that T_n(λ, 0, t) ≥ 0 for every n and every |t| ≥ T
(T_n = `xiSliceHeatTransfer lam 0 t n`, the Taylor coefficients of e^{(λ/2)∂_x²}S_0(t, ·)).

Corollary: λ_WD < 1/12 strictly (per-pair law at heights < T(1/24) with the zero-free region
Im z ≤ ½ − 1/(100 log γ); above T(1/24) WD-KKL; monotonicity in λ via `hasSum_xiSliceHeatTransfer_shift`).
More generally λ_WD ≤ max(λ₁, (1/3)·max{(Im z)² : zeros at heights ≤ T(λ₁) + ½}).

## Paper proof (plan)
1. Transfer: T_n(λ,0,t) = ∫ G_λ(t − t') M_n(t') dt', M_n(t') = slice moment of H_λ at t' (corpus).
2. KKL + cone: M_n(t') ≥ 0 for |t'| ≥ X₀(λ), all n (corpus `exists_nonnegTaylorAtZero_riemannHeat_slice`).
3. Fourier form: M_n(t') = ∫ ψ_n(w) cos(t'w) dw with ψ_n ≥ 0 even (w = u + v, D = u − v), so |M_n(t')| ≤ M_n(0)
   and M_n(t') ≥ M_n(0)(1 − t'²σ_n²/2), σ_n² = E_n[(u+v)²] under the measure ∝ g(u)g(v)(u−v)^n, g = Φe^{λu²}.
4. Concentration [OPEN CORE]: σ_n² → 0. Mechanism: for fixed D the w-profile log g((D+w)/2) + log g((D−w)/2)
   has curvature ≍ −πe^{D} (needs the sharp two-sided log-derivative |Φ'/Φ + 2πe^{2u}| ≤ C on the tail;
   corpus has only Φ'/Φ ≤ −πe^{2u}), and the weight D^n pushes D → ∞.
5. Laplace domination: for t ≥ X₀ + 1, the positive part over [X₀+½, X₀+1] beats the contamination over
   |t'| < X₀ by the factor e^{(t−X₀−¼)/(2λ)}; uniform for n ≥ n₁ by step 4, per-n for n < n₁.

## Lean plan
A. Sharp log-derivative of Φ on the tail (cusp series, termwise DR + 2πYR = R/2 + 2YR').
B. Concentration lemma for the moment measures.
C. Laplace domination and assembly; corollary λ_WD < 1/12.

## Status
- 2026-10-11: card written; paper plan; step A next.
- 2026-10-11: Steps A–C DONE [L]. `RiemannKernelSharpLogDerivative.lean`, `XiSliceHeatMomentConcentration.lean`, `XiSliceHeatLargeHeightPositivity.lean` (`exists_xiSliceHeatTransfer_nonneg_large_height`, `wdHeatThreshold_lt_twelfth`). Standard axioms, wired into RHTower, lint clean for these modules. Card ready to move to 3-formalized after a paper write-up check.
- 2026-10-11: consolidated into 3-formalized/wd-heat-threshold-theory.md (stage 3).
