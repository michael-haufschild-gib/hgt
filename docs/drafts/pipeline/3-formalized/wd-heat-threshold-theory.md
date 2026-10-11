# WD heat threshold: per-pair law, slice Ki–Kim–Lee, and RH ⟺ λ_WD = Λ

- **ID:** wd-heat-threshold
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/wd-goal-loop-2026-10-09.md` rows 266–280; superseded cards `1-in-progress/wd-heat-per-pair-twelfth.md`, `1-in-progress/wd-kkl-large-height-heated-positivity.md`
- **Statement:** For the heated slice coefficients T_n(λ, x₀, t) of S_0(t,x) = Ξ(t−ix)Ξ(t+ix) and the WD heat threshold λ_WD: 0 ≤ λ_WD < 1/12; RH ⟺ λ_WD = 0 ⟺ λ_WD = Λ ⟺ T_0(λ_WD, 0, t) = 0 for some t; admissible heats = [λ_WD, ∞) with strict positivity above and touching at λ_WD; heated positivity at all heights ≥ T(λ) for every λ > 0; heated hyperbola (Im z)² ≤ (Re z − t)² + x₀² + 3λ ⇒ T_n(λ, x₀, t) ≥ 0; negative heat fails at every real zero of Ξ.

## Goal
Complete qualitative theory of the heat direction of route WD. Not RH: every result is an equivalence or a statement at λ > 0.

## Gates
- [x] 0 → 1
- [x] 1 → 2  paper proofs in ledger rows 274–280
- [x] 2 → 3  Lean: `HTGeometry/PolynomialHeatProduct`, `HTGeometry/PolynomialHeatFactorBounds`, `RHTower/XiSliceHeatPerPairPositivity`, `RHTower/RiemannKernelSharpLogDerivative`, `RHTower/XiSliceHeatMomentConcentration`, `RHTower/XiSliceHeatLargeHeightPositivity`, `RHTower/XiSliceHeatThresholdTouching`, `RHTower/XiSliceHeatNegativeFailure`; standard axioms; wired; lint clean for these modules.
- [ ] 3 → 4  (no stage 4 per user directive)

## Main Lean theorems
`wdHeatThreshold_le_twelfth`, `xiSliceHeatTransfer_nonneg_of_heatedHyperbola`, `xiSliceHeatTransfer_nonneg_perPair`, `exists_xiSliceHeatTransfer_nonneg_large_height`, `wdHeatThreshold_lt_twelfth`, `wdHeatThreshold_lt_of_realRooted`, `riemannHypothesis_iff_wdHeatThreshold_eq_newmanConstant`, `xiSliceHeatTransfer_pos_of_gt`, `exists_xiSliceHeatTransfer_eq_zero_at_threshold`, `riemannHypothesis_iff_exists_xiSliceHeatTransfer_zero_order_eq_zero`, `not_forall_xiSliceHeatTransfer_nonneg_of_real_zero`, `exists_heatKernel_moment_concentration`.

## No-go closure (heat direction cannot reach λ_WD = 0)
- **Exact killing mechanism:** the unconditional inputs of the heat direction (Ki–Kim–Lee asymptotics in the Euler region, Gamma growth, zero counting, kernel tail asymptotics) do not use the Euler product; they hold for Davenport–Heilbronn-type functions with off-line zeros. So the direction cannot force λ_WD = 0. Heat λ corresponds to Gaussian height averaging at scale √λ (transfer identity), i.e. to the averaged (μ-type) side of the corpus dichotomy (row 214).
- **Strongest positive survivor:** the full phase diagram above, in Lean.
- **New insight:** WD has two deformation directions. The abscissa x₀ is Euler-product-sensitive and is governed by zero-free regions (VK: x₀(t) = ½ − w(t)). The heat λ is Euler-blind, and at large heights it buys everything (slice Ki–Kim–Lee). Per zero pair, heat λ buys 3λ of abscissa² (sharp; de Bruijn transfer gives 2λ). RH sits at (x₀, λ) = (0, 0), unreachable along either direction without new arithmetic input at the zero-spacing scale.
- **Status:** formalized (stage 3). Card closed.

## Log
- 2026-10-11 — created at stage 3 consolidating rows 274–280.
