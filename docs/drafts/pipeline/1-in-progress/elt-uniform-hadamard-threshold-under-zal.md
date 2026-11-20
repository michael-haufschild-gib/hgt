# Uniform Hadamard positivity threshold under the zero approach law

- **ID:** elt-uniform-hadamard-threshold-under-zal
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-1911/todo.md` #17 · `formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean`
- **Statement:** Under `ZerosApproachLine` (`EventualHadamardPositivity`), prove `BddAbove (hadamardThreshold '' Set.Ioi (1 / 2))`, equivalently `ZetaLandingLaw : ZerosApproachLine → FiniteOffLine`.

## Goal
Eliminate infinite sequences of off-line zeros of `ζ(s)` whose real parts converge to `1/2` (`Θ_∞ = 1/2`, `(rightZeros zetaZeroConfig).Infinite`), reducing `RiemannHypothesis` to `ZerosApproachLine ∧ (FiniteOffLine → RiemannHypothesis)` (`riemannHypothesis_iff_three_atoms`).

## Gates
- [x] 0 → 1  in-progress: equivalences, two-sided countermodel barriers, and open analytic core isolated
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem in `ExceptionalLayerTheory`, `lake --old env lean` green, standard axioms only

## Approach and Open Mathematical Core

1. **Established equivalences (`zetaLandingLaw_tfae`, `failure_of_landing_forces_additive_tracking`).**
   `EventualHadamardPositivity → BddAbove (hadamardThreshold '' Set.Ioi (1 / 2))` is unconditionally equivalent to `ZetaLandingLaw` (`ZerosApproachLine → FiniteOffLine`), `EventualHadamardPositivity → EventualHadamardPositivityRight (1 / 2)`, `ZerosApproachLine → negIndex (zetaKernel ∘ (twoPrimeLattice Nat.prime_two Nat.prime_three).subtype) < ⊤`, `ZerosApproachLine → EventualSlicePositivity`, `ZerosApproachLine → CosineDefectsBounded`, `ZerosApproachLine → EventualFilteredCentralGapBudget`, and `ZerosApproachLine → FiniteDimensional ℝ oddBoundStateSpace`. Under `ZerosApproachLine ∧ ¬FiniteOffLine`, `topRightOrdinate σ → +∞` and `hadamardThreshold σ - topRightOrdinate σ → 0` as `σ ↓ 1/2`.

2. **Four simultaneous barriers any valid proof must cross.**
   - *Functional-equation and `Γ_ℝ` barrier (`exists_riemann_gamma_counting_model_without_landing`):* Pairing consecutive `Ξ`-ordinates into quartets `1/2 ± δ_n ± i γ_{2n+1}` (`δ_n → 0⁺`) yields an order-`1` entire completion with the exact `Γ_ℝ(s)` factor, residue `1` at `s = 1`, exact Riemann–von Mangoldt zero count `2⌊N_ζ(T)/2⌋`, `ApproachesLine`, and `¬FiniteOffLine`. Pure functional-equation, Hadamard-product, de Bruijn–Newman heat-flow, and Pontryagin–de Branges arguments without `∑_{n ≥ 1} n^{-s}` cannot prove `ZetaLandingLaw`.
   - *Positive integer-norm Euler-product and pole-cleared mollifier barrier (`exists_approaching_integer_norm_euler_product`):* `WaveSpec` constructs a convergent Euler product `∏_k (1 - q_k^{-s})^{-1} = ∑_{n ≥ 1} a_n n^{-s}` (`q_k ≥ 2`, `a_n ∈ ℕ`, `(1/N)∑_{n<N} a_n → A > 0`) continuing holomorphically and zero-free across `Re s = 1/2` to `{Re s > 1/3, s ≠ 1}` with subpolynomial vertical growth on `Re s ≥ 1/2`, `ApproachesLine`, and `¬FiniteOffLine`. Clearing the finitely many deep zeros in `Re s ≥ 1/2 + ε/2` by `A_ε(s) = ∏_j (1 - 2^{ρ_j - s})` keeps `|A_ε(s)| ≥ (2^{ε/4} - 1)^M > 0` on `0 ≤ Re s ≤ 1/2 + ε/4`, yet every surviving shallow zero `ρ_k = 1/2 + δ_k + i γ_k` (`0 < δ_k ≤ ε/4`) still contributes an `X^{δ_k}` residue on `[γ_k - 1, γ_k + 1]` consistent with Poisson low-value bounds. Pure Dirichlet-series, positivity, Tauberian, Bettin–Gonek mollifier, Montgomery zero-detection, and Hadamard three-lines arguments on `Re s ≥ 1/2` without `ξ(1 - s) = ξ(s)` cannot prove `ZetaLandingLaw`.
   - *Stickelberger–Gauss completion barrier (`MoebiusSignedGaussPairingsEndAtThreeFifths`):* Rank-one Möbius-signed Gauss-sum completions over cyclotomic fields pay Stickelberger defect `c ≥ k/2` and theta-completion cost `c ≥ (2/3)k - 1`, terminating at abscissa `3/5 > 1/2` and missing `δ_k → 0⁺`.
   - *Lehmer-pair and `t → 0⁺` heat-saddle indistinguishability:* Relocating pairs of critical-line zeros `1/2 + i(γ_k ± η_k)` to `1/2 ± δ_k + i γ_k` with `δ_k, η_k ≪ exp(-exp(γ_k))` changes `ζ(s)` outside `|s - (1/2 + i γ_k)| < γ_k^{-A}` by `O(exp(-exp(γ_k)))`, while in Ki–Kim–Lee's Gaussian saddle `u = y + t log(X / 2π)` (`KiKimLeeLargeHeightReality`), healing a depth-`δ_k` quartet occurs at `t_k ≍ δ_k^2`, where `t_k log(γ_k / 2π) ≪ δ_k` lies deep inside the critical strip rather than in the Euler half-plane `Re s > 1`. Any height-local approximate functional equation, Riemann–Siegel expansion, or positive-time heat-flow argument cannot separate a close on-line Lehmer pair (`Z(t_k^*) Z''(t_k^*) ≤ 0`) from an off-line pair (`Z(t_k^*) Z''(t_k^*) > 0`).

3. **`[OPEN CORE]`:**
   Prove an unconditional coupling on actual `ζ(s)` that simultaneously uses `ξ(1 - s) = ξ(s)`, exact unit Dirichlet coefficients `a_n = 1` (`∑_{n ≥ 1} n^{-s}`), and `ZerosApproachLine` (`LindelofCriticalLine` and `Θ_∞ = 1/2`) either at unbounded multiplicative scales `log x ≫ 1/δ_k` (bounding the negative index of `zetaKernel` on `⟨2, 3⟩` under `Θ_∞ = 1/2`) or via an exact global sign invariant of `(Z')^2 - Z Z''` at large heights (`EventualSlicePositivity`).

## Log
- 2026-11-20 — created in `1-in-progress` with exact equivalence audit, four-way obstruction boundary, and `[OPEN CORE]` specification.
