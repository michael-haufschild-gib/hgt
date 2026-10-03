# Log-lattice Poisson anti-concentration (functions vanishing on {log(n/X)})

- **ID:** log-lattice-poisson-anticoncentration
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, L375–L380 (session 2026-10-03)
- **Statement:** Let `h` be continuous and supported in `[−W,W]`, with `ĥ ∈ L¹`, and suppose `h(log(n/X)) = 0` for every integer `n ≥ 1`. Then
  `|∫h| ≤ C_η [ X^{−2}∫|ĥ| + X^{−½}∫_{|r|≥cX}|ĥ(r)|(1+√(|r|/X)) dr ]`.

## Goal
This is the ζ-free engine of the two-cluster sector of prime-blind Weil positivity (PBAP).
- Long tests made of two blocks at separation `L = log X` are prime-blind iff the block autocorrelation `ψ` vanishes on the shifted log-lattice `{log(n/X)}` (L375).
- The pole term of such a test is `X^{½}∫ψe^{y/2}`.
- Applied to `h = ψe^{y/2}`, the lemma shows the pole gain is paid for by spectral mass at heights `≳ X`, where the archimedean term grows like `log r`.
- Consequence (L380, Corollary B): two-cluster PBAP holds unconditionally for every constrained block whose spectrum does not escape above `X(log X)²`.

Non-circularity: no input about ζ, its zeros, or primes is used. The only arithmetic is that the nodes are the integers.

## Gates
- [x] 0 → 1  in-progress: well-posed; mechanism is Poisson summation in `x = Xe^y` plus van der Corput.
- [x] 1 → 2  fully-proven: complete paper proof below, `[PROVED HERE]`, no open dependency.
- [x] 2 → 3  formalized: `RHTower.LogLatticePoisson.norm_integral_le_of_vanish_logLattice` (module `RHTower/LogLatticePoissonAnticoncentration`, 946 lines). `lake build --old` green; axioms `propext, Classical.choice, Quot.sound`; umbrella `RHTower.lean` wired after `DilationFreeSetMeasure`.
- [ ] 3 → 4  publication-ready (no stage 4 by directive).

## Precise statement
**Theorem.** Let `0 < W < W′`, and let `η ∈ C_c^∞((−W′,W′))` with `η = 1` on `[−W,W]`. Put `c := πe^{−W′}`. There is `C = C(η, W′)` such that the following holds for all `X ≥ 1`.
- Hypotheses on `h : ℝ → ℂ`:
  - (a) `h` is continuous with `supp h ⊆ [−W,W]`;
  - (b) `ĥ(r) := ∫h(y)e^{−iry}dy` is integrable;
  - (c) `h(log(n/X)) = 0` for every integer `n ≥ 1`.
- Conclusion:
  `|∫_ℝ h| ≤ C [ X^{−2}∫_{|r|<cX}|ĥ| + ∫_{|r|≥cX}|ĥ(r)|·(X^{−½}(1 + √(|r|/X)) + X^{−2}) dr ]`.

## Proof [PROVED HERE]
1. **Transport to the integer lattice.** Define `H(x) := h(log(x/X))·X/x` for `x > 0` and `H(x) := 0` for `x ≤ 0`.
   - `H` is continuous with support in `[Xe^{−W}, Xe^{W}] ⊂ (0,∞)`.
   - By (c), `H(n) = 0` for every `n ∈ ℤ`.
   - With `Ĥ(ξ) := ∫H(x)e^{−2πiξx}dx` and the substitution `x = Xe^y`: `Ĥ(ξ) = X∫h(y)e^{−2πiξXe^{y}}dy`. In particular `Ĥ(0) = X∫h`.
2. **Spectral representation.** By (a), (b) and Fourier inversion, `h(y) = (2π)^{−1}∫ĥ(r)e^{iry}dr` for all `y`.
   - Since `h = hη`, Fubini (justified by `ĥ ∈ L¹` and the compact support of `η`) gives
     `Ĥ(j) = (X/2π)∫ĥ(r)I_j(r)dr`, with `I_j(r) := ∫η(y)e^{iφ_j(y)}dy` and `φ_j(y) := ry − 2πjXe^{y}`.
   - Here `φ_j′ = r − 2πjXe^y` and `φ_j″ = φ_j‴ = −2πjXe^y`, so `2π|j|Xe^{−W′} ≤ |φ_j″| ≤ 2π|j|Xe^{W′} =: ν_j` on `supp η`.
3. **Two bounds for `I_j`.**
   - (i) *Second-derivative test* (van der Corput with a `C¹` amplitude): `|I_j(r)| ≤ A₁/√(2π|j|Xe^{−W′})`, with `A₁ = 8(‖η‖_∞ + ‖η′‖₁)`.
   - (ii) *Two integrations by parts* when `|φ_j′| ≥ μ > 0` on `supp η`: from `I = ∫((η/φ′)′/φ′)′e^{iφ}`,
     `|I_j(r)| ≤ ‖η″‖₁/μ² + (3‖η′‖₁ + ‖η‖₁)ν_j/μ³ + 3‖η‖₁ν_j²/μ⁴`.
4. **Summation over `j ≠ 0` for fixed `r ≥ 0`.** (`r ≤ 0` is symmetric, with `j ↦ −j`.)
   - `j ≤ −1`: `φ_j′ = r + 2π|j|Xe^y ≥ 2π|j|Xe^{−W′} =: μ`, and `ν_j/μ ≤ e^{2W′}`. So (ii) gives `|I_j| ≤ A₂/(|j|X)²`, and `Σ_{j≤−1} ≤ A₂ζ(2)/X²`.
   - `j ≥ 1` with `r < cX = πe^{−W′}X`: `μ = 2πjXe^{−W′} − r ≥ πjXe^{−W′}`, so again `|I_j| ≤ A₂/(jX)²` and `Σ ≤ A₂ζ(2)/X²`.
   - `j ≥ 1` with `r ≥ cX`. Put `j_± := re^{±W′}/(2πX)`.
     - *Far* `j` (`j ≥ 2j₊` or `j ≤ j₋/2`): `μ ≥ ½max(2πjXe^{−W′}, r)` and `ν_j/μ ≤ 4e^{2W′}`, so `|I_j| ≤ A₃/μ²`. The sum over far `j` is `≤ A₃(Σ_{j≥2j₊}(πjXe^{−W′})^{−2} + j₋·(2/r)²) ≤ A₄/(rX)`.
     - *Mid* `j` (`j₋/2 < j < 2j₊`, at most `1 + 2j₊` of them): by (i), `|I_j| ≤ A₁/√(πj₋Xe^{−W′}) ≤ A₅/√r`. The sum is `≤ A₅(1 + re^{W′}/(πX))/√r ≤ A₆X^{−½}(1 + √(r/X))`, using `r ≥ cX`.
   - Hence `S(r) := Σ_{j≠0}|I_j(r)| ≤ C₀X^{−2}` for `|r| < cX`, and `S(r) ≤ C₀[X^{−½}(1+√(|r|/X)) + X^{−2}]` for `|r| ≥ cX` (with `1/(|r|X) ≤ X^{−2}/c`).
5. **Poisson summation.** If the right side of the theorem is infinite, there is nothing to prove.
   - Otherwise `Σ_j|Ĥ(j)| ≤ (X/2π)∫|ĥ|S < ∞`.
   - The 1-periodization `P(x) = Σ_nH(x+n)` is a finite sum of continuous functions, hence continuous, and its Fourier coefficients are `Ĥ(j)`. An absolutely summable Fourier series converges uniformly to a continuous function with the same coefficients, so `P(0) = Σ_jĤ(j)`.
   - `P(0) = Σ_nH(n) = 0`, so `X∫h = Ĥ(0) = −Σ_{j≠0}Ĥ(j)`.
6. **Conclusion.** `X|∫h| ≤ (X/2π)∫|ĥ(r)|S(r)dr`. Divide by `X` and insert step 4. ∎

## Remarks
- The weight `√(|r|/X)` comes from the `≍ r/X` stationary aliases at height `r`, bounded with absolute values. Removing it needs cancellation in the dual sums `Σ_j j^{−ir}`, which is Lindelöf territory (L378–L385).
- Corpus tools for Lean:
  - Poisson summation: mathlib, `Real.tsum_eq_tsum_fourierIntegral`.
  - Second-derivative test: `R:VanDerCorputLocal` (`secondDerivTestOn`) and `R:VanDerCorputWeightedSecondGeneral`.
  - First-derivative / IBP engine: `R:FirstMoment` (`norm_integral_mul_exp_phase_le`) and `R:VanDerCorputIBP`.

## Log
- 2026-10-03 — created at stage 2 from L375–L380. Paper proof complete (steps 1–6). Lean formalization next.
- 2026-10-03 — formalized. The Lean statement takes:
  - the spectral density `F` (`h = specFn F`, i.e. `h(y) = ∫F(r)e^{iry}dr`);
  - a `C²` cutoff `c : Cutoff a` equal to `1` on `[-W,W]`;
  - the integrability of `‖F‖·Bnd`.

  It proves `‖∫h‖ ≤ ∫‖F(r)‖·Bnd(r)`, with `Bnd = 4K_far/X² + [|r|e^a/(πX) > 1]·4C√(|r|e^a/(πX))` and `C = 32L₁/√(2πXe^{-a})`.

  Supporting lemmas, reusable:
  - `integral_mul_cexp_eq_two_ibp` (exact double integration by parts);
  - `norm_integral_mul_cexp_le_two_ibp` (`O(1/μ²)` oscillatory bound);
  - `norm_osc_le_vdC`, `norm_osc_le_coeff`, `sum_norm_osc_le` (alias sums over ℤ);
  - `fourier_transported_eq` and `fourier_transported_specFn` (change of variables `x = Xe^y` and Fubini).
