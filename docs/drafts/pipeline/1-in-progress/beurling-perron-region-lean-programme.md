# Lean programme: prime-deletion Beurling systems, Perron region

- **ID:** beurling-perron-lean
- **Stage:** 1-in-progress (formalization programme for the stage-2 card `2-fully-proven/beurling-prime-deletion-perron-region.md`)
- **Type:** THEOREM (Lean, in progress)
- **Statement (Lean target):** `RiemannHypothesis → ∀ α ∈ (½, 4/5), ∀ β ∈ (β₀(α), ½), ∃ B : BeurlingSystem, IsAlphaBetaSystem B α β`, `β₀(α) = 3α/(α+4)` for `α ≤ 2/3`, `1/(3−α)` for `α ≥ 2/3`. The card's theorem is conditional on RH; the faithful Lean statement is the implication.

## Construction used in Lean (variant of BDR §5)
- BDR §5 takes the deleted primes `P_S` from the random construction of Broucke–Vindas (BDR Thm 1.2) with `π_S = F + O(1)`, `F(x) = Σ_{p≤x} p^{α−1}`, and needs the error measure `dE` (α < 2/3) or the double primes `P_D` (Remark 5.2).
- Lean uses **grouped independent selection**: inside each dyadic block `[2^k, 2^{k+1})` the primes are cut into consecutive groups `G_j` of weight `Σ_{p∈G_j} p^{α−1} ≤ 1` (two consecutive groups weigh `> 1`, so `#groups ≤ 2W_k + 1`); an independent variable `X_j ∈ G_j ∪ {⋆}` picks `p` with probability `p^{α−1}`. `S = {X_j}` consists of distinct primes, so `P_D = ∅`.
- For fixed `(x, t)`, `Σ_{p∈S, p≤x} p^{−it} − Σ_{p≤x} p^{α−1−it}` is, block by block, a sum of `≤ 2W_k + 1` independent centred variables of modulus `≤ 2` (exact means, no partial-group issue). Complex Hoeffding (`HTGeometry.measureReal_norm_sum_ge_le`) + union bound over the `≤ 2^k` jump points `x` and a `t`-net of spacing `2^{−kα/2}` on `|t| ≤ exp(c 2^{kα}/k²)` (beyond that the trivial bound suffices) give, for one realization per block,
  **(R)** `|Σ_{p∈S,p≤x} p^{−it} − Σ_{p≤x} p^{α−1−it}| ≤ C x^{α/2} log x √log(|t|+2)` for all `x ≥ 2`, `t ∈ ℝ`.
- (R) at `t = 0` gives `π_S(x) = F(x) + O(x^{α/2} log x)`, enough for the prime asymptotics (`ψ_{α,β}(x) − x = −x^α/α + O(x^{½+ε})` under RH via von Koch `chebyshevPsi_sub_le_of_riemannHypothesis`).
- (R) gives `log ζ_S(s) = log ζ(s+1−α) + O_ε(√log(|t|+2))` on `Re s ≥ α/2 + ε` for every `α < 1` (the BDR restriction `α < 2/3` came from `dE`): the coefficient sequence `1_S(p) − p^{α−1}` has twisted partial sums `≪ x^{α/2+}`, so `HTGeometry.BoundedPartialSums` continues it with bounds uniform along horizontal rays.

## Modules (bottom-up)
1. `RHTower/BeurlingRandomPrimeDeletion` — grouping, per-block probabilistic existence, gluing, (R).
2. `RHTower/BeurlingDeletionZeta` — `G(s) = log ζ_S(s) − log ζ(s+1−α)` continuation and `√log` bound; `1/ζ_S = exp(−G)/ζ(s+1−α)`; prime asymptotics of `S`.
3. `RHTower/RiemannHypothesisZetaGrowth` — under RH: `ζ^{±1} ≪ |t|^ε` on `Re ≥ ½+δ` (from `exists_producerZeta_subpolynomial_of_weilPositiveFull` with `lam = Λ`); `|ζ(σ+it)| ≪ |t|^{½−σ+ε}` left of `½` (functional equation); crude bound in the thin strip.
4. `RHTower/BeurlingDeletionPerron` — truncated Perron (corpus `Sieve.PerronTruncationError`, `PNTPlus.PerronFormula`) + contour shift ⇒ `N'(x) = a'x + O(x^{1/(3−α)+ε})`.
5. `RHTower/BeurlingHyperbolaConvolution` — BDR Lemma 5.1, `I(β) = ζ(β)/ζ_S(β) ≠ 0`.
6. `RHTower/BeurlingDeletionSawtooth` — `α < 2/3`: `M_{S'} ≪ x^{α/2+ε}`, trigonometric approximation of the sawtooth, Mellin + stationary phase ⇒ `N'(x) = a'x + O(x^{3α/(α+4)+ε})`.
7. `RHTower/BeurlingPerronRegion` — Beurling system assembly (labels `(ℙ∖S) ⊕ ℙ`, norms `p`, `q^{1/β}`), `IsAlphaBetaSystem`, Ω-parts, final theorem, elementary comparisons of the exponent curves, DMU lower bound for the deletion system.

## Corpus assets found
- `HTGeometry.ComplexSumConcentration.measureReal_norm_sum_ge_le` (complex Hoeffding), `BoundedSumConcentration`.
- `RHTower.WeilPositiveProducerLindelof.exists_producerZeta_subpolynomial_of_weilPositiveFull`.
- `RHTower.VonKochChebyshevBound.chebyshevPsi_sub_le_of_riemannHypothesis`.
- `RHTower.BeurlingSystem*` (structure, `intNorm`, counting, zeta series, partial summation).
- `HTGeometry.DirichletSeriesBoundedPartialSums` (continuation from bounded twisted partial sums).
- Perron: `RHTower.Sieve.PerronTruncationError`, `PerronFiniteSum`, `PNTPlus.PerronFormula`.
- Oscillatory integrals: `HTGeometry.OscillatoryIntegrationByParts`; sawtooth: `RHTower.SawtoothFourierSeries`.

## Log
- 2026-10-04 — programme designed after reading BDR §5; grouped-selection variant replaces the Broucke–Vindas random primes.
- 2026-10-04 — Module 1 done: `HTGeometry/GroupedSelectionConcentration` (`exists_selection`), `RHTower/BeurlingRandomPrimeDeletion` (`exists_deletedPrimes`: (R) with constant `52 r/(r−1) + 6`, `r = 2^{α/2}`); both compile under `lake env lean`, not yet module-built/audited/wired.
- 2026-10-04 — Module 2 done (compiles): `RHTower/BeurlingDeletionZeta` (`DeletionData`, `corr`, `differentiableOn_corr`, `corr_eq_LSeries`, `norm_corr_le` ≤ `3·baseConst(δ/2)·√log(|t|+2)`), `RHTower/BeurlingDeletionEulerProduct` (`summable_indicator_rpow`, `rem₁`, `rem₂ α`, holomorphy and uniform bounds, `LSeries_sFree_eq`). `HTGeometry.BoundedPartialSums.norm_sum_mul_powNeg_le_of_growth` added.
- 2026-10-04 — Module 3 done: `RHTower/RiemannHypothesisZetaGrowth` (`exists_norm_riemannZeta_two_sided`: `(|t|+3)^{∓ε}` on `[½+δ, 5/2]`; `exists_norm_riemannZeta_left_le`: `C|t|^{½−σ}(|t|+3)^ε` for `0<σ<½`). Module 4a done: `HTGeometry/SmoothedPerronFormula` (`verticalIntegral'_eq_tsum_smooth1` for `|c n| ≤ 1`, `c 0 = 0`, `1 < σ ≤ 2`).
- Module 4 design (smoothed Perron, avoids thin-strip bounds): integrand `ζ(s)·E(s)·Q(s)·𝓜[Smooth1](s)·X^s`, `E = exp(−corr − rem₁ + rem₂)`, `Q = (s−α)/ζ_u(s+1−α)`; shift `3/2 → σ₀` by `HTGeometry.verticalIntegral'_sub_of_simple_pole`; horizontal decay from `ZetaConvexityBound.exists_norm_riemannZeta_le_convexity` (exponent < 1/2) and `MellinOfSmooth1b` (`|s|^{−2}`); left line from module 3; unsmoothing error `#{n ∈ X(1−cε, 1+cε)}`.
- 2026-10-04 — Module 4 done (compiles): `HTGeometry/SmoothedPerronContourShift` (`exists_norm_sum_sub_le`: abstract smoothed Perron shift, `Σ_{n≤X} c(n) = H(1)X + O(X^{(θ+σ₀)/(1+θ)+κ})` from holomorphy of `H` on `Re s > a`, `|H/(s−1)| ≪ |t|^{κ₁<2}` on the strip, `≪ (|t|+1)^θ` on `Re s = σ₀`), `RHTower/BeurlingDeletionPerron` (`exists_norm_count_sub_le`: under RH, `N'(X) = a'X + O(X^{1/(3−α)+η})` for all `0<α<1`, `a' = perronNum 1`).
- 2026-10-04 — Module 5 (hyperbola) done (compiles): `HTGeometry/PowerHyperbolaConvolution` (`abs_sum_rpow_mul_sub_le`: partial summation constant `abelConst`; `abs_hyperbolaCount_sub_le`: `N(x) = a Z₁ x + Z_β x^β + O(x^{β/(1+β−γ)})`), `HTGeometry/AbelConstantContinuation` (`eqOn_continuation`, `eq_density` `H(1)=a`, `mul_abelConst_eq` `(β−1)Z_β = H(β)`).
- 2026-10-04 — **Perron region closed (compiles):** `RHTower/BeurlingDeletionSystemCount` (system `(ℙ∖S) ⊕ ℙ^{1/β}`, `countBall_eq_hyperbolaCount`, `isDiscrete_deletionSystem`), `RHTower/BeurlingDeletionSystemPrimes` (`BeurlingSystem.chebyshevPsi`, `chebyshevPsi_deletionSystem`), `RHTower/BeurlingDeletionPrimeAsymptotics` (`isBigO_chebyshevPsi_sub`, `not_isBigO_chebyshevPsi_sub`), `RHTower/BeurlingPerronRegion` (`BeurlingSystem.IsAlphaBetaSystem`, `isAlphaBetaSystem_of_count`, `exists_isAlphaBetaSystem_of_perron`: RH ⇒ ∀ ½<α<1, 1/(3−α)<β<½, ∃ [α,β]-system). Covers the card for `2/3 ≤ α < 4/5`.
- Remaining: (6) sawtooth refinement `N'(x) = a'x + O(x^{3α/(α+4)+ε})` for `α < 2/3`; (7) card's DMU lower-bound claim for the deletion system (needs `π_S = F + O(x^{η})`, `η < α/2` — current (R) gives only `x^{α/2}`; plan: mass-greedy groups + Chernoff count control).
- 2026-10-04 — **Sawtooth design (module 6), L² variant, no stationary phase.** `N'(x) = Σ_{m≤x} μ_S(m)⌊x/m⌋ = A x − ½M_S(x) − x Σ_{m>x} μ_S(m)/m − R(x)`, `A = Σ μ_S(m)/m` (abs. conv.), `R = Σ_{m≤x} μ_S(m)ψ(x/m)`.
  * `M_S(y) ≪ y^{α/2+ε}`: abstract smoothed Perron (`exists_norm_sum_sub_le`) with `H = (s−1)E(s)Q(s)`, `H(1)=0`. Tail by Abel summation.
  * Partition `1 = φ(m/M₁) + (1−φ(m/M₁))φ(m/M₂) + (1−φ(m/M₂))`, `M₁ = x^{1/(1+α)}`, `M₂ = x^{4/(α+4)}`, `φ` smooth step. Small: `≤ #sqfree S-integers ≤ 2M₁ ≪ M₁^{α+ε}` (Rankin). Large: Abel summation on `I_k = (x/(k+1), x/k]` (ψ monotone there, weight monotone) ⇒ `≪ x M₂^{α/2−1+ε}`. Middle: dyadic smooth blocks `F(m/M)`, `F` supported in `[1,4]`.
  * Block: `ψ − ψ_Δ` majorized by `2K_Δ`, `ψ_Δ = ψ ∗ φ_Δ = −Σ_{h≥1} φ̂(hΔ) sin(2πhy)/(πh)` (corpus sawtooth sine series + dominated convergence), `K_Δ = Σ_n κ((y−n)/Δ) = Σ_h Δκ̂(hΔ)e(hy)` (Mathlib Poisson summation). Exponential sums `S_b(h) = Σ_m b(m)F(m/M)e(hx/m)`, `b ∈ {μ_S, |μ_S|}`.
  * Key bound `|S_b(h)| ≪ M^{σ₀}(1+|h|x/M)^{1/2+κ}` (+ pole term `≪ M^{α}·M/(|h|x)` for `|μ_S|`): Mellin inversion of `f(u)=F(u)e(c/u)`, contour shift to `σ₀ = α/2+δ`, then Cauchy–Schwarz with **Mellin–Plancherel** (`mellin_eq_fourier` + `SchwartzMap.integral_norm_sq_fourier` for smooth compact support) on `|t| ≤ 1+|c|` and on `|t| > 1+|c|` using `s f̃(s) = −Mellin(u f')(s)`.
  * Optimize `Δ = M^{−(α+1)/3}x^{1/3}`: block `≪ M^{(2α−1)/3}x^{1/3+ε}`; geometric sum ⇒ `x^{3α/(α+4)+ε}`.
  Modules: S1 `HTGeometry/MellinPlancherelBound`, S2 `HTGeometry/MellinTestFunctionPerron`, S3 `HTGeometry/SmoothedSawtoothFourier`, S4 `RHTower/BeurlingDeletionMobius`, S5 `RHTower/BeurlingDeletionSawtooth`, S6 final theorem.
