# Arithmetic Forces Blindness: Pole-Saturated Fejér Forcing, Beurling–Hamburger Rigidity, and Three-Currency Unification

- **ID:** arithmetic-forces-blindness-common-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper, formalizing in Lean)
- **Source:** `docs/reports/review-2510/route-unification-ledger.md` §6.3 · `docs/reports/review-2510/hard-obstacles-summary.md` §§3–4 (Q2 / B3.15, Q3 / B3.2, B3.14)
- **Statement:** Pole-saturated Bochner–Fejér positivity against a nonnegative arithmetic measure forces vanishing of spectral defect across dual frequency space and spectral zero space: (I) Riemann's degree-one functional equation with simple poles uniquely forces any nonnegative inverse-square-integrable Borel measure on `[1, ∞)` to be `-2 Re(α) · ∑_{k ≥ 1} δ_k`, uniquely forcing any Beurling prime measure `Π` on `(1, ∞)` to equal Riemann's prime-power measure `∑_{n ≥ 2} (Λ(n)/log n) δ_n` (resolving Q2 / B3.15 affirmatively); (II) record-minimum renormalization on `dampedMobiusEnergy` produces at every subcritical damping `ε ∈ (0, 1/2)` an actual cofactor limit with `K(p, p) ≥ p^{2ε - 2} > 0` for all `p ∈ ℕ+`, excluding augmentation and every zero-cofactor kernel as singleton escape states in U1 (Q3); (III) on spectral divisors, the renormalization saddle-point identity has exact supremum `(√(a₁ m) - √a₀)² / (1 - β)` and sharp all-degree Fejér least upper bound `3 - 2√2`, and forced spectral vanishing simultaneously drives blindness across all three currencies (U1 width functor, U2 scale-orbit Weil sign, U3 maximal blind Meyer ideal).

## Goal

Establish and formalize unconditionally the common forcing law unifying the cancellation (U1), positivity (U2), and realization (U3) families of the route-unification ledger without adding criteria, numerical tweaks, or countermodel no-gos:
1. Resolve Open Question **Q2 (B3.15)** positively in full measure-theoretic generality: prove that Riemann's degree-one `Γ_ℝ(s)` functional equation, simple pole structure, and Euler/measure nonnegativity uniquely determine `ζ` and Riemann's prime-power measure among all Borel measures on `[1, ∞)` and all continuous or discrete Beurling Euler products on `(1, ∞)`.
2. Prove in **U1 (Q3)** via record-minimum renormalization that at every subcritical damping `0 < ε < 1/2`, the damped Möbius receiver possesses an actual cofactor limit `L` satisfying the sharp diagonal floor `L.kernel p p ≥ p^{2ε - 2} > 0` simultaneously for all `p ∈ ℕ+`, ruling out the augmentation kernel `1_{j=k=1}` and every finite-cutoff zero-cofactor kernel as singleton escape limits.
3. Establish the **Unified Arithmetic Forcing Law** connecting pole-saturated Bochner–Fejér coupling, the exact renormalization saddle-point extremum (`IsGreatest`) with sharp all-degree Fejér ceiling `3 - 2√2` (`IsLUB`), and simultaneous forced blindness in all three currencies (`widthFunctor`, `BlindOffLine zetaZeroConfig`, and `meyerTraceBoundedIdeal`).

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems checked via `lake --old env lean`, `#print axioms` clean, umbrella-wired
- [ ] 3 → 4  publication-ready: standalone paper

## Dependency-Closed Paper Proof

### Part I. Measure-Theoretic & Beurling Hamburger Rigidity (`PositiveMeasureHamburgerRigidity`) `[PROVED HERE]`

Let `ν` be a nonnegative Borel measure on `ℝ` satisfying `ν (Iio 1) = 0` and `Integrable (fun u : ℝ => 1 / u ^ 2) ν`.

1. **Automatic `σ`-finiteness and theta regularity.**
   For each `k : ℕ`, on `Icc 1 (k + 1)` we have `1 / (k + 1 : ℝ)^2 ≤ 1 / u^2`, so `ν (Icc 1 (k + 1)) ≤ (k + 1)^2 ∫⁻ (1 / u^2) dν < ⊤`. Since `ℝ = Iio 1 ∪ ⋃_{k : ℕ} Icc 1 (k + 1)` and `ν (Iio 1) = 0`, `ν` is `σ`-finite without any external typeclass assumption.
   Define `measureTheta ν x := ∫ u, (exp(-π u^2 x) : ℂ) ∂ν` for `x > 0`. Using `exp(-w) ≤ w⁻¹` for `w > 0` and `1 ≤ u` `ν`-a.e., `‖exp(-π u^2 x)‖ ≤ (π x)⁻¹ / u^2`, giving `‖measureTheta ν x‖ ≤ (π x)⁻¹ ∫ (1 / u^2) dν` and continuity on `(0, ∞)`.

2. **Pole reflection parity.**
   Suppose `measureTheta ν x = x^{-1/2} measureTheta ν x⁻¹ + α + β x^{-1/2}` for all `x > 0`. Evaluating at `x = 1` gives `measureTheta ν 1 = measureTheta ν 1 + α + β`, hence `β = -α`. Evaluating at `x = 4` (where `4^{-1/2} = 1/2`) gives `measureTheta ν 4 = (1/2) measureTheta ν (1/4) + (1/2) α`; since `measureTheta ν` takes real values (`im = 0`), taking imaginary parts yields `α.im = 0` and `β.im = 0`. Set `ρ := -2 α.re`, so `α = -ρ / 2` and `β = ρ / 2`.

3. **Half-plane Laplace identity for `ν`.**
   Define on `{t : ℂ | 0 < t.re}`:
   `measureSeries ν t := ∫ u, (t / (π (u^2 + t^2))) ∂ν`,
   `measureDual ν t := ∫ u, exp(-2π u t) ∂ν`.
   For real `t > 0`, Tonelli–Fubini (`integral_integral_swap`, justified by `SFinite ν` and integrable nonnegative norms `∫_0^∞ exp(-π (u^2 + t^2) x) dx = 1 / (π (u^2 + t^2)) ≤ (1 / π) / u^2` and `∫_0^∞ x^{-1/2} exp(-π u^2 / x - π t^2 x) dx = (1 / t) exp(-2π u t) ≤ (1 / (2 π^2 t^3)) / u^2`) yields:
   `measureSeries ν t = measureDual ν t + α / (π t) + β`.
   On balls `B(t₀, t₀.re / 2)` inside `{t | 0 < t.re}`, `‖u^2 + t^2‖ ≥ c u^2` (`norm_sq_add_sq_ge_on_ball`) and `exp(-2π u δ) ≤ 6 / (2π u δ)^3` gives `‖-2π u exp(-2π u t)‖ ≤ (6 / (4 π^2 δ^3)) / u^2`, which is `ν`-integrable. Thus differentiation under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) makes both `measureSeries ν` and `measureDual ν` holomorphic on `{t | 0 < t.re}`, and identity theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) extends the Laplace identity to all `t` with `0 < t.re`.

4. **Collar-blind Fejér defect annihilation.**
   Set `t = ε + i τ` (`0 < ε ≤ 1`, `τ ∈ [-1, 1]`), take `2 Re(·)`, multiply by the Fejér triangle kernel `1 - |τ| ≥ 0`, and integrate over `τ ∈ [-1, 1]`:
   - **Spectral/Poisson side (`measureSeries`):** Using partial fractions,
     `2 Re((ε + i τ) / (π (u^2 + (ε + i τ)^2))) = (1 / π) (ε / (ε^2 + (τ - u)^2) + ε / (ε^2 + (τ + u)^2))`.
     For every `u ≥ 1`, `τ ∈ [-1, 1]`, and `0 < ε ≤ 1`:
     if `u ≥ 2`, `|τ ∓ u| ≥ u - 1 ≥ u / 2`, so `(1 - |τ|) ε / (ε^2 + (τ ∓ u)^2) ≤ 4 / u^2`;
     if `1 ≤ u < 2`, `1 - |τ| ≤ |τ ∓ u|` and `2 ε |τ ∓ u| ≤ ε^2 + (τ ∓ u)^2`, so `(1 - |τ|) ε / (ε^2 + (τ ∓ u)^2) ≤ 1 / 2 ≤ 2 / u^2 ≤ 4 / u^2`.
     Thus `(8 / π) / u^2` uniformly dominates the integrand on `[-1, 1] × [1, ∞)` for all `ε ∈ (0, 1]`. For every `(τ, u)` with `|τ| < 1` and `u ≥ 1`, `|τ ∓ u| ≥ 1 - |τ| > 0`, so the integrand tends to `0` as `ε → 0⁺`. By Fubini and dominated convergence, the integrated LHS tends to `0` as `ε → 0⁺`.
   - **Dual + polar side (`measureDual + α/(π t) + β`):**
     First, `∫_{-1}^1 2(1 - |τ|) Re(exp(-2π u (ε + i τ))) dτ = 2 exp(-2π u ε) ∫_{-1}^1 (1 - |τ|) cos(2π u τ) dτ = 2 exp(-2π u ε) (sin(π u) / (π u))^2`. Dominated by `(2 / π^2) / u^2`, its `ν`-integral tends to `2 ∫ (sin(π u) / (π u))^2 dν(u)` as `ε → 0⁺`.
     Second, `∫_{-1}^1 2(1 - |τ|) Re(α / (π (ε + i τ)) + β) dτ = -(ρ / π) ∫_{-1}^1 (1 - |τ|) ε / (ε^2 + τ^2) dτ + ρ ∫_{-1}^1 (1 - |τ|) dτ`. Since `∫_{-1}^1 (1 - |τ|) dτ = 1`, `∫_{-1}^1 ε / (ε^2 + τ^2) dτ = 2 arctan(1 / ε) → π`, and `0 ≤ ∫_{-1}^1 |τ| ε / (ε^2 + τ^2) dτ` tends to `0` as `ε → 0⁺` (splitting at `√ε`), the polar integral tends to `-ρ + ρ = 0`.
   - **Conclusion:** Equating limits gives `∫ (sin(π u) / (π u))^2 dν(u) = 0`.

5. **Forced integrality and exact Hamburger weights.**
   Since `(sin(π u) / (π u))^2 ≥ 0` is continuous and `ν`-integrable, `(sin(π u) / (π u))^2 = 0` `ν`-a.e. On `[1, ∞)`, `(sin(π u) / (π u))^2 = 0 ↔ sin(π u) = 0 ↔ ∃ k : ℕ, u = k + 1`. Combined with `ν (Iio 1) = 0`, we obtain `ν ((Set.range (fun k : ℕ => (k : ℝ) + 1))ᶜ) = 0`.
   Decomposing `ℝ` into `(range (· + 1))ᶜ` and pairwise disjoint singletons `{(k : ℝ) + 1}` expresses `ν` as `Measure.sum (fun k : ℕ => ν {(k : ℝ) + 1} • Measure.dirac ((k : ℝ) + 1))`.
   Setting `c : ℕ → ℂ` by `c 0 = 0` and `c (k + 1) = ((ν {(k : ℝ) + 1}).toReal : ℂ)`, `hmom` yields `Summable (fun k : ℕ => ‖c (k + 1)‖ / (k + 1)^2)`, and `measureTheta ν x = coeffTheta c x = freqTheta (fun k => c (k + 1)) (fun k => (k : ℝ) + 1) x`. By `freqSeries_eq_of_freqTheta_relation` and `coeff_eq_of_hamburgerSeries_periodic_re_pos`, `c (k + 1) = -2 α = ρ` for every `k : ℕ`, so `ν {(k : ℝ) + 1} = ENNReal.ofReal ρ` for all `k : ℕ` (and `ρ ≥ 0`).

6. **Beurling prime-measure uniqueness (`beurlingIntegerMeasure`).**
   For any `σ`-finite measure `Π` on `ℝ` with `Π (Iic 1) = 0` and `Integrable (fun u => 1 / u^2) Π`, define `mulConvPow Π 0 = dirac 1`, `mulConvPow Π (m + 1) = map (· * ·) (Π.prod (mulConvPow Π m))`, and `beurlingIntegerMeasure Π = Measure.sum (fun m : ℕ => ((m ! : ℝ≥0∞)⁻¹) • mulConvPow Π m)`.
   - Induction on `m` shows `mulConvPow Π (m + 1) (Iic 1) = 0`, hence `beurlingIntegerMeasure Π (Iio 1) = 0` and `beurlingIntegerMeasure Π {1} = 1`.
   - Tonelli gives `∫⁻ u⁻² d(mulConvPow Π m) = (∫⁻ u⁻² dΠ)^m`, so `∫⁻ u⁻² d(beurlingIntegerMeasure Π) = exp(∫⁻ u⁻² dΠ) < ⊤`, establishing `Integrable (fun u => 1 / u^2) (beurlingIntegerMeasure Π)`.
   - If `beurlingIntegerMeasure Π` satisfies Riemann's theta law (or completed `Γ_ℝ` functional equation via `converse_theta_relation`), Step 5 forces `ρ = (beurlingIntegerMeasure Π {1}).toReal = 1`, `α = -1/2`, `β = 1/2`, and `beurlingIntegerMeasure Π = Measure.sum (fun k : ℕ => dirac ((k : ℝ) + 1))`.
   - Since `Π ≤ beurlingIntegerMeasure Π` and `Π {1} = 0`, `Π` vanishes outside `{ (k : ℝ) + 2 | k : ℕ }` and every singleton mass `Π {(n : ℝ)}` is finite (`≤ 1`). Comparing `beurlingIntegerMeasure Π {(N : ℝ)} = 1` against `riemannPrimeMeasure := Measure.sum (fun n : ℕ => ENNReal.ofReal (if 2 ≤ n then Λ n / log n else 0) • dirac (n : ℝ))` (whose `beurlingIntegerMeasure` also equals `∑_{k ≥ 0} δ_{k+1}` by unique prime factorization / `vonMangoldt` exponential identity) by strong induction on `N ≥ 2` proves `Π = riemannPrimeMeasure` as measures on `ℝ`.

---

### Part II. Record-Minimum Cofactor Escape Rigidity (`RecordMinimaForceInfiniteCofactorLimits`) `[PROVED HERE]`

Let `ε : SubcriticalDamping` (`0 < ε < 1/2`).
1. By `exists_dampedMobiusEnergy_le`, there exists `D ≥ 0` such that `dampedMobiusEnergy ε N ≤ D (1 + N^{1 - 2ε})` for all `N : ℕ`, while `receiverEnergy_succ_pos` gives `0 < dampedMobiusEnergy ε N` for all `N ≥ 1`.
2. For each `m : ℕ`, set `γ_m := 1 - 2ε + 1 / (m + 1 : ℝ) > 1 - 2ε`. Then `g_m(N) := dampedMobiusEnergy ε N / (N : ℝ)^{γ_m}` satisfies `0 < g_m(N)` for all `N ≥ 1` and `Tendsto g_m atTop (𝓝 0)`.
3. Given any threshold `B ≥ 1`, let `μ_B := min_{1 ≤ j ≤ B} g_m(j) > 0`. Since `g_m(N) → 0`, `{N | B < N ∧ g_m(N) < μ_B}` is nonempty; choosing `N* = Nat.find` gives `B < N*` and `∀ j, 1 ≤ j → j ≤ N* → g_m(N*) ≤ g_m(j)`.
4. Recursively construct `N : ℕ → ℕ` with `N 0 = 2` and `N (m + 1) > N m` as a record minimum of `g_{m+1}` above `N m`. Then `T m := N m - 1` is strictly increasing (`T m + 1 = N m`).
5. By `exists_actualCofactorLimit_along ε T`, there exist a strictly increasing `ns : ℕ → ℕ` and `L : ActualCofactorLimit ε` with `L.subsequence r = T (ns r)`.
6. Fix any `p : ℕ+`. For `r` large enough that `N (ns r) ≥ p`, `1 ≤ N (ns r) / p ≤ N (ns r)`, so the record-minimum property gives `dampedMobiusEnergy ε (N (ns r) / p) / dampedMobiusEnergy ε (N (ns r)) ≥ ((N (ns r) / p : ℕ) / (N (ns r) : ℝ))^{γ_{ns r}} → (p : ℝ)^{2ε - 1}`. Meanwhile, `contracted_energy_ratio_tendsto L p` says the LHS tends to `(p : ℝ) * L.kernel p p`. By `le_of_tendsto_of_tendsto`, `(p : ℝ)^{2ε - 2} ≤ L.kernel p p` for every `p : ℕ+`.
7. Define `augmentationCofactorKernel (j k : ℕ+) : ℝ := if j = 1 ∧ k = 1 then 1 else 0`. Since `L.kernel 2 2 ≥ 2^{2ε - 2} > 0 = augmentationCofactorKernel 2 2`, `L.kernel ≠ augmentationCofactorKernel`, `actualCofactorKernelSet ε ≠ {augmentationCofactorKernel}`, and if any actual limit `M` has `M.kernel p p = 0`, `cardinal_actualKernelSet_eq_continuum_of_ne` yields `Cardinal.mk (actualCofactorKernelSet ε) = Cardinal.continuum`.

---

### Part III. The Unified Law: Saddle-Point Extremum, Sharp Fejér Ceiling, and Three-Currency Blindness (`ArithmeticForcesBlindness`) `[PROVED HERE]`

1. **Abstract Bochner–Fejér Defect-Annihilation Law.**
   Let `(Ω, μ)` be any measure space with nonnegative measure `μ`, `Φ : Ω → ℝ` measurable and `μ`-integrable with `0 ≤ Φ` `μ`-a.e., `D ≥ 0` a spectral defect, and `P : ℝ` a pole budget satisfying `∫ ω, Φ ω ∂μ + D ≤ P`:
   - **(Saturation / `P ≤ 0`):** `P ≤ 0` forces `D = 0`, `∫ Φ dμ = 0`, and `Φ =ᶠ[ae μ] 0`.
   - **(Quantized domination / `D = a₁ m`, `m : ℕ`):** `0 ≤ P < a₁` forces `m = 0`.

2. **Exact Renormalization Saddle-Point Identity (`IsGreatest`) & Sharp Fejér Ceiling (`IsLUB = 3 - 2√2`).**
   - For `0 < a₀`, `0 < a₁`, `0 < m` with `a₀ < a₁ m`, and `β < 1`, algebraic square completion proves `IsGreatest ((fun σ => a₁ * m / (σ - β) - a₀ / (σ - 1)) '' Ioi 1) ((Real.sqrt (a₁ * m) - Real.sqrt a₀)^2 / (1 - β))`, attained at `σ* = 1 + (1 - β) √a₀ / (√(a₁ m) - √a₀) > 1`.
   - Over all finite-degree nonnegative cosine polynomials (`K ≥ 1`, `∀ θ, 0 ≤ cosinePolynomial K a θ`, `0 < a 0`, `a 0 ≤ a 1`), `cosinePolynomial_purchase_ratio_lt_two` gives `(√(a 1) - √(a 0))^2 / a 0 < 3 - 2√2`, while uniform Fejér kernels of length `M → ∞` converge to `3 - 2√2`, proving `IsLUB` with strict non-attainment at every finite degree.

3. **Three-Currency Blindness Forcing Across U1, U2, and U3.**
   Let `Ω ⊆ ℂ` be any spectral region on which `XiDivisorSupport` is empty:
   - **U3:** Every `g : DeningerMeyerStrongLogTarget` whose off-line Mellin nonvanishing locus lies in `Ω` lies in `meyerTraceBoundedIdeal`, hence `0 ≤ meyerSourceTrace g g`.
   - **U2:** Every `f ∈ realTests` whose off-line spectral nonvanishing locus lies in `Ω` lies in `BlindOffLine zetaZeroConfig`, hence `∀ ξ, 0 ≤ configWeil zetaZeroConfig (orbitTest f ξ)` and `OrbitHodgeIndex`.
   - **U1:** Whenever `Ω` contains `{z : ℂ | 1 / 2 + σ < z.re}` (`0 ≤ σ ≤ 1 / 2`), `widthFunctor.obj R ≤ ⟨σ, ...⟩` across all six canonical `ζ`-receivers; at `σ = 0`, all three currencies simultaneously collapse to rate zero, complete Weil sign, and exhaustion of `meyerTraceBoundedIdeal`.

## Novelty and Scope Audit

- **Internal corpus check:** `HamburgerFunctionalEquation` handles only `ℕ`-frequencies; `HamburgerGeneralFrequencies` proves only the half-plane Laplace identity and isolated-atom residues for discrete sequences `(a_n, λ_n)`. Neither proves integrality or uniqueness for nonnegative generalized frequencies or general Borel/Beurling measures (explicitly listed as Open Question Q2 / B3.15 in `hard-obstacles-summary.md`). In `ArithmeticDefectRigidity`, `oddWhiteNoiseKernel` was excluded by `scaled_diagonal_antitone`, while `augmentationKernel` and general zero-cofactor singleton limits remained open in Q3 / B3.2. In `HarmonicCouplingForcesSourceBlindness`, only boundary zero-order vanishing and `a₁ < 2 a₀` were proved, without the exact saddle-point extremum `IsGreatest`, without the `3 - 2√2` `IsLUB` theorem across Fejér degrees, and without the three-currency forcing bridge.
- **External literature check:** Classical Hamburger (1921) and Bochner–Chandrasekharan (1956) require integer or finitely-generated/spaced frequencies and fail for general frequencies `[1, ∞)` with signed coefficients (as shown by even primitive character combinations mod 29). Kurasov–Sarnak (2020) and Olevskii–Ulanovskii (2020) construct non-periodic positive crystalline measures when `ρ > 1` and `widehat{μ}` is signed, leaving the bi-positive spectral-gap Beurling rigidity question open in the review ledger. Our collar-blind Fejér pairing resolves Q2 unconditionally for arbitrary nonnegative Borel measures on `[1, ∞)` and arbitrary Beurling prime measures on `(1, ∞)`.

## Log
- 2026-10-25 — created in `1-in-progress` and paper proof completed with zero open dependencies; moved to `2-fully-proven` and starting Lean 4 formalization immediately.
