# Window jump counts through `log 3` and naive heights on `ℤ[ℚ_{>0}^×]`

- **ID:** WJCH
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Source:** docs/reports/review-0211/obstacles-summary.md §2.5.1 (Q1, steps 1–3) and §2.6.1 (B20, B28, B32)
- **Statement:**
  1. **Single-prime window jump-count and `T₂`-graph decomposition (`2a ≤ log 3`):** For every real test `f ∈ realTests` supported in `[−a, a]` with `2a ≤ log 3`, all prime powers `n ≥ 3` have `autocorr f (log n) = 0`, and Weil's quadratic form decomposes into the archimedean Lévy jump count `J_∞(f)`, the `T₂`-graph jump count `J_{T₂}(f) = ∫ (f(u) − f(u + log 2))² du` (or in gauge coordinates `f = M g`, the interior strip jump `∫_{−a}^{a − log 2} M(u)M(u + log 2)(g(u) − g(u + log 2))² du`), diagonal mass, and the signed pole squares `2 coshPairing(f)² − 2 sinhPairing(f)²`. On `2a ≤ log 2` (including the endpoint `2a = log 2`), the `T₂` term vanishes as well.
  2. **Variable-hub and `T₂`-stick sum-of-squares identities, unconditional positivity regimes, and the folded-Markov obstruction:**
     - Variable hub conductances `w(x) ≥ 0` and coupled `T₂`-pairs `(x, log 2 − x)` admit exact completion-of-squares identities into manifest squares plus a global Schur margin.
     - Unconditionally and without numerical matrix computation: `primitiveH1` and `weilPair` are strictly coercive on all window tests up to `a ≤ 3/10` (`W(f, f) ≥ (1/5000) ∫ f²`), on all odd window tests past the first prime up to `a ≤ 181/500 > ½ log 2` (`W(f, f) ≥ (1/1000) ∫ f²`), and on all smooth even-pole-orthogonal (`coshPairing f = 0`) window tests across the entire prime-free window and past `p = 2` up to `2a ≤ log 2 + 1/50` (`W(f, f) ≥ (1/1000) ∫ f²`).
     - **Exact folded-Markov obstruction (`Q1` step 3):** Pointwise nonnegativity of the folded jump conductance `ω(|x − y|) + ω(x + y) − c₀ cosh(x/2) cosh(y/2)` on `(0, a)²` forces `c₀ ≤ 2 ω(a) / cosh(a/2)`. At both `a = ½ log 2` (`c₀ ≤ 8(√2 − 1)`) and `a = ½ log 3` (`c₀ ≤ 3(√3 − 1)`), the `c₀`-calibrated form is strictly negative on smooth plateau tests, so no positive gauge `M > 0` admits a pointwise-nonnegative folded jump-plus-potential decomposition at `a = ½ log 2` or `a = ½ log 3`; non-local inter-point squares are forced. Moreover, every individual `Θ`-translate `lift b` (`|b| < ½ log 2`) lies in the full polarized Weil radical (`weilPair (lift b) q = 0` for all `q : SourceGraph`).
  3. **Multiplicative rational scale heights on `ℤ[ℚ_{>0}^×]` and two-prime subrings (`B20, B28, B32`):**
     - Pullback along `posRatLog : PosRatScale →+ ℝ` (`q ↦ log q`) equips `ℚ_{>0}^×` with the scaling datum `zetaPosRatScalingDatum` and integral Rosati form `posRatRosatiForm x ξ` on `ℤ[ℚ_{>0}^×]`.
     - On every unconditional positivity window (`a ≤ 3/10` all parities, `a ≤ 181/500` odd, `2a ≤ log 2 + 1/50` smooth `cosh`-orthogonal), `⌊posRatRosatiForm x ξ⌋₊ : ℕ` is an unconditionally nonnegative count satisfying `posRatRosatiForm x ξ = ↑⌊posRatRosatiForm x ξ⌋₊ + rem(ξ)²` and `|↑⌊posRatRosatiForm x ξ⌋₊ − posRatRosatiForm x ξ| ≤ 1`.
     - Across all cycles `x : ScalingCycle` (and already on the Hecke orbit of a single spectrally generic smooth test `g`, even restricted to the rank-two subring `ℤ[p^ℤ · q^ℤ] ⊂ ℤ[ℚ_{>0}^×]` of any two distinct primes `p ≠ q`), existence of a nonnegative naive height or `ℕ`-valued count within bounded error of the Rosati form (equivalently, existence for every window length `A > 0` of a count-plus-squares decomposition `½ W(H, H) = c_A(H) + ∑_i L_i(H)²`) is unconditionally equivalent to `RiemannHypothesis`, and fails on `goldenDatum` and `complexFake`.

## Gates
- [x] 0 → 1  in-progress: exact mathematical statements fixed, corpus buildings mapped
- [x] 1 → 2  fully-proven: complete dependency-closed paper proofs
- [ ] 2 → 3  formalized: Lean 4 modules checked cleanly with `lake --old env lean`, standard axioms verified, wired into umbrella modules

## Proofs

### 1. `{∞, 2}` Window Jump-Count and `T₂`-Graph Decomposition (`2a ≤ log 3`)
1. **Endpoint autocorrelation vanishing:** If `tsupport f ⊆ [−a, a]` and `x ≥ 2a`, then `f(u) f(u + x) ≠ 0` implies `u ∈ [−a, a]` and `u + x ∈ [−a, a]`, hence `−a ≤ u ≤ a − x ≤ −a`, forcing `u = −a`. Since `{−a}` has Lebesgue measure zero, `autocorr f x = ∫ f(u) f(u + x) du = 0`.
2. **Closed prime-free and single-prime cutoffs:** By explicit formula evaluation (`re_weilFullFunctional_vonMangoldt_eq_of_supportScale_le`),
   `W(f, f) = Ω(0) ∫ f² + J_∞(f) − 2 ∑_{n=1}^{N+2} (Λ(n)/√n) autocorr f (log n) + 2 poleCross N f`.
   - For `2a ≤ log 2`: every `n ≥ 2` satisfies `2a ≤ log 2 ≤ log n`, so the entire prime sum vanishes.
   - For `2a ≤ log 3`: every `n ≥ 3` satisfies `2a ≤ log 3 ≤ log n`, so only `n = 2` (`Λ(2)/√2 = log 2 / √2`) survives.
3. **`T₂`-graph jump and pole-square identities:**
   - Expanding `∫ (f(u) − f(u + log 2))² du = 2 ∫ f² − 2 autocorr f (log 2)` rewrites `−2 (log 2 / √2) autocorr f (log 2)` as `(log 2 / √2) J_{T₂}(f) − √2 log 2 ∫ f²`. In gauge coordinates `f = M g` supported in `[−a, a]`, `2 g(u) g(u + log 2) = g(u)² + g(u + log 2)² − (g(u) − g(u + log 2))²` isolates the interior `T₂`-graph jump `(log 2 / √2) ∫ M(u) M(u + log 2) (g(u) − g(u + log 2))² du ≥ 0`.
   - Since `autocorr f` is even and vanishes outside `[−2a, 2a] ⊆ [−c, c]`, `2 poleCross N f = 2 ∫_{−∞}^∞ cosh(x/2) autocorr f x dx = 2 ∬ cosh((v − u)/2) f(u) f(v) du dv = 2 coshPairing(f)² − 2 sinhPairing(f)²` via `cosh((v − u)/2) = cosh(u/2) cosh(v/2) − sinh(u/2) sinh(v/2)`.
   - Along any two-hop path `x ↔ x' ↔ y` with positive conductances `c₁, c₂ > 0`, `c₁(g_x − g_{x'})² + c₂(g_{x'} − g_y)² = (c₁ c₂ / (c₁ + c₂))(g_x − g_y)² + (1/(c₁ + c₂))(c₁(g_x − g_{x'}) − c₂(g_{x'} − g_y))²`.

### 2. Variable-Hub / `T₂`-Stick Squares, Positivity Regimes, and Folded-Markov Obstruction
1. **Variable-hub and `T₂`-stick completion of squares:**
   - Pointwise for `w + p ≠ 0`, `w(u − ū)² + p u² = (w + p)(u − w ū / (w + p))² + (w p / (w + p)) ū²`. Integrating against `M(x) ≥ 0` yields the variable-conductance Schur identity.
   - For a `T₂`-coupled pair `(u₁, u₂)` with `d₁₁ = a₁ + w₁ + g₁₂ > 0` and `Δ = d₁₁ d₂₂ − g₁₂² > 0` (`d₂₂ = a₂ + w₂ + g₁₂`), sequential Gaussian completion of squares in `u₁` then `u₂` expresses `a₁ u₁² + w₁(u₁ − ū)² + a₂ u₂² + w₂(u₂ − ū)² + g₁₂(u₁ − u₂)²` as a sum of two manifest linear-form squares plus `((w₁ + w₂) − (d₂₂ w₁² + 2 g₁₂ w₁ w₂ + d₁₁ w₂²)/Δ) ū²`.
2. **Positivity transfers into `LatticeSectionTheory`:**
   - For `f ∈ realTests`, `weilPair f f = fullZeroForm f` (`fullZeroForm_eq_re_weilFullFunctional`). Combining `fullZeroForm_ge_of_support_le_threeTenths` (`a ≤ 3/10`), `fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths` (`a ≤ 181/500` odd), and parity splitting `F = F_even + F_odd` with `polarGroundEnergy_mul_le_fullZeroForm` at `primeTwoAperture` (`2b = log 2 + 1/50`) yields the three unconditional coercivity theorems.
3. **Folded-Markov corner obstruction and `Θ`-translate radical:**
   - If `ω(|x − y|) + ω(x + y) − c₀ cosh(x/2) cosh(y/2) ≥ 0` for all `x, y ∈ (0, a)` with `x ≠ y`, sending `(x, y) → (0, a)` yields `2 ω(a) − c₀ cosh(a/2) ≥ 0`, so `c₀ ≤ 2 ω(a) / cosh(a/2)`. At `a = ½ log 2`, `2 ω(½ log 2) / cosh(¼ log 2) = 8(√2 − 1) < 3.32`; at `a = ½ log 3`, `2 ω(½ log 3) / cosh(¼ log 3) = 3(√3 − 1) < 2.20`. Evaluating the `c₀`-calibrated quadratic form on an explicit smooth even bump inside `(−a, a)` gives a strictly negative value, refuting existence of any positive gauge `M` with pointwise-nonnegative folded jump kernel and potential.
   - For `|b| < ½ log 2`, `lift b` splits into `(lift b + lift (−b))/2 + (lift b − lift (−b))/2`. The second term lies in `signedRadical` directly (`sub_mem_radical`); the first is even (`lift (−b)` is the reflection of `lift b`) and `lift 0` is even, so `(lift b + lift (−b))/2 − lift 0 ∈ signedRadical`, while `weilPair (lift 0) q = 0` by parity against `oddSource` and radical annihilation on `evenSource` (`CHMDThetaTranslateGraph`).

### 3. Multiplicative Scale Group Ring `ℤ[ℚ_{>0}^×]` and Equivalence with `RiemannHypothesis`
1. **Group structure and pullback scaling datum:** Define `PosRatScale` on `{q : ℚ // 0 < q}` with `0 := 1`, `+ := (· * ·)`, `− := (·⁻¹)`. Then `posRatLog : PosRatScale →+ ℝ` (`q ↦ log q`) is injective (`Real.log_injOn_pos` + `Rat.cast_injective`) with dense range (`denseShifts_ratHecke`). Pulling back `zetaScalingDatum` along `posRatLog` gives `zetaPosRatScalingDatum : ScalingDatum PosRatScale ScalingCycle`; similarly `twoPrimeLog p q : ℤ × ℤ →+ ℝ` (`(m, n) ↦ m log p + n log q`) pulls back `zetaScalingDatum` to `ℤ × ℤ`.
2. **Unconditional window count heights:** Whenever `0 ≤ intRosatiForm D x ξ` is established unconditionally (which holds for every correspondence supported on the unconditional window regimes above), `c(ξ) := ⌊intRosatiForm D x ξ⌋₊ : ℕ` satisfies `intRosatiForm D x ξ = (c(ξ) : ℝ) + √(Int.fract (intRosatiForm D x ξ)) ^ 2` and `|(c(ξ) : ℝ) − intRosatiForm D x ξ| ≤ 1` without clamping negative values.
3. **All-cycle and single-orbit equivalences with `RiemannHypothesis`:**
   - Since `(D.pullback φ).toPolarSurface = D.toPolarSurface`, `(D.pullback φ).hodgeIndex_tfae` and `orbitHodgeIndex_iff_exists_naiveHeight` immediately equate `RiemannHypothesis` with existence of a nonnegative naive height (or `ℕ`-valued count height via `⌊q(ξ)⌋₊`) on `PosRatScale →₀ ℤ` (and on `(ℤ × ℤ) →₀ ℤ`) for every `x : ScalingCycle`.
   - Moreover, for any fixed cycle `x` with continuous `D.orbitCorr x` and any `φ : H →+ G` with `DenseRange φ`, fiber-grouping on finite subsets transfers `(D.pullback φ).OrbitHodgeIndex x` to `D.OrbitHodgeIndex x` at that individual cycle `x`.
   - On a single spectrally generic smooth real test `g`, `riemannHypothesis_iff_ratHecke_negIndex_eq_zero` and `riemannHypothesis_iff_twoPrime_negIndex_eq_zero` together with the integer rounding principle `sum_sum_nonneg_of_int` and `exists_naiveHeight_iff_nonneg` equate `RiemannHypothesis` with existence of a nonnegative naive height (or `ℕ`-valued count) on `PosRatScale →₀ ℤ` — and already on `(ℤ × ℤ) →₀ ℤ` for any two distinct primes `p ≠ q` — along the single cycle `diagCycle g`.
