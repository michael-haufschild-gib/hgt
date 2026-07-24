# Elementary PNT with power-log error (infrastructure sub-project)

- **ID:** `elementary-pnt-power-log-error-infrastructure`
- **Stage:** 1-in-progress (formalization infrastructure)
- **Type:** `[BRIDGE]` infrastructure (classical, not candidate-new)
- **Purpose:** supply the single remaining input of
  `weighted-euler-tangent-global-graph-decoupling` (and reusable corpus-wide): primes in every
  short multiplicative window `[X, X(1+Θ(1/(c·log X)))]`, i.e.
  `ψ(x) = x + O(x/(log x)^A)` for every fixed `A` (Bombieri–Wirsing strength; `A ≈ B+2`
  suffices per consumer).  Consumer interface already formalized:
  `RHTower.exists_separated_primeLog_nodes` (needs one prime log per `η`-window) and
  `HTGeometry.norm_le_ray_of_sampled_decay` (node families).
- **Route (elementary, Selberg):**
  1. Dirichlet-algebra Leibniz rule: `(f * g)·log = (f·log) * g + f * (g·log)`.
  2. `Λ·log + Λ*Λ = μ * log²` (from `Λ * ζ = log`, mathlib has `vonMangoldt_mul_zeta`-form).
  3. Hyperbola-method estimate of `Σ_{n≤x} (μ*log²)(n)` → **Selberg symmetry formula**
     `ψ(x)log x + Σ_{n≤x} Λ(n)ψ(x/n) = 2x log x + O(x)`.
  4. Bootstrap the symmetry formula (Erdős–Selberg / Bombieri–Wirsing iteration) to
     `R(x) := ψ(x) − x = O(x/(log x)^A)`.
  5. Short-interval consequence: `ψ(x(1+δ)) − ψ(x) ≥ δx(1−o(1))` for `δ = 1/(log x)^{A−1}` ⇒
     prime (power) in the window; remove prime powers via Chebyshev θ/ψ comparison
     (corpus `MertensFirst.psi_theta_div_le` and mathlib Chebyshev).
- **Status log:**
  - 2026-07-23: card created; step 1 (Leibniz rule) starting.
  - 2026-07-23: **step 1+2 DONE** — `formal/GaloisForLFunctions/RHTower/DirichletLogDerivation.lean`
    (umbrella-registered, `lake build` clean, standard axioms): `pmul_log_mul` (the real-coefficient
    Leibniz rule; the corpus already had the ℂ-form `HTGeometry.logWeight_leibniz` in
    `OperatorTailDirichletMatroid.lean` — the real form is documented as its counterpart, needed
    because `Λ` and `ArithmeticFunction.log` are ℝ-valued), `zeta_pmul_log`, and
    **`vonMangoldt_pmul_log_add_mul_self`** (Selberg's identity `Λ·log + Λ*Λ = (log·log)*μ`).
    NEXT (step 3): summatory hyperbola estimate of `Σ_{n≤x}((log·log)*μ)(n)` toward the Selberg
    symmetry formula; reuse `RHTower.Mertens` summatory tooling (`log_summatory_eq`,
    `sum_log_le/ge`).
  - 2026-07-23: **step 3 brick 1 DONE** —
    `formal/GaloisForLFunctions/RHTower/DirichletSummatorySwap.lean` (umbrella-registered,
    `lake build` clean, standard axioms): **`sum_Icc_mul_apply`** — the general finite hyperbola
    identity `Σ_{n≤N}(f*g)(n) = Σ_{d≤N} f(d)·Σ_{m≤N/d} g(m)` for real arithmetic functions
    (sigma-reindexing of the divisor antidiagonals; corpus previously had only the Λ-count
    `log_summatory_eq` and the ℚ-reciprocal `divisorSummatory_reciprocal_harmonic` special
    cases — both checked before building).  NEXT (step 3 brick 2): `T₂(y) = Σ_{m≤y} log²m
    = y·log²y − 2y·log y + 2y + O(log²y)` (partial-summation analogue of `Mertens.sum_log_le/ge`),
    then the μ-weighted assembly toward the symmetry formula.
  - 2026-07-24: **step 3 brick 2 DONE** — `formal/GaloisForLFunctions/RHTower/LogSquaredSummatory.lean`
    (umbrella-registered, `lake build` clean, standard axioms): `integral_log_sq`
    (`∫₁^y log²t dt = y·log²y − 2y·log y + 2y − 2`), `monotoneOn_log_sq`, and the signed sandwich
    **`le_sum_log_sq` / `sum_log_sq_le`** (`A(N) ≤ T₂(N) ≤ A(N+1)`), pinning `T₂(N) = Σ_{m≤N} log²m`
    to its main term within `O(log²N)`. Corpus audit: no prior `Σ log²m` or `∫ log²` anywhere
    (`PrimeClockFiniteScaling.sum_logStep_sq_le` is squared log *increments*, private);
    `HTGeometry.MonotoneRiemannSum` wraps the same mathlib comparison in absolute-error form —
    cross-referenced in the module header; the signed form here is what the assembly consumes.
    NEXT (step 3 brick 3): μ-weighted hyperbola assembly — apply `sum_Icc_mul_apply` to Selberg's
    identity (`vonMangoldt_pmul_log_add_mul_self`, μ as outer factor), substitute the `T₂` bounds,
    reduce the symmetry formula to `Σ_{d≤x} μ(d)/d·logᵏ(x/d)` (k = 0,1); needs corpus `MertensFirst`
    plus a `|Σ_{d≤x} μ(d)/d| ≤ 1`-type lemma (CHECK CORPUS FIRST: search moebius partial sums).
  - 2026-07-24: **step 3 brick 3a DONE** — `formal/GaloisForLFunctions/RHTower/MoebiusFloorSummatory.lean`
    (umbrella-registered, `lake build` clean, standard axioms): `moebius_floor_summatory`
    (`Σ_{d≤N} μ(d)⌊N/d⌋ = 1`, direct corollary of the corpus swap `sum_Icc_mul_apply` with
    `coe_moebius_mul_coe_zeta`) and **`abs_sum_moebius_div_le_one`** (`|Σ_{d≤N} μ(d)/d| ≤ 1`,
    floor/remainder split; the `d=1` harmonic term absorbs the excess). Corpus search recorded:
    `Mollifier.harmonicFloorMoebiusSum_eq_one` is the ℚ harmonic-weighted analogue (cross-referenced
    in header); mathlib has only pointwise `abs_moebius_le_one` — both statements new.
    NEXT (step 3 brick 3b): μ-weighted hyperbola assembly of the symmetry formula — apply
    `sum_Icc_mul_apply` to `(log·log) * μ` (μ outer via `mul_comm`), substitute the `T₂` sandwich
    (`le_sum_log_sq`/`sum_log_sq_le`) and `abs_sum_moebius_div_le_one` + `MertensFirst` bounds to get
    `Σ_{n≤x} Λ(n)log n + Σ Λ(n)ψ(x/n) = 2x·log x + O(x)` (CHECK CORPUS FIRST: search
    "psi summatory vonMangoldt" and "log div sum" before each new lemma).
  - 2026-07-24: **step 3 brick 3b-i DONE** — `formal/GaloisForLFunctions/RHTower/HarmonicLogMascheroni.lean`
    (umbrella-registered, `lake build` clean, standard axioms):
    **`abs_sum_inv_sub_log_sub_mascheroni_le`** (`|Σ_{i≤N} 1/i − log N − γ| ≤ 1/N`, with
    `γ = Real.eulerMascheroniConstant`) plus the bridge `sum_inv_Icc_eq_ratCast_harmonic`.
    Corpus/mathlib search recorded BEFORE writing: mathlib's `NumberTheory/Harmonic/EulerMascheroni`
    supplies the strict sandwich `eulerMascheroniSeq N < γ < eulerMascheroniSeq' N` — the module is a
    thin extraction (upper error `log(N+1)−log N ≤ 1/N` via `log_le_sub_one_of_pos`); corpus had only
    ℚ-`harmonic` uses (`Mollifier`). This is the harmonic input at the exact precision the
    Tatuzawa–Iseki assembly needs.
    NEXT (step 3 brick 3b-ii): `Σ_{n≤N} log n / n = ½log²N + c + O(log N / N)` (constant exists by
    monotone-bounded telescoping, same pattern as γ; CHECK CORPUS FIRST: search "log div n summatory"
    and mathlib `Mathlib.Analysis.SumIntegralComparisons` antitone versions for `log t / t` beyond
    `t ≥ e`), then the Tatuzawa–Iseki identity itself via `sum_Icc_mul_apply`.
  - 2026-07-24: **step 3 brick 3b-ii DONE** (route revision) — the planned `Σ log n / n` constant
    brick is NOT needed: with the harmonic `O(1/N)` input, the Tatuzawa–Iseki error budget closes via
    `G(x) = O(log²x)` and `Σ_{d≤x} log²(x/d) = O(x)`. The actual engine landed instead:
    `formal/GaloisForLFunctions/RHTower/MoebiusFloorInversion.lean` (umbrella-registered, `lake build`
    clean, standard axioms): **`moebius_floor_inversion`**
    (`Σ_{d≤N} μ(d)·Σ_{m≤⌊N/d⌋} F(⌊N/(dm)⌋) = F(N)` for any `F : ℕ → ℝ`, `N ≥ 1`) — hyperbola
    regrouping by products + Möbius cancellation; generalizes `moebius_floor_summatory` (`F = 1`).
    Corpus search recorded BEFORE writing: no floor-sum inversion anywhere (corpus Möbius inversions
    are Lambert/divisor-sum forms); reused `Mollifier.sum_moebius_divisors` and mirrored the
    `DirichletSummatorySwap` sigma-bijection with roles reversed.
    NEXT (step 3 brick 3c): discrete Tatuzawa–Iseki identity — apply `moebius_floor_inversion` to
    `F·log`-type weights and `vonMangoldt = μ * log` to get
    `Σ_{d≤N} μ(d)·T(⌊N/d⌋) = F(N)log N + Σ_{n≤N} Λ(n)F(⌊N/n⌋) + (floor-log error)` with
    `T(k) = log k·Σ_{n≤k} F(⌊k/n⌋)`; the floor-log discrepancy `log(N/d) − log⌊N/d⌋` sums to
    `O(log² N)` (CHECK CORPUS FIRST: search "vonMangoldt moebius log convolution" — mathlib has
    `vonMangoldt_eq...`? verify `sum_moebius_mul_log_eq` at VonMangoldt.lean:133 as the Λ = −μ*log
    connector).
  - 2026-07-24: **step 3 brick 3c DONE** — `formal/GaloisForLFunctions/RHTower/TatuzawaIsekiIdentity.lean`
    (umbrella-registered, `lake build` clean, standard axioms): **`tatuzawa_iseki`** — the discrete
    Tatuzawa–Iseki identity `Σ_{n≤N} μ(n)(log N − log n)·S(⌊N/n⌋) = F(N)log N + Σ_{k≤N} Λ(k)F(⌊N/k⌋)`
    with `S = floorSummatory F`, EXACT (choosing weights `log N − log n` instead of `log⌊N/n⌋`
    eliminates the floor-log error entirely — route improvement over the card's plan). Plus
    `hyperbola_weight_regroup` (weight-generic product regrouping; `moebius_floor_inversion` is its
    Möbius instance) and `sum_divisorsAntidiagonal_moebius_mul_log` (bridge to mathlib's
    `sum_moebius_mul_log_eq`, i.e. `μ*log = −Λ`). Corpus search recorded before writing: no TI or
    generic regroup existed; connector verified in scratch first.
    NEXT (step 4 start): apply `tatuzawa_iseki` to `F₁(k) = ψ(k)` (`ψ = Σ_{n≤k} Λ(n)`, check corpus
    ChebyshevPsi) and `F₂(k) = k − γ·1 − ...` to derive Selberg's symmetry formula: needs
    (i) `Σ_{n≤N} ψ(⌊N/n⌋) = Σ_{k≤N} log k` (swap, corpus `sum_Icc_mul_apply` with Λ*ζ = log),
    (ii) the LHS bound `|Σ_n μ(n)(log N − log n)(S₁−S₂)(⌊N/n⌋)| = O(N)` from `G = O(log²)` windows.
    CHECK CORPUS FIRST: search "chebyshev psi summatory" and "vonMangoldt_mul_zeta".
  - 2026-07-24: **step 4 brick 4a DONE** — `formal/GaloisForLFunctions/RHTower/SymmetricHyperbolaFloorCount.lean`
    (umbrella-registered, `lake build` clean, standard axioms): **`sum_div_add_sqrt_sq`** — the exact
    lattice reflection `Σ_{d≤N}⌊N/d⌋ + ⌊√N⌋² = 2·Σ_{d≤⌊√N⌋}⌊N/d⌋` (nat arithmetic; range split at
    `⌊√N⌋` + card-bijection swapping the hyperbola strips). Needed because the discrete TI route
    requires Dirichlet's divisor asymptotic with `O(√k)` error for `F₂ = id`. Corpus search recorded:
    no divisor-count or sqrt-hyperbola result existed.
    NEXT (step 4 brick 4b): Dirichlet divisor asymptotic — combine `sum_div_add_sqrt_sq` with
    `abs_sum_inv_sub_log_sub_mascheroni_le` (⌊N/d⌋ = N/d − frac, |Σ_{d≤√N} frac| ≤ √N) to get
    `|Σ_{d≤N}⌊N/d⌋ − N·log N − (2γ−1)·N| ≤ C·√N` (explicit C; note `log ⌊√N⌋` vs `½ log N`
    reconciliation costs `O(√N)` via `⌊√N⌋² ≤ N < (⌊√N⌋+1)²`). CHECK CORPUS FIRST: search
    "fractional part sum bound" before the frac-sum lemma.
  - 2026-07-24: **step 4 brick 4b DONE** — `formal/GaloisForLFunctions/RHTower/DirichletDivisorAsymptotic.lean`
    (umbrella-registered, `lake build` clean, standard axioms): **`abs_sum_div_sub_dirichlet_le`** —
    Dirichlet's divisor asymptotic `|Σ_{d≤N}⌊N/d⌋ − N·log N − (2γ−1)N| ≤ 20·√N` (explicit constant).
    Assembly: `sum_div_add_sqrt_sq` (reflection) + per-floor `|⌊N/d⌋ − N/d| ≤ 1` on the strip +
    `abs_sum_inv_sub_log_sub_mascheroni_le` at `s=⌊√N⌋` + `2log s` vs `log N` reconciliation
    (`≤ 2/s`) + `s ≤ √N`, `N/s ≤ √N+3`. Error budget: `4N/s + 4s ≤ 20√N`.
    The pointwise input for `F₂ = id` in the TI route is now banked: `S_id(k) = k log k + (2γ−1)k + O(√k)`.
    NEXT (step 4 brick 4c): log-summatory sandwich `|Σ_{m≤k} log m − (k log k − k)| ≤ log(k+1) + 1`
    (Stirling-strength, integral comparison exactly as `LogSquaredSummatory` — CHECK CORPUS FIRST:
    MertensFirst.sum_log_le/ge are O(k)-precision, LogSquaredSummatory pattern gives O(log k); mathlib
    `integral_log` exists). Then `S_ψ(k) = Σ_{m≤k} log m` via swap (`Λ*ζ = log`), giving pointwise
    `|S_F(k)| ≤ C√k` for `F = ψ − id + 2γ`, then the TI instantiation → Selberg symmetry formula.
  - 2026-07-24: **step 4 brick 4c DONE** — `formal/GaloisForLFunctions/RHTower/ChebyshevPsiLogSummatory.lean`
    (umbrella-registered, `lake build` clean, standard axioms): `chebyshevPsi` (first named real
    `ψ(k) = Σ_{m≤k} Λ(m)` in the corpus — checked: MertensFirst uses raw sums, CCM coeffs are private
    ℂ), **`floorSummatory_chebyshevPsi`** (`Σ_{d≤N} ψ(⌊N/d⌋) = Σ_{m≤N} log m`, via `sum_Icc_mul_apply`
    + `ζ*Λ = log`; transpose of `MertensFirst.log_summatory_eq`, cross-referenced), and the Stirling
    sandwich **`stirling_le_sum_log` / `sum_log_le_stirling`**
    (`k log k − k + 1 ≤ Σ log m ≤ (k+1)log(k+1) − (k+1) + 1`, integral comparison vs
    `∫₁^y log = y log y − y + 1`).
    All pointwise inputs for the TI instantiation are now banked: S_ψ (this), S_id
    (`abs_sum_div_sub_dirichlet_le`, O(√k)), S_1 (trivial: floorSummatory (const 1) k = k).
    NEXT (step 4 brick 4d): pointwise defect bound — define `F₀(k) = ψ(k) − k + 2γ` (constant fixed by
    Dirichlet: S_ψ − S_id + 2γ·k = O(√k)); prove
    `|floorSummatory F₀ k| ≤ C·√k` (combine the three summatory results; C explicit ≈ 25). Then TI at
    `F₀` gives `|F₀(N)log N + Σ Λ(k)F₀(⌊N/k⌋)| ≤ Σ_{n≤N}(log N − log n)·C√(N/n) = O(N)` — the
    Selberg symmetry formula. CHECK CORPUS FIRST before the `Σ √(N/n)` bound: search
    "sqrt sum antitone" (HTGeometry ImproperAntitoneRiemannSum may apply).
  - 2026-07-24: **step 4 brick 4d DONE** — `formal/GaloisForLFunctions/RHTower/PsiDefectSqrtBound.lean`
    (umbrella-registered, `lake build` clean, standard axioms): `psiDefect` (`F₀ = ψ − id + 2γ`),
    `log_add_one_le_three_sqrt` (`log(k+1) ≤ 3√k`), and the keystone
    **`abs_floorSummatory_psiDefect_le`** (`|Σ_{d≤k} F₀(⌊k/d⌋)| ≤ 24√k`): the ψ part is the Stirling
    sandwich (error ≤ 1 + log(k+1)), the id part is Dirichlet's divisor bound (≤ 20√k), main terms
    cancel exactly. Corpus search recorded: no precedent.
    NEXT (step 4 brick 4e — Selberg symmetry formula): instantiate `tatuzawa_iseki` at `psiDefect`:
    LHS `Σ_n μ(n)(log N − log n)·fS F₀(⌊N/n⌋)` bounded by
    `Σ_n (log N − log n)·24√(N/n) ≤ 24√N·Σ_n log(N/n)/√n ≤ C·N` — needs
    `Σ_{n≤N} log(N/n)·√(N/n) ≤ C·N` or the weaker split
    `√(⌊N/n⌋) ≤ √N/√n` + `Σ_{n≤N} (log N − log n)/√n ≤ C√N` (partial summation / antitone integral
    comparison; CHECK CORPUS FIRST: HTGeometry `ImproperAntitoneRiemannSum`, `MonotoneRiemannSum`).
    RHS gives `F₀(N)log N + Σ Λ(k)F₀(⌊N/k⌋) = ψ(N)log N + Σ Λ(k)ψ(⌊N/k⌋) − Σ Λ(k)⌊N/k⌋ + 2γψ(N)
    − N log N + 2γ log N`; with `Σ Λ(k)⌊N/k⌋ = Σ log m` (MertensFirst.log_summatory_eq!) and
    Chebyshev `ψ(N) ≤ (log 4 + 4)N` (MertensFirst.psi-type bound at :73), the symmetry formula
    `|ψ(N)log N + Σ_k Λ(k)ψ(⌊N/k⌋) − 2N log N| ≤ C·N` follows.
  - 2026-07-24: **step 4 brick 4e-i DONE** — `formal/GaloisForLFunctions/HTGeometry/QuarterRootTelescopeSum.lean`
    (HTGeometry umbrella, `lake build` clean, standard axioms): sqrt-only quarter-power machinery —
    **`sum_inv_quarter_root_cube_le`** (`Σ_{n≤N} 1/(√√n)³ ≤ 4√√N`, telescoping via
    `a⁴−b⁴ = (a−b)(a³+a²b+ab²+b³) ≤ (a−b)4a³`), `quarter_root_inv_cube_le`, and
    `log_le_four_quarter_root_sub_one` (`log x ≤ 4(√√x − 1)`). No rpow, no improper integrals.
    Corpus search recorded: no precedent (only √√2 constants elsewhere).
    NEXT (step 4 brick 4e-ii): the weighted bound
    `Σ_{n≤N} (log N − log n)·√(⌊N/n⌋:ℕ) ≤ 16·N`: per-term
    `(log N − log n) = log(N/n) ≤ 4·√√(N/n)` (4e-i log lemma), `√⌊N/n⌋ ≤ √N/√n = (√√(N/n))²·...`,
    product `≤ 4(√√(N/n))³ = 4(√√N)³/(√√n)³` (needs `√√(x/y) = √√x/√√y` via `Real.sqrt_div`),
    then 4e-i telescope → `≤ 16(√√N)⁴ = 16N`. Then brick 4f: instantiate `tatuzawa_iseki` at
    `psiDefect` with `abs_floorSummatory_psiDefect_le` (24√k) and this bound → Selberg symmetry
    formula with explicit constant.
  - 2026-07-24: **step 4 brick 4e-ii DONE** — `formal/GaloisForLFunctions/RHTower/SelbergWeightSqrtSumBound.lean`
    (umbrella-registered, `lake build` clean, standard axioms): **`sum_log_weight_sqrt_floor_le`**
    (`Σ_{n≤N} (log N − log n)·√⌊N/n⌋ ≤ 16N`) — per-term `log(N/n)·√⌊N/n⌋ ≤ 4(√√N)³/(√√n)³` via the
    4e-i log lemma + `Real.sqrt_div` twice, then the quarter-root telescope.
    NEXT (step 4 brick 4f — SELBERG SYMMETRY FORMULA): combine `tatuzawa_iseki psiDefect N`,
    `abs_floorSummatory_psiDefect_le` (24√k at k = ⌊N/n⌋), `|μ| ≤ 1` ⇒ LHS ≤ 24·16N = 384N... note
    per-term |μ(n)(logN − log n)·fS F₀(⌊N/n⌋)| ≤ (log N − log n)·24·√⌊N/n⌋ — factor 24 rides along:
    total `|F₀(N)log N + Σ_k Λ(k)F₀(⌊N/k⌋)| ≤ 384·N`. Then unfold `F₀ = ψ − id + 2γ` on the RHS:
    `Σ Λ(k)⌊N/k⌋ = Σ_{m≤N} log m` (MertensFirst.log_summatory_eq), `Σ Λ(k) = ψ(N)`
    (chebyshevPsi), Stirling sandwich, Chebyshev `Σ_{d≤n} Λ d ≤ (log 4 + 4)n`
    (MertensFirst:73 — check exact name) ⇒
    **`|ψ(N)·log N + Σ_{k≤N} Λ(k)·ψ(⌊N/k⌋) − 2N·log N| ≤ C·N`** explicit C.
  - 2026-07-25: **step 4 brick 4f-i DONE** — `formal/GaloisForLFunctions/RHTower/SelbergSymmetryCore.lean`
    (umbrella-registered, `lake build` clean, standard axioms): **`abs_psiDefect_selberg_core`**
    (`|F₀(N)log N + Σ_{k≤N} Λ(k)F₀(⌊N/k⌋)| ≤ 384N`, TI at `psiDefect` + termwise 24√k + 16N weight
    bound) and `chebyshevPsi_eq_psi` — bridge to mathlib's `Chebyshev.psi` (real-argument, Ioc form),
    which the earlier corpus check MISSED because it grep'd only the corpus, not mathlib; bridge now
    recorded. NOTE: mathlib's `Chebyshev` file may contain more usable ψ infrastructure (psi_le,
    monotonicity?) — scan it before proving new ψ facts.
    NEXT (step 4 brick 4f-ii — SELBERG SYMMETRY FORMULA, final): unfold `psiDefect = chebyshevPsi −
    id + 2γ` in the core bound:
    `F₀(N)log N = ψ(N)log N − N log N + 2γ log N`;
    `Σ Λ(k)F₀(⌊N/k⌋) = Σ Λ(k)ψ(⌊N/k⌋) − Σ_{m≤N} log m + 2γψ(N)` via
    `log_summatory_eq` (MertensFirst) and `chebyshevPsi`;
    error terms: `|Σ log m − (N log N − N)| ≤ 1 + 3√N` (Stirling sandwich + log_add_one_le_three_sqrt),
    `ψ(N) ≤ (log 4 + 4)N` (`sum_vonMangoldt_Icc_le`), `γ < 2/3`
    (`Real.eulerMascheroniConstant_lt_two_thirds`), `γ > 0` (via one_half_lt), `log 4 ≤ 3`,
    `log N ≤ 3√N ≤ 3N` ⇒
    **`|ψ(N)log N + Σ_{k≤N} Λ(k)ψ(⌊N/k⌋) − 2N log N| ≤ 410N`**.
  - 2026-07-25: **STEP 4 (part 1) COMPLETE — SELBERG'S SYMMETRY FORMULA FORMALIZED** —
    `formal/GaloisForLFunctions/RHTower/SelbergSymmetryFormula.lean` (umbrella-registered,
    `lake build` clean, standard axioms):
    **`selberg_symmetry_formula : |ψ(N)·log N + Σ_{k≤N} Λ(k)·ψ(⌊N/k⌋) − 2N·log N| ≤ 410·N`**,
    fully unconditional, explicit constant. Chain (all this week, all `lake build` clean):
    swap → Selberg identity → T₂/T₁ sandwiches → μ-floor bounds → floor inversion →
    Tatuzawa–Iseki (exact) → hyperbola reflection → Dirichlet divisor O(√N) → ψ-defect 24√k →
    quarter-root telescope → 16N weight bound → 384N core → symmetry formula.
    Connectors used: `Mertens.log_summatory_eq`, `Mertens.sum_vonMangoldt_Icc_le` (namespace
    `RHTower.Mertens`!), mathlib `eulerMascheroniConstant_lt_two_thirds`.
    NEXT (step 4 part 2 — Erdős–Selberg bootstrap): from the symmetry formula derive
    `R(x) = ψ(x) − x` satisfies `|R(N)|log²N ≤ Σ_{k≤N} Λ(k)|R(⌊N/k⌋)|·(log stuff) + O(N log N)`
    (the standard a(x) recursion), then the iteration lemma driving `limsup |R|/x` down to 0 with
    power-log rate `O(x/log^A x)`. This is the longest remaining step (textbook: several pages;
    plan 4-6 bricks: (i) R-recursion from symmetry formula, (ii) |R| subadditive averaging lemma,
    (iii) the log-power iteration, (iv) final `abs_psi_sub_le`). THEN step 5: short-interval primes
    from ψ asymptotic → `exists_separated_primeLog_nodes` discharge → parent card assembly.
    CHECK CORPUS FIRST each brick (search "erdos selberg bootstrap", "psi recursion").
  - 2026-07-25: **step 4 part 2 brick (i) DONE** — `formal/GaloisForLFunctions/RHTower/PsiRemainderRecursion.lean`
    (umbrella-registered, `lake build` clean, standard axioms): `psiRemainder` (`R = ψ − id`),
    `psiDefect_eq_psiRemainder_add`, and **`abs_psiRemainder_recursion`**
    (`|R(N)log N + Σ_{k≤N} Λ(k)R(⌊N/k⌋)| ≤ 400N`) — derived from the 384N core directly (tighter
    than via the symmetry formula), shedding `2γlogN ≤ 4N` and `2γψ(N) ≤ 10N`.
    NEXT (step 4 part 2 brick (ii)): from the recursion, the fundamental inequality
    `|R(N)|·log N ≤ Σ_{k≤N} Λ(k)·|R(⌊N/k⌋)| + 400N` (triangle inequality — trivial corollary,
    fold into brick iii); then the REAL work: (iii-a) `|R(m)| − |R(n)| ≤ Σ_{n<j≤m} Λ(j) + ...`
    Lipschitz-type control of R (ψ monotone ⇒ R(m) − R(n) ∈ [−(m−n), ψ(m)−ψ(n)]), (iii-b) the
    Λ-averaged smoothing that converts `Σ Λ(k)|R(N/k)| ≤ (a + o(1))N log N` into
    `|R| ≤ a'N` with `a' < a` (Erdős–Selberg contraction; textbook Nathanson ch.9 —
    plan: formalize the limsup-free explicit-constant variant: if `|R(k)| ≤ a·k + b·√k` for all
    k ≤ N... this is genuinely the hard iteration — consider instead targeting directly the
    O(x/log^A) variant via repeated application). CHECK CORPUS FIRST: search "limsup contraction
    iteration", "bootstrap decreasing sequence".
  - 2026-07-25: **step 4 part 2 brick (ii) DONE** — `formal/GaloisForLFunctions/RHTower/VonMangoldtLogSummatory.lean`
    (umbrella-registered, `lake build` clean, standard axioms): `sum_vonMangoldt_conv_eq`
    (`Σ(Λ*Λ) = Σ Λ(d)ψ(⌊N/d⌋)`, defeq via `sum_Icc_mul_apply`), Abel bounds
    **`sum_vonMangoldt_mul_log_le` / `le_sum_vonMangoldt_mul_log`**
    (`ψ(N)logN − 7N ≤ Σ Λ(k)log k ≤ ψ(N)logN`, discrete telescope + regroup-by-j), and extracted
    helpers `chebyshevPsi_le_seven`, `log_succ_sub_log_le` (were inlined 3-4× before — REUSE THESE).
    Combined with the symmetry formula these give **Selberg's second-inequality weight evaluation**:
    `Σ_{k≤N}(Λ(k)log k + (Λ*Λ)(k)) = ψ(N)logN + Σ Λψ + O(N) = 2N logN + O(N)` (≤ 417N error).
    NEXT (step 4 part 2 brick (iii)): assemble that evaluation as a theorem
    `|Σ_{k≤N}(Λ log + Λ*Λ)(k) − 2N logN| ≤ 420N`, then the R-form second inequality:
    `|R(N)|log²N ≤ Σ_{k≤N}(Λ(k)logk + (Λ*Λ)(k))·|R(⌊N/k⌋)| + O(N logN)` (apply the 400N recursion
    at N and at each ⌊N/k⌋ — Nathanson Lemma 9.1/9.2 shape). Slow-variation lemma
    (R(m) − R(n) ≥ −(m−n) for n ≤ m; ψ monotone) also still pending — trivial, fold in.
    CHECK CORPUS FIRST each brick.
  - 2026-07-25: **step 4 part 2 brick (iii) DONE** — `formal/GaloisForLFunctions/RHTower/SelbergWeightEvaluation.lean`
    (umbrella-registered, `lake build` clean, standard axioms): **`abs_selberg_weight_summatory`**
    (`|Σ_{k≤N}(Λ(k)log k + (Λ*Λ)(k)) − 2N logN| ≤ 420N`), **`hyperbola_bilinear_regroup`**
    (two-weight regroup; at `g=h=Λ` + `sum_antidiagonal_vonMangoldt_mul` gives
    `Σ_kΛ(k)Σ_jΛ(j)F(⌊N/kj⌋) = Σ_m(Λ*Λ)(m)F(⌊N/m⌋)`), and `psiRemainder_sub_ge` (slow variation
    `R(m)−R(n) ≥ −(m−n)`).
    NEXT (step 4 part 2 brick (iv) — Selberg's SECOND inequality): from the 400N recursion applied
    at N (×logN) and at each fiber ⌊N/k⌋ (weighted by Λ(k)):
    `|R(N)|·log²N ≤ Σ_{m≤N}(Λ(m)log m + (Λ*Λ)(m))·|R(⌊N/m⌋)| + C·N·logN`. Ingredients: recursion
    at fibers |R(⌊N/k⌋)log⌊N/k⌋ + Σ_jΛ(j)R(⌊N/kj⌋)| ≤ 400⌊N/k⌋; sum ×Λ(k):
    `Σ Λ(k)·400·(N/k) ≤ 400N(logN + 8)` via corpus `Mertens.mertens_first`-type bound
    (CHECK exact name/statement: |Σ_{d≤n} Λ(d)/d − log n| ≤ log4+4, MertensFirst:91);
    weight split `Λ(k)logN = Λ(k)log k + Λ(k)log(N/k)` needs `log⌊N/k⌋ vs log(N/k)` care —
    use logN − logk − log⌊N/k⌋ ∈ [0, 1/⌊N/k⌋·…] (⌊N/k⌋ ≤ N/k < ⌊N/k⌋+1 ⇒ difference ≤
    log(1+1/⌊N/k⌋) ≤ 1/⌊N/k⌋); triangle everything.
  - 2026-07-25: **step 4 part 2 brick (iv) DONE — SELBERG'S SECOND INEQUALITY** —
    `formal/GaloisForLFunctions/RHTower/SelbergSecondInequality.lean` (umbrella-registered,
    `lake build` clean, standard axioms): **`selberg_second_inequality`**
    (`|R(N)|log²N ≤ Σ_{m≤N}(Λ(m)log m + (Λ*Λ)(m))|R(⌊N/m⌋)| + 800N logN + 2900N`), plus
    `abs_psiRemainder_le` (`|R(j)| ≤ 8j`) and `vonMangoldt_conv_nonneg`. Proof: recursion at N
    ×logN; per-fiber recursion at ⌊N/k⌋ summed with `Mertens.mertens_first` (400N(logN+7));
    bilinear regroup → (Λ*Λ) weight; floor-log discrepancy ≤ 8 per unit Λ-mass (56N).
    The bootstrap now has: recursion (400N), weight evaluation (420N), second inequality,
    slow variation, |R| ≤ 8j.
    NEXT (step 4 part 2 brick (v) — the contraction): from the second inequality + weight
    evaluation derive: if `|R(⌊N/m⌋)| ≤ a·⌊N/m⌋ + b` for all m (uniform ratio hypothesis), then
    `|R(N)| ≤ a·N·(2NlogN + 420N)/(N log²N)`-type → `|R(N)| ≤ (a + C/logN)·N`?? — that alone
    does NOT contract (gives a back). The contraction needs the sign-change/interval-averaging
    argument (Nathanson 9.3-9.6: R changes sign in [x, e^{C/a}x] windows via Mertens; then
    |R| average over log-window strictly less than a). Plan brick (v): the sign-change lemma —
    ∀ interval [x, Kx] with K = e^{C·...}, ∃ y with |R(y)| ≤ small (uses Mertens Σ Λ/k = logN+O(1)
    two-sided + slow variation). CHECK CORPUS FIRST: search "sign change window remainder".
  - 2026-07-25: **step 4 part 2 brick (v) DONE** — two modules:
    `formal/GaloisForLFunctions/HTGeometry/DiscreteSignCrossing.lean` (HTGeometry umbrella):
    **`exists_mul_succ_nonpos`** — discrete sign-crossing (f(a)f(b) ≤ 0 ⇒ consecutive crossing);
    `formal/GaloisForLFunctions/RHTower/PsiRemainderSignChange.lean` (RHTower umbrella; both
    `lake build` clean, standard axioms): `psiRemainder_succ_sub` (exact step `R(j+1)−R(j) =
    Λ(j+1)−1`), **`exists_abs_psiRemainder_le_of_sign_change`** (sign change in [a,b] ⇒
    ∃m∈[a,b], |R(m)| ≤ log b + 1 — down-crossings land within 1 of zero, up-crossings start within
    log(m+1)−1), and `abs_floorSummatory_psiRemainder_add_le` (`|Σ_{n≤N}R(⌊N/n⌋) + 2γN| ≤ 24√N`).
    NEXT (step 4 part 2 brick (vi) — forcing sign changes): show R must change sign (or be small)
    in every window [y, Ky] for suitable K: route — Mertens two-sided
    `|Σ_{d≤n}Λ(d)/d − log n| ≤ 7` gives `Σ_{y<d≤z} Λ(d)/d ≥ log(z/y) − 14`; if R > δt on all of
    [y,z] (no sign change, R positive), integrate/партial-sum ψ(t) ≥ t + δt against ... derive
    contradiction with mertens-type upper bound when log(z/y) large (Nathanson 9.4: uses
    Σ_{n≤x}R(x/n) = O(x) instead — we HAVE `abs_floorSummatory_psiRemainder_add_le`: if R ≥ δ⌊N/n⌋
    for all fibers in a range... the fibers ⌊N/n⌋ sweep all values — pick the route: constant-sign
    on [1,N]... needs care; plan on paper first next iteration). CHECK CORPUS FIRST.
  - 2026-07-26: **step 4 part 2 brick (vi-a) DONE** — `formal/GaloisForLFunctions/RHTower/PsiRemainderHarmonicSum.lean`
    (umbrella-registered, `lake build` clean, standard axioms): **`abs_sum_psiRemainder_harmonic_le`**
    (`|Σ_{n≤N} R(n)(1/n − 1/(n+1))| ≤ 20` — the discrete `∫R(t)/t²dt = O(1)`), via
    `sum_reciprocal_telescope` and `sum_chebyshevPsi_harmonic_eq` (Abel:
    `Σψ(n)(1/n−1/(n+1)) = ΣΛ(k)/k − ψ(N)/(N+1)`), Mertens, harmonic-γ at N+1, `ψ ≤ 7N`.
    NEXT (step 4 part 2 brick (vi-b) — the window small-value theorem): windowed difference
    `|Σ_{y<n≤z} R(n)(1/n − 1/(n+1))| ≤ 40`; if δ > 0 and |R(n)| ≥ δn with CONSTANT SIGN on
    (y, z] then Σ ≥ δ·Σ_{y<n≤z} n/(n(n+1)) = δ(H_{z+1}−H_{y+1}) ≥ δ(log(z/y) − 2) ⇒
    `log(z/y) ≤ 40/δ + 2`. Contrapositive + sign-change lemma
    (`exists_abs_psiRemainder_le_of_sign_change`) ⇒ **∀ y, δ: ∃ m ∈ [y, y·e^{40/δ+2}] with
    |R(m)| ≤ max(δm, log m + 1)** — the small-value supply. Then brick (vii): the contraction
    iteration feeding small-value windows into `selberg_second_inequality` fiber sums.
  - 2026-07-26: **step 4 part 2 brick (vi-b) DONE — THE WINDOW SMALL-VALUE THEOREM** —
    `formal/GaloisForLFunctions/RHTower/PsiRemainderWindowSmallValue.lean` (umbrella-registered,
    `lake build` clean, standard axioms): **`exists_small_psiRemainder_in_window`**
    (δ > 0, 1 ≤ y ≤ z, `log z − log y > 40/δ + 2` ⇒ ∃ m ∈ (y,z], |R(m)| ≤ δm + log z + 1), via
    `abs_windowed_psiRemainder_harmonic_le` (windowed J ≤ 40) and `sum_inv_succ_window_ge`
    (`Σ_{(y,z]} 1/(n+1) ≥ log(z/y) − 2`); trichotomy: |R| < δ·id somewhere / sign change
    (crossing lemma) / constant sign (contradicts the 40-bound).
    The small-value supply for the contraction is COMPLETE. Remaining for
    `ψ(x) = x + O(x/log^A x)`: brick (vii) — the contraction iteration: define
    `a_j := limsup-free uniform ratio bound on [N_j, ∞)`; use `selberg_second_inequality` +
    `abs_selberg_weight_summatory` + small-value windows + slow variation (`psiRemainder_sub_ge`)
    to prove the ratio recursion `a_{j+1} ≤ a_j − c·a_j³` (or the log-power variant); then the
    numeric iteration lemma. This is 2-3 more bricks (the iteration lemma is generic — put in
    HTGeometry). CHECK CORPUS FIRST: search "iteration decreasing cubic recursion limit".
  - 2026-07-26 (addendum, user-prompted corpus audit): retroactive search on brick (vi-b) FOUND a
    partial duplication — `LegStripThreshold.harmonic_log_upper` already provides the sharp harmonic
    tail bound `log((i+k)/i) ≤ Σ_{j<k}1/(i+j)`. `sum_inv_succ_window_ge` REFACTORED to derive from
    it by reindexing (offset y+2); ~55 lines of hand-rolled telescope deleted. Module re-audited:
    `lake build` clean, standard axioms. LESSON REINFORCED: run the explicit corpus query before
    EVERY lemma, including ones assembled "only from my own recent modules" — harmonic/telescope
    material is spread across old corpus files (LegStripThreshold, Mertens, Mollifier).
  - 2026-07-26: **step 4 part 2 brick (vii-a) DONE** — `formal/GaloisForLFunctions/RHTower/VonMangoldtLogHarmonicSummatory.lean`
    (umbrella-registered, `lake build` clean, standard axioms):
    **`abs_sum_vonMangoldt_log_div_sub_le`** (`|Σ_{m≤N} Λ(m)log m/m − ½log²N| ≤ 15logN + 1`) via
    partial summation against Mertens; helpers `sum_inv_sq_le` (finite Basel ≤ 2, via
    `sum_reciprocal_telescope` — corpus-searched first: PrimeClockFiniteScaling's variant is weaker
    and private), `sum_log_increment_eq`, `sum_log_sq_increment_eq` (telescopes).
    ROUTE NOTE (major simplification, recorded during planning): the parent card's node supply
    needs only FIXED relative window width (δ = 1/(4(deg+1)) per instance), so ψ(x) = x + o(x)
    (limsup|R|/x = 0, qualitative Erdős–Selberg) SUFFICES — no power-log rate needed. Target
    statement: ∀ ε > 0, ∃ x₀, ∀ x ≥ x₀, |R(x)| ≤ εx.
    NEXT (brick (vii-b)): the other half of the weight: `Σ_{m≤N}(Λ*Λ)(m)/m = ½log²N + O(logN)` —
    define AF `f := Λ/id` (f*f)(m) = (Λ*Λ)(m)/m (antidiag per-term, ab=m ⇒ 1/(ab)=1/m), swap
    (`sum_Icc_mul_apply`) → Σ_a(Λ(a)/a)·M(⌊N/a⌋), Mertens + log⌊N/a⌋ discrepancy (≤ 2Λ(a)/N sum
    ≤ 14) + THIS brick's L1 → ½log²N + O(logN). Then Σw(m)/m = log²N + O(logN) combined.
  - 2026-07-26: **step 4 part 2 brick (vii-b) DONE** — `formal/GaloisForLFunctions/RHTower/VonMangoldtConvHarmonicSummatory.lean`
    (umbrella-registered, `lake build` clean, standard axioms): `vonMangoldtDiv` (AF `Λ/id`),
    `vonMangoldtDiv_mul_apply` (`(Λ/id)*(Λ/id) = (Λ*Λ)/id`), and
    **`abs_sum_vonMangoldt_conv_div_sub_le`** (`|Σ(Λ*Λ)(m)/m − ½log²N| ≤ 30logN + 120`) — swap +
    three-way Mertens split + (vii-a) + floor-discrepancy `2ψ(N)/N ≤ 14`.
    **The fiber-averaged Selberg weight is now fully evaluated**:
    `Σ_{m≤N}(Λ(m)log m + (Λ*Λ)(m))/m = log²N + O(logN)` (combine (vii-a) + (vii-b): ≤ 45logN + 121).
    NEXT (brick (viii) — the contraction core): with W(m) := Λ(m)logm + (Λ*Λ)(m) ≥ 0, weight
    evaluation `ΣW = 2NlogN + O(N)` (420N banked), fiber weight `ΣW/m = log²N + O(logN)` (banked),
    second inequality (banked), small-value windows (banked), slow variation (banked): derive the
    ratio-improvement step: if ∀ k ∈ [K₀, N], |R(k)| ≤ a·k, then |R(N)| ≤ (a − c(a))·N + o-terms,
    where c(a) > 0 from replacing |R(⌊N/m⌋)| ≤ a⌊N/m⌋ by the small-value windows on a
    positive-proportion set of fibers. PLAN ON PAPER FIRST (numerically pre-certify the window
    bookkeeping with mpmath per CLAUDE.md before writing Lean). CHECK CORPUS FIRST.
  - 2026-07-26: **step 4 part 2 brick (viii-a) DONE — THE GAIN ENGINE** —
    `formal/GaloisForLFunctions/RHTower/PsiRemainderOneSidedWindowAverage.lean` (umbrella-registered,
    `lake build` clean, standard axioms): **`sum_abs_psiRemainder_window_le_of_lower`**
    (`R ≥ −ε·id` on `(y,z]` ⇒ `Σ|R(n)|w(n) ≤ 40 + 2ε(log(z/y)+1)`, via `|x| = x + 2max(−x,0)` +
    windowed 40-bound + negative-part ≤ εn), with `sum_inv_succ_window_le` and
    `inv_succ_le_log_succ_sub` (`1/(n+1) ≤ log(n+1)−logn`). Numerically pre-certified.
    This replaces the trivial `a·log(z/y)` fiber average by a CONSTANT on windows above small-value
    points — the strict improvement the contraction extracts.
    NEXT (brick (viii-b) — window chaining): combine `exists_small_psiRemainder_in_window` (supply of
    small points m₀ every `40/δ + 2` log-units) + `psiRemainder_sub_ge` (slow variation: for
    n ∈ (m₀, (1+ρ)m₀]: R(n) ≥ R(m₀) − (n − m₀) ≥ −δm₀ − logz − 1 − ρm₀ ≥ −(δ+ρ)n − logz − 1 —
    NOTE the additive `log z + 1` must be absorbed: use ε' := δ + ρ + (log z + 1)/y on the window)
    ⇒ on `(m₀, (1+ρ)m₀]`: gain-engine applies with ε' ⇒ partition ANY long window `(Y, 2^k Y]` into
    gain-windows + trivial-windows and average: `Σ_{Y<n≤Z}|R|w ≤ (a·(1 − θ) + Cε')·log(Z/Y) + ...`
    with θ = ρ/(40/δ + 2 + ρ) — the density of gain-coverage. PLAN the exact partition on paper +
    mpmath first. Then (viii-c): transfer fiber sum Σ W(m)|R(⌊N/m⌋)| to window form (the m ↦ ⌊N/m⌋
    bookkeeping — hardest remaining step; consider instead proving the contraction directly for the
    HARMONIC average A(x) := Σ_{n≤x}|R(n)|w(n)/log-normalized and connecting to the second
    inequality via ⌊N/m⌋-fibers ≈ harmonic distribution).
  - 2026-07-27: **DEAD ROUTE (recorded before Lean)** — the (viii-b) plan "chain gain-engine windows"
    FAILS quantitatively: per-window gain ≤ a·ρ' ≤ a·log(1+a/4) ≤ a²/4 ≤ 16, but the gain engine
    carries +40 (windowed-J constant) per window ⇒ net gain negative for ALL a ≤ 8. mpmath check
    confirms. The 40 cannot be shrunk (J-bound is genuinely O(1)).
    **CORRECTED ROUTE**: elementary window-Chebyshev via binomial coefficients:
    `Σ_{p prime ∈ (x,y]} log p ≤ log C(y, y−x) ≤ (y−x)(log y − log(y−x) + 1)` (for y ≤ 2x; primes
    in the window divide the binomial; Stirling lower via banked `stirling_le_sum_log`). This gives
    the missing UPPER slow variation: ψ(t) − ψ(m₀) ≤ (t−m₀)(1 + log(t/(t−m₀))) + O(√t log t) ⇒
    around every small point, |R| ≤ ε(ρ)·t POINTWISE two-sided on relative-ρ windows,
    ε(ρ) = δ + ρ(2 + log(1/ρ)) + o(1) — no +40 anywhere; contraction gain (a − ε(ρ))ρ > 0 for
    ρ small ∝ a. The one-sided gain engine (viii-a) remains useful as a fallback but is NOT on the
    critical path.
  - 2026-07-27: **step 4 part 2 brick (viii-b′) DONE — BINOMIAL WINDOW-CHEBYSHEV** —
    `formal/GaloisForLFunctions/RHTower/PrimeWindowBinomialBound.lean` (umbrella-registered,
    `lake build` clean, standard axioms): **`sum_primes_log_window_le`**
    (`x < y ≤ 2x` ⇒ `Σ_{p prime∈(x,y]} log p ≤ (y−x)(log y − log(y−x) + 1)`; primes in the window
    divide `C(y, y−x)` via `Nat.Prime.dvd_choose` + `Finset.prod_primes_dvd`), with
    `log_choose_le` (`log C(y,k) ≤ k(log y − log k + 1)` via descFactorial + banked Stirling) and
    `log_factorial_eq` (`log k! = Σ log m`). Numerically certified (200 random cases).
    NEXT (brick (viii-c)): the ψ-window upper — extend to ψ: prime powers p^j ∈ (x,y] with j ≥ 2
    contribute ≤ 2√y·log y (count ≤ 2√y crude); yields
    `ψ(y) − ψ(x) ≤ (y−x)(log y − log(y−x) + 1) + 2√y log y` — then two-sided pointwise slow
    variation around small points: for m₀ small (|R(m₀)| ≤ δm₀ + logz + 1) and t ∈ (m₀, (1+ρ)m₀]:
    `R(t) ≤ R(m₀) + ψ(t) − ψ(m₀) ≤ δm₀ + ρm₀(log(1/ρ)+2) + O(√t log t)` and
    `R(t) ≥ R(m₀) − (t − m₀)` ⇒ `|R(t)| ≤ ε(ρ)t + o(t)` POINTWISE, ε(ρ) := δ + ρ(log(1/ρ) + 3).
    Then (viii-d): the fiber-average contraction using pointwise-small windows (no +40 anywhere).
  - 2026-07-27: **step 4 part 2 brick (viii-c) DONE — TWO-SIDED POINTWISE SLOW VARIATION** —
    `formal/GaloisForLFunctions/RHTower/PsiWindowUpperBound.lean` (umbrella-registered, `lake build`
    clean, standard axioms): `theta_window_eq` (θ-window = window prime log-sum),
    **`chebyshevPsi_window_le`** (`x < y ≤ 2x` ⇒ `ψ(y) − ψ(x) ≤ (y−x)(logy − log(y−x) + 1) +
    2√y·logy` — binomial bound + MATHLIB's `Chebyshev.psi_sub_theta_le`, found by search: NO
    prime-power counting needed), and **`abs_psiRemainder_le_of_window`**
    (`m₀ ≤ t ≤ 2m₀` ⇒ `|R(t)| ≤ |R(m₀)| + (t−m₀)(logt − log(t−m₀) + 2) + 2√t·logt`).
    Combined with `exists_small_psiRemainder_in_window`: around every small point, |R| ≤ ε(ρ)·t
    pointwise on relative-ρ windows. The corrected contraction route is fully supplied.
    NEXT (brick (viii-d) — THE CONTRACTION): assemble: given a := uniform ratio bound on [K₀, N],
    choose δ := a/8, ρ with ρ(log(1/ρ)+3) ≤ a/4; partition fibers of the second inequality into
    blocks; on gain-blocks (small point + window) use pointwise ε(ρ) ≤ a/2; coverage θ(a) =
    ρ/(40/δ + 2 + ρ); derive `limsup-ratio recursion a' ≤ a(1 − θ/2) + o(1)` ⇒ limsup = 0. PLAN
    the fiber-partition bookkeeping on paper + mpmath FIRST (the m ↦ ⌊N/m⌋ transfer with W-weights:
    use Σ W(m)/m = log²N + O(logN) banked evaluations on block ranges).
  - 2026-07-27: **step 4 part 2 brick (viii-d1) DONE** — `formal/GaloisForLFunctions/RHTower/SelbergWeightBlockMass.lean`
    (umbrella-registered, `lake build` clean, standard axioms): `abs_sum_selbergWeight_div_sub_le`
    (`|ΣW(m)/m − log²N| ≤ 45logN + 121`), **`abs_selbergWeight_block_sub_le`** (block mass
    `log²M' − log²M ± (90logM' + 242)`), **`filter_fiber_eq_Ioc`** (fiber-block identity:
    `{m ≤ N : c < ⌊N/m⌋ ≤ c'} = Ioc ⌊N/(c'+1)⌋ ⌊N/(c+1)⌋` — omega needs explicit `Nat.mul_comm`
    bridges for variable products, noted for future div-identities).
    NEXT (brick (viii-d2)): the per-fiber-block bound: for a fiber block (c, c'] with sup-ratio
    hypothesis `∀ t ∈ Ioc c c', |R t| ≤ s·t`:
    `Σ_{m∈Ioc ⌊N/(c'+1)⌋ ⌊N/(c+1)⌋} W(m)|R(⌊N/m⌋)| ≤ s·N·Σ_{same} W(m)/m` (pointwise:
    W(m)|R(⌊N/m⌋)| ≤ W(m)·s·⌊N/m⌋ ≤ s·N·W(m)/m), then combine with block-mass evaluation.
    After that (viii-d3): the block-decomposition of the full fiber sum via `filter_fiber_eq_Ioc`
    partition of (0, N] fibers, gain-block selection, and the ratio recursion.
  - 2026-07-27: **step 4 part 2 brick (viii-d2) DONE** — two modules (both umbrella-registered,
    `lake build` clean, standard axioms):
    `formal/GaloisForLFunctions/HTGeometry/IocPartitionSum.lean`: **`sum_Ioc_partition`**
    (antitone cuts `d` tile: `Σ_{k<K} Σ_{Ioc (d(k+1)) (d k)} f = Σ_{Ioc (d K) (d 0)} f`);
    `formal/GaloisForLFunctions/RHTower/SelbergFiberBlockBound.lean`: **`fiber_block_weighted_le`**
    (ratio ≤ s on fiber block (c,c'] ⇒ block fiber-sum ≤ s·N·(block W/m-mass); uses
    `filter_fiber_eq_Ioc` membership + `⌊N/m⌋ ≤ N/m`).
    Contraction assembly state: with cuts c_k in fiber space, m-cuts d_k := ⌊N/(c_k+1)⌋ are antitone
    (Nat.div_le_div_left), `sum_Ioc_partition` splits the second-inequality fiber sum into blocks,
    each priced by `fiber_block_weighted_le` + `abs_selbergWeight_block_sub_le`.
    NEXT (brick (viii-d3)): the assembled block decomposition theorem: for any antitone fiber cuts
    `0 = c_0 < ... < c_K = N` and per-block ratio bounds `s_k`:
    `Σ_{m≤N} W(m)|R(⌊N/m⌋)| ≤ N·Σ_k s_k·(log²-increment_k + 90logN + 242) + edge terms` —
    then (viii-d4) instantiate cuts: uniform-a blocks + gain blocks (small-value + pointwise window
    ⇒ s = a/2 on gain blocks) ⇒ ratio recursion.
  - 2026-07-27: **step 4 part 2 brick (viii-d3) DONE** — `formal/GaloisForLFunctions/RHTower/SelbergBlockDecomposition.lean`
    (umbrella-registered, `lake build` clean, standard axioms): **`fiber_sum_block_decomposition`**
    (increasing fiber cuts + per-block ratio bounds ⇒ fiber sum ≤ N·Σ_k s_k·(m-block W/m-mass)) and
    **`selberg_second_block_form`** (substituted into the second inequality:
    `|R(N)|log²N ≤ N·Σ_k s_k·mass_k + 800NlogN + 2900N`).
    THE STRUCTURAL SKELETON OF THE CONTRACTION IS COMPLETE. Remaining, all quantitative
    instantiation: (viii-d4) choose cuts — uniform blocks of fiber-log-length L(δ) = 40/δ + 2 + ρ',
    each containing a gain sub-block (small point + `abs_psiRemainder_le_of_window` ⇒ ratio ≤
    δ + ρ(log(1/ρ)+3) + o(1) there, ratio a elsewhere); evaluate masses via
    `abs_selbergWeight_block_sub_le`; per-block K ≈ log N/L blocks, error K·(90logN+242) ≪ log²N
    for L fixed as N → ∞ ⇒ recursion `a' ≤ a − (a − ε)·ρ'·(2·avg(1−β)) /L + o(1)`. (viii-d5) the
    numeric iteration ⇒ ∀ε ∃x₀ ∀x≥x₀ |R(x)| ≤ εx. PLAN (viii-d4) cut bookkeeping on paper+mpmath
    first — it is the last hard step.
  - 2026-07-28: **step 4 part 2 brick (viii-d4-i) DONE — GAIN-WINDOW EXISTENCE** —
    `formal/GaloisForLFunctions/RHTower/PsiRemainderGainWindow.lean` (umbrella-registered,
    `lake build` clean, standard axioms): `mul_log_ratio_mono` (algebraic monotonicity of
    `u ↦ u(log t − log u + 2)` via `log(u₂/u₁) ≤ u₂/u₁ − 1` — no calculus) and
    **`exists_pointwise_small_window`** (`log Q > 40/δ + 2` ⇒ ∃ m₀ ∈ (Y, QY], ∀ t ∈
    [m₀, (1+ρ)m₀]: `|R(t)| ≤ (δ + ρ(log(1/ρ)+3))t + (log(QY)+1) + 2√t·log t`). Numerically
    certified before writing.
    NEXT (brick (viii-d4-ii) — the cut construction): given uniform ratio `a` above `x₀`, define
    the explicit cut sequence: fiber cuts at Y_j := x₀·(2Q)^j-type geometric blocks, each block
    (Y_j, Q·Y_j] supplying m₀(j) with gain window (m₀, (1+ρ)m₀]; cuts per block:
    c: Y_j < m₀ < ⌈(1+ρ)m₀⌉ ≤ 2QY_j = Y_{j+1}: 4 cuts per block; ratios: s = a off-gain,
    s = 3a/8 + junk/t ≤ a/2 on gain (choose δ = a/8, ρ := ρ(a) with ρ(log(1/ρ)+3) ≤ a/8,
    absorb junk ≤ a/8·t for t ≥ T₁(a, Q)). Feed `selberg_second_block_form`; evaluate masses
    (`abs_selbergWeight_block_sub_le`): gain-block mass ≥ log(1+ρ)·(2log(N/Y_{j+1})+...) —
    lower bounds on block masses needed (mass ≥ increment − error). Sum over j; coverage
    fraction ρ'/(log(2Q)) ⇒ recursion `a' ≤ a(1 − ρ'/(2log(2Q))) + o(1)`. This is one big
    theorem + a numeric-iteration lemma (viii-d5). PLAN the exact statement first next iteration.
  - 2026-07-28: **SECOND DEAD-ROUTE ANALYSIS (paper, before Lean)** — the (viii-d4-ii) W-mass cut
    plan fails like the first: per-block mass evaluations carry Mertens-type O(logN) errors while
    gain blocks carry only ρ'·logN mass (ρ' ≪ 1); grouping by ratio value still needs LOWER bounds
    on gain-union W-mass = prime mass in short windows = PNT-circular. CORRECTED ARCHITECTURE
    (σ-route, Nathanson-faithful, discretized):
    (A) sharp window harmonic bounds, error O(1/y) NOT O(1) (the crude ±2 versions are useless at
        gain-window scale; errors then sum geometrically over the ladder);
    (B) σ(N) := Σ_{n≤N}|R(n)|(1/n − 1/(n+1)) ladder contraction: geometric blocks (Y_j, 2Q·Y_j],
        gain windows via `exists_pointwise_small_window`, harmonic masses exact by (A) ⇒
        σ(N) ≤ (a − (a−ε)ρ'/(2log2Q))·logN + O_Q(1);
    (C) fiber transfer: Σ_m W(m)|R(⌊N/m⌋)| ≤ 2NlogN·σ(N) + O(NlogN): Abel against
        V(t) = Σ_{m≤t}W(m) = 2tlogt ± 420t (banked) ONCE globally; variation term controlled by
        Σ_n logn·(ψ(N/n)−ψ(N/(n+1))) = O(N) via Abel-back + ψ ≤ 7t (Σψ(N/n)/n ≤ 7N·H'' hmm — ≤
        7NΣ1/n² fine); small-m head m < 1/ρ absorbed as O_ρ(N·log²(1/ρ)).
    Then (viii-d5) recursion+iteration as before. THIS iteration ships (A).
  - 2026-07-28: **σ-route brick (A) DONE** — `formal/GaloisForLFunctions/RHTower/WindowHarmonicSharpBounds.lean`
    (umbrella-registered, `lake build` clean, standard axioms): **`abs_sum_inv_succ_window_sub_le`**
    (`|Σ_{(y,z]} 1/(n+1) − log(z/y)| ≤ 2/y`) and **`abs_sum_inv_window_sub_le`**
    (`|Σ_{(y,z]} 1/n − log(z/y)| ≤ 1/y`) — O(1/y) errors, geometric-ladder-summable; plus
    `sum_log_inc_window` telescope. (Lean note: linarith needs `2/y = 1/y + 1/y` bridge — division
    atoms don't auto-combine.)
    NEXT (σ-route brick (B) — the σ-ladder contraction): σ-window bound per gain block:
    on (m₀, ⌊(1+ρ)m₀⌋]: Σ|R(n)|(1/n − 1/(n+1)) ≤ ε_eff·(harmonic mass) with ε_eff from
    `exists_pointwise_small_window` (junk absorbed for Y ≥ T₁); per non-gain block: trivial
    a·mass; ladder Y_j = Y₀(2Q)^j, j < J := Nat.log (2Q) (N/Y₀); assemble:
    σ(N) − σ(Y₀) ≤ a(logN − logY₀) − (a − ε)·ρ'·J + Σ_j O(1/Y_j) errors ⇒
    σ(N) ≤ (a − (a−ε)ρ'/(2log(2Q)))·logN + C(Q, Y₀). Then (C) the fiber transfer.
  - 2026-07-28: **σ-route brick (B1) DONE — THE PER-BLOCK σ-CONTRACTION** —
    `formal/GaloisForLFunctions/RHTower/SigmaBlockContraction.lean` (umbrella-registered,
    `lake build` clean, standard axioms): **`sigma_block_contraction`** — on a ladder block
    `(Y, 2QY]` with uniform ratio `a` above `x₀ ≤ Y` (and `Y ≥ 2/ρ`, `logQ > 40/δ + 2`,
    junk-absorption `κ`, `ε' := δ + ρ(log(1/ρ)+3) + κ ≤ a`):
    `Σ_{block}|R(n)|w(n) ≤ a·(log(2QY) − logY) − (a − ε')·ρ/3 + 6a/Y`.
    Fixed per-block gain, geometrically summable boundary error — exactly what the two dead
    W-routes lacked. (Lean notes: `-(x)/y` vs `-(x/y)` are distinct linarith atoms — ring-bridge;
    maxHeartbeats 1000000 needed for the 250-line proof.)
    NEXT (σ-route brick (B2) — the ladder): iterate over j < J := blocks of (x₁, N]:
    Y_j := x₁·(2Q)^j; Σ_j block-bounds + sharp bounds on the head (1, x₁] (trivial 8-ratio) and
    tail (Y_J, N] (ratio a) ⇒ `σ(N) ≤ a·logN − (a−ε')·(ρ/3)·J + 6a·Σ1/Y_j + C(x₁)` with
    J ≥ (log(N/x₁)/log(2Q)) − 1 ⇒ σ(N) ≤ (a − θ)·logN + C', θ := (a−ε')ρ/(3·log(2Q) ·... wait
    per-block gain is ABSOLUTE (ρ/3-sized), J blocks ⇒ total gain (a−ε')(ρ/3)·J ~ linear in logN ✓.
    Then (C) fiber transfer, (D) recursion+iteration.
  - 2026-07-28: **σ-route brick (B2) DONE — THE σ-LADDER CONTRACTION** —
    `formal/GaloisForLFunctions/RHTower/SigmaLadderContraction.lean` (umbrella-registered,
    `lake build` clean, standard axioms): **`sigma_ladder_contraction`** — for the geometric ladder
    `Y_j = x₁(2Q)^j`: `Σ_{x₁<n≤x₁(2Q)^J}|R(n)|w(n) ≤ a·(log(x₁(2Q)^J) − log x₁) − (a−ε')(ρ/3)·J
    + a·Σ_{j<J}6/(x₁(2Q)^j)` — full unit of gain per block, junk-absorption propagates up the
    ladder (`log(Q·Y)` grows by `log2Q` while the base doubles).
    σ-CONTRACTION STRUCTURALLY COMPLETE. Remaining bricks: (B3) tidy corollary — geometric error sum
    ≤ 12/x₁ + head (1, x₁] crude bound + J ≥ log(N/x₁)/log(2Q) − 1 (Nat.log or explicit) ⇒
    `σ(N) ≤ (a − θ(a))·log N + C(a, x₁)` with θ := (a−ε')ρ/(6log(2Q)); (C) the fiber transfer
    `Σ W(m)|R(⌊N/m⌋)| ≤ 2NlogN·σ(N) + O(NlogN)` (Abel vs V(t) = 2tlogt ± 420t ONCE, variation
    term via Σ logn·Δψ-fibers = O(N)); (D) recursion `a ↦ a − θ(a)·(a-θ-scale)` via second
    inequality; (E) iteration to ∀ε ∃x₀: |R| ≤ εx. Then step 5: short-window primes from
    ψ ~ x ⇒ node discharge ⇒ PARENT CARD assembly.
  - 2026-07-29: **σ-route brick (B3) DONE — THE σ-CONTRACTION IN CLOSED FORM** —
    `formal/GaloisForLFunctions/RHTower/SigmaContractionCorollary.lean` (umbrella-registered,
    `lake build` clean, standard axioms): **`sigma_window_contraction_of_ratio`** — for any N ≥ x₁
    (ladder height J := Nat.log (2Q) (N/x₁)):
    `Σ_{x₁<n≤N}|R(n)|w(n) ≤ (a − g/L)·(logN − logx₁) + (g + 14a/x₁)`,
    g := (a−ε')ρ/3, L := log(2Q). The contraction rate θ = g/L is strictly positive whenever
    ε' < a. (Lean notes: omega needs mul_comm bridges around Nat.log/div products; `set` doesn't
    abstract later-derived hypotheses — rw [← hdef] before final linarith.)
    THE σ-SIDE OF THE ERDŐS–SELBERG ARGUMENT IS COMPLETE. Remaining: (C) the fiber transfer
    `Σ_m W(m)|R(⌊N/m⌋)| ≤ 2NlogN·(σ-total) + O(NlogN)` — LAST technical brick (plan: Abel against
    V(t) = Σ_{m≤t}W(m) with banked `abs_selberg_weight_summatory` 420N evaluation; variation term
    via `Σ_n logn·(ψ(N/n) − ψ(N/(n+1))) = O(N)` Abel-back trick); (D) recursion a ↦ a(1 − c(a));
    (E) iteration. CHECK CORPUS FIRST each.
  - 2026-07-29: **σ-route brick (C2) DONE — THE DISCRETE FUBINI** —
    `formal/GaloisForLFunctions/RHTower/WeightedSigmaFubini.lean` (umbrella-registered, `lake build`
    clean, standard axioms): `sigmaPartial` (exported σ(s) def), **`weighted_sigma_eq`**
    (`Σ_v |R(v)|w(v)(logN − logv) = Σ_{1<t≤N}(logt − log(t−1))·σ(t−1)` — exact swap) and
    **`weighted_sigma_le`** (increments ≤ 1/(t−1)). This reduces the weighted mass (what the fiber
    transfer produces) to scale-sampled plain σ-partial sums (what B3 bounds) — NO weighted ladder.
    ROUTE NOTE: factor-2 accounting verified on paper — the (logN − logv) weight is what keeps the
    recursion at ratio a (not 2a).
    NEXT: (C3) `Σ_{1<t≤N}(1/(t−1))σ(t−1) ≤ (a−θ)·½log²N + C·logN` — apply B3 per t (t−1 ≥ x₁) +
    head; needs `Σ_{s≤N} logs/s ≤ ½log²N + O(logN)` (derive via banked increment sandwich) —
    CHECK CORPUS: the hΔlogsum inside VonMangoldtLogHarmonicSummatory is INLINE; consider exporting.
    Then (C1) the fiber transfer m-side → weighted v-sum (last hard brick; plan the two-regime
    fiber-count bookkeeping on paper+mpmath first), (D) recursion, (E) iteration.
  - 2026-07-29: **σ-route brick (C3-i) DONE** — `formal/GaloisForLFunctions/RHTower/ScaleSigmaSum.lean`
    (umbrella-registered, `lake build` clean, standard axioms): **`sum_log_div_le`**
    (`Σ_{s≤M} log s/s ≤ ½log²M + 1` — increment sandwich + log²-telescope + Basel; the ½ is exactly
    the coefficient the recursion divides against) and **`sum_inv_le`** (`Σ_{s≤M}1/s ≤ logM + 2`).
    NEXT (C3-ii): `sigmaPartial_le_of_ratio` — uniform `σ(s) ≤ (a − g/L)·log s + C₁` for all s ≥ 1
    (head s ≤ x₁ crude via 8Σ1/(v+1) ≤ 8(log s + 2); above x₁ via B3 + σ(x₁)-head; need
    `a − g/L ≥ 0`: g ≤ aρ/3 ≤ a/6 < a·log2 ≤ aL via banked `log y ≥ 1 − 1/y`), then (C3-iii) the
    combined `Σ_{s≤M}σ(s)/s ≤ (a−g/L)(½log²M + 1) + C₁(logM+2)`. Then (C1) fiber transfer (paper
    plan + mpmath first), (D), (E).
  - 2026-07-29: **σ-route brick (C3-ii) DONE — THE UNIFORM σ BOUND** —
    `formal/GaloisForLFunctions/RHTower/SigmaUniformBound.lean` (umbrella-registered, `lake build`
    clean, standard axioms): `sigmaPartial_le_crude` (`σ(s) ≤ 8(log s + 2)`), `gain_div_log_le`
    (`g/L ≤ a` — rate positivity survives: g ≤ a/6, L ≥ log2 ≥ 1/2), and
    **`sigmaPartial_le_of_ratio`** — the single closed form at EVERY scale s ≥ 1:
    `σ(s) ≤ (a − g/L)·log s + C₁`, `C₁ = g + 14a/x₁ + 8(log x₁ + 2)`.
    NEXT (C3-iii): one small lemma — `Σ_{s≤M}(1/s)σ(s) ≤ (a−g/L)(½log²M + 1) + C₁(logM + 2)` —
    per-term multiply + `sum_log_div_le` + `sum_inv_le` (both banked); then reindex through the
    Fubini (`weighted_sigma_le` has Σ_{t∈Ioc 1 N}(1/(t−1))σ(t−1) — reindex s := t−1 to Icc 1 (N−1)).
    Then (C1) fiber transfer (paper + mpmath first — the LAST hard brick), (D) recursion combining
    second inequality + (C1) + Fubini + (C3), (E) iteration.
  - 2026-07-30: **σ-route brick (C3-iii) DONE — SCALE SIDE COMPLETE** —
    `formal/GaloisForLFunctions/RHTower/WeightedSigmaTotalBound.lean` (umbrella-registered,
    `lake build` clean, standard axioms): **`weighted_sigma_total_le`** —
    `Σ_{v≤N}|R(v)|w(v)(logN − logv) ≤ (a − g/L)(½log²N + 1) + C₁(logN + 2)` for N ≥ 2, chaining
    Fubini → uniform σ bound → scale summatories. The σ-side of the contraction is DONE.
    REMAINING for the elementary PNT (the exact bridge):
    (C1) fiber transfer: `Σ_{m≤N}W(m)|R(⌊N/m⌋)| ≤ 2N·[weighted mass] + C₂·N·logN` where
    [weighted mass] = the LHS of weighted_sigma_total_le. PLAN (to certify with mpmath next
    iteration): expand W-cumulative V(m) = Σ_{k≤m}W(k) with |V(m) − 2mlogm| ≤ 420m
    (`abs_selberg_weight_summatory`... note that gives Σ(Λlogk + ΛΛ) with error 420·M — VERIFY
    the exact banked form: `abs_selberg_weight_summatory : |ΣW − 2NlogN| ≤ 420N`); Abel:
    Σ W(m)g(m) = Σ_m V(m)(g(m) − g(m+1)) + V(N)g(N+1-boundary) with g(m) := |R(⌊N/m⌋)|;
    then V(m) = 2mlogm ± 420m and the smooth part Σ 2mlogm·(g(m)−g(m+1)) Abel-backs to
    Σ (2mlogm − 2(m−1)log(m−1))g(m) ≈ Σ(2logm + 2)g(m); the error part needs
    Σ m·|g(m) − g(m+1)| = O(NlogN): |g(m)−g(m+1)| ≤ |R(⌊N/m⌋) − R(⌊N/(m+1)⌋)| ≤
    (⌊N/m⌋−⌊N/(m+1)⌋) + (ψ(⌊N/m⌋)−ψ(⌊N/(m+1)⌋)) [slow variation both sides, ψ mono]:
    Σm·(fiber gaps + ψ-fiber gaps): Σm(⌊N/m⌋−⌊N/(m+1)⌋) Abel-backs to Σ⌊N/m⌋ ≈ NlogN ✓;
    Σm(ψ-gaps) Abel-backs to Σψ(⌊N/m⌋) = Σ log k ≈ NlogN ✓ (floorSummatory_chebyshevPsi!!).
    Then Σ(2logm+2)|R(⌊N/m⌋)|: fiber-decompose EXACTLY: Σ_v |R(v)|·Σ_{m∈fiber v}(2logm+2) with
    fiber-interval log-sums via Stirling sandwich → 2N·(1/v−1/(v+1))-masses... the last
    conversion needs care (the plan's two-regime issue) — mpmath-certify then formalize.
    (D) recursion, (E) iteration.
  - 2026-07-30: **σ-route brick (C1-ii) DONE — THE FIBER VARIATION BOUND** —
    `formal/GaloisForLFunctions/RHTower/FiberVariationBound.lean` (umbrella-registered, `lake build`
    clean, standard axioms): `abs_psiRemainder_sub_le_sum` (step telescoping
    `|R(B)−R(A)| ≤ Σ_{(A,B]}(Λ(u)+1)`) and **`sum_mul_abs_fiber_diff_le`**
    (`Σ_{m≤N} m·||R(⌊N/m⌋)|−|R(⌊N/(m+1)⌋)|| ≤ 2N logN + 9N`) — gaps partition (0,N], m-weight
    ≤ N/u on the gap of u, Mertens + harmonic close it. Numerically certified. This is the ONCE-paid
    Abel-transfer error against V(t) = 2tlogt ± 420t.
    (C1) ARCHITECTURE (revised on paper this iteration): the transfer is
    Σ W(m)g(m) = Σ V(m)Δg(m) [exact Abel, g(N+1) = |R(0)| = 0] = Σφ(m)Δg + ΣE(m)Δg with
    φ = 2mlogm: |ΣEΔg| ≤ 420·(this brick) ≤ 840NlogN + O(N); Σφ Δg Abel-backs EXACTLY to
    Σ_{m∈Icc 2 N}(φ(m)−φ(m−1))g(m), φ-increments ∈ [2logm, 2logm+2].
    NEXT (C1-iii): the m-side main sum `Σ_{m≤N}(2logm+2)|R(⌊N/m⌋)|` → connect to the weighted
    v-mass: CAUTION — the naive fiber-count route has the +1-slack problem (recorded); the SOUND
    route: logm ≤ logN − log⌊N/m⌋ (exact: m ≤ N/⌊N/m⌋) pointwise, then the m-sum with weight
    (2(logN − logv_m)+2) FIBER-EXACTLY equals Σ_v |R(v)|(2(logN−logv)+2)·#fiber_v and #fiber_v =
    ⌊N/v⌋−⌊N/(v+1)⌋ — handle #fiber via a SECOND Abel in v (same variation machinery, weight
    N/v-type) — OR bound m-side directly by the m-space ladder. DECIDE next iteration with mpmath;
    both routes fully specified above. Then (C1-iv) assembled transfer, (D), (E).
  - 2026-07-30: **ROUTE DECISION for (C1-iii) (paper, before Lean)** — both v-space conversions are
    DEAD: (Route A) Abel-in-v pays `Σ(Λ(v)/v)(logN−logv)·N ≈ ½Nlog²N` (an absolute +½ on the
    ratio); (fiber-count route) the +1-slack per fiber EQUALS the main term in the band
    `v ∈ [√(N/logN), √(NlogN)]` (fibers of size O(1)). CORRECT ROUTE (Nathanson-faithful): the
    **m-space ladder** — after the Abel step the main sum is `Σ_m (2logm+2)|R(⌊N/m⌋)|`; bound
    `|R(⌊N/m⌋)| ≤ r_m·N/m` (⌊⌋-slack O(NlogN) ✓) and contract `Σ(2logm+2)r_m/m` by a ladder in m
    with the SMOOTH weight `(2logm+2)/m`: block masses are log²-sized (evaluation errors O(logY/Y),
    utterly dominated), gain windows = m-preimages of fiber small-value windows (the small-value
    theorem applies to the fiber window (N/(QY), N/Y] of log-ratio logQ). Bricks:
    (M1) sharp window bounds for Σ(2logm+2)/m [THIS iteration]; (M2) m-block contraction (mirror
    B1); (M3) m-ladder + closed form (mirror B2/B3): `Σ_{m≤N}(2logm+2)r_m/m ≤ (a−θ)log²N + C·logN`;
    (M4) assembled transfer + recursion — (D) then follows DIRECTLY (no v-space T needed).
    STATUS NOTE: v-space bricks (C2), (C3-i,ii,iii) remain valid corpus but are OFF the critical
    path.
  - 2026-07-31: **m-space brick (M1-upper) DONE** — `formal/GaloisForLFunctions/RHTower/WindowLogHarmonicSharp.lean`
    (umbrella-registered, `lake build` clean, standard axioms): `sum_G_inc_window` (G = log² + 2log
    telescope) and **`sum_log_harmonic_window_le`** (`2 ≤ y ≤ z`:
    `Σ_{(y,z]}(2logm+2)/m ≤ G(z) − G(y) + (2log(y+1)+6)/y`) — increment identity
    `(2logm+2)Δ = ΔG + Δ²` + shifted reciprocal-square tail (`Δ² ≤ 1/((m−2)(m−1))` telescope;
    NOTE the unshifted `1/(m−1)²` comparison runs the WRONG direction — caught in compile).
    Numerically certified.
    NEXT (M1-lower, if needed — check: the m-block contraction needs LOWER bounds only on
    gain-window masses: lower `Σ_{(y,z]}(2logm+2)/m ≥ G(z) − G(y) − (small)`: same machinery,
    increments against ΔG(m→m+1) − Δ²); then (M2) m-block contraction: block (Y, 2QY], fiber
    small-point m₀ ∈ fiber window ⇒ m-gain window (⌊N/((1+ρ)m₀)⌋, ⌊N/m₀⌋]-ish with ratio ε' ⇒
    `Σ_{m∈block}(2logm+2)r_m/m ≤ a(G-block) − (a−ε')·(gain G-mass ≥ ρ/2·2logY-ish) + errors`;
    (M3) ladder+closed form; (M4) transfer+recursion.
  - 2026-07-31: **m-space brick (M1-lower) DONE** — appended to `WindowLogHarmonicSharp.lean`
    (rebuilt, standard axioms): **`sum_log_harmonic_window_ge`** (`1 ≤ y ≤ z`:
    `Σ_{(y,z]}(2logm+2)/m ≥ G(z) − G(y) − (2log(y+1)+3)/y`). The two-sided sharp evaluation of the
    m-ladder weight is complete.
    NEXT (M2 — the m-block contraction): mirror `sigma_block_contraction` with weight
    `(2logm+2)/m`: block (Y, 2QY] in m-space; the FIBER window for the small-value theorem is
    (⌊N/(2QY)⌋, ⌊N/Y⌋]-ish — careful: need its log-ratio > 40/δ + 2: log(⌊N/Y⌋/⌊N/(2QY)⌋) ≈
    log(2Q) − floor-errors ⟸ fine for N/Y large (require Y ≤ N/x₁-type: blocks stay below
    m ≤ N/x₁ so fibers ≥ x₁); m-gain window := preimage Ioc ⌊N/((1+ρ)m₀)⌋ ⌊N/m₀⌋ of the fiber
    gain window (m₀, (1+ρ)m₀] — pointwise |R(⌊N/m⌋)| ≤ ε'⌊N/m⌋ for m in preimage since
    ⌊N/m⌋ ∈ [m₀, (1+ρ)m₀] there (verify: m ≤ ⌊N/m₀⌋ → ⌊N/m⌋ ≥ m₀ ✓ standard; m > ⌊N/((1+ρ)m₀)⌋
    → ⌊N/m⌋ ≤ (1+ρ)m₀ ✓); gain-window G-mass ≥ ρ/2·(2·log(N/((1+ρ)m₀))-ish) — lower bound via
    (M1-lower) with the preimage endpoints; per-block statement:
    `Σ_{m∈block}(2logm+2)/m·r_m ≤ a·(G-increment) − (a−ε')·(ρ/3)·(2log(Y)-scale) + errors·logY/Y`.
    Then (M3) ladder, (M4) transfer+recursion, (E) iteration.
  - 2026-07-31: **m-space brick (M2a) DONE — THE M-SPACE GAIN WINDOW** —
    `formal/GaloisForLFunctions/RHTower/MSpaceGainWindow.lean` (umbrella-registered, `lake build`
    clean, standard axioms): **`exists_m_gain_window`** — for `Y ≥ 8`, `Y ≥ 8/ρ`, `N ≥ 8QY`,
    fiber base `W₀ = ⌊N/(2QY)⌋ ≥ 2/ρ` with junk-absorption: ∃ (A, B] ⊆ (Y, 2QY] with
    `log B − log A ≥ ρ/4` and pointwise `|R(⌊N/m⌋)| ≤ ε'·⌊N/m⌋` on it (floor-preimage of the
    fiber gain window; certified over 3134 random cases before writing).
    NEXT (M2b — the m-block contraction): assemble the three zones of (Y, 2QY] with M1-upper on
    a-zones, the pointwise ε' + ⌊N/m⌋ ≤ N/m on the gain zone, M1-lower/G-exactness for the gain
    mass ≥ (ρ/4)·2logY: `Σ_{m∈(Y,2QY]}(2logm+2)|R(⌊N/m⌋)| ≤ N·[a·ΔG_block − (a−ε')(ρ/2)logY
    + C(logN)/Y]`. Then (M3) ladder, (M4) transfer+recursion, (E) iteration.

### (M2b) DONE — m-block contraction (`MBlockContraction.lean`)
`RHTower.m_block_contraction`: under the M2a hypotheses plus `0 < a`,
`ε' ≤ a`, `x₀ ≤ ⌊N/(2QY)⌋`, and the uniform ratio `|R(t)| ≤ a·t` for `t ≥ x₀`:

`Σ_{m∈(Y,2QY]} (2·log m + 2)·|R(⌊N/m⌋)|
   ≤ N·( a·(G(2QY) − G(Y)) − (a−ε')·(ρ/2)·log Y + 3a·(2·log(2QY)+8)/Y )`,
`G(t) = log²t + 2·log t`.

Proof: three-zone split of `(Y, 2QY]` at the M2a gain window `(A, B]`
(`Finset.Ioc_union_Ioc_eq_Ioc` twice + disjoint sum unions); per-zone
uniform helper `hzone` (pointwise ratio → `r·N·(2logm+2)/m` → M1-upper
`sum_log_harmonic_window_le`); error normalization `hEnorm`
(`(2log(y+1)+6)/y ≤ (2log(2QY)+8)/Y` via `log_succ_sub_log_le` +
`div_le_div_of_nonneg_left/right`); gain `G`-mass
`G(B) − G(A) = (logB−logA)(logB+logA+2) ≥ (ρ/4)·2·logY`; final `linarith`
over the ring-identity `e1..e4, efinal` bridges. Numerically certified
(3000 random cases, 0 fails) before writing. Build clean (8519 jobs),
axioms standard, index regenerated. No new corpus overlap (probe:
`div_le_div_of_nonneg_left/right`, `Real.log_le_log`,
`Finset.Ioc_union_Ioc_eq_Ioc`, `pow_le_pow_left₀` all verified in
scratch; zone machinery reused from WindowLogHarmonicSharp + MSpaceGainWindow).

NEXT (M3 — the m-ladder + closed form): iterate `m_block_contraction`
over blocks `Y_j = x₁·(2Q)^j`, `j = 0..J−1`, `J := Nat.log (2Q) (N/x₁)`
(mirror `sigma_ladder_contraction` + `sigma_window_contraction_of_ratio`):
telescoping the `a·ΔG_block` main terms gives `a·(G(2QY_{J−1}·…) − G(x₁))`;
each block donates gain `(a−ε')·(ρ/2)·log Y_j ≥ (a−ε')·(ρ/2)·log x₁` — but
NOTE the per-block gain must be converted to a fraction of the block's own
G-mass (block ΔG ≈ 2·log(2Q)·log Y_j) to contract the *coefficient*:
target `Σ_{m∈(x₁,N]}(2logm+2)|R(⌊N/m⌋)| ≤ (a − θ_m)·G(N) + C(Q,x₁)·log N`
with `θ_m := (a−ε')·(ρ/4)/(2·log(2Q))` (gain/blockmass ratio, uniform in j).
Junk hypotheses (`hWρ`, `hjunkf`, ratio floor `x₀`) propagate exactly as in
`sigma_ladder_contraction` — reuse its hypothesis-plumbing pattern. Then
(M4) transfer+recursion, (E) iteration.

### (M3) DONE — m-ladder contraction (`MLadderContraction.lean`)
`RHTower.m_ladder_contraction`: for all `J` with the top-block hypotheses
(`8Q·x₁(2Q)^J ≤ N`, width `2/ρ ≤ ⌊N/(2Q·x₁(2Q)^J)⌋`, ratio floor
`x₀ ≤ ⌊N/(2Q·x₁(2Q)^J)⌋`, uniform junk `log N + 1 + 2√t·log t ≤ κt` above
the top-block fiber threshold — all propagate DOWN the ladder by
`Nat.div_le_div_left` antitonicity), plus the new ladder-geometry
hypothesis `hx₁Q : log(2Q) + 2 ≤ 2·log x₁`:

`Σ_{m∈(x₁, x₁(2Q)^{J+1}]} (2·log m + 2)·|R(⌊N/m⌋)|
   ≤ N·( (a − θ_m)·(G(x₁(2Q)^{J+1}) − G(x₁)) + (J+1)·3a·(2·log N + 8)/x₁ )`,
`θ_m := (a−ε')·ρ/(8·log(2Q))`.

Mechanism: per-block conversion inside `hblockconv` — block G-mass
`ΔG = log(2Q)·(2logY + log(2Q) + 2) ≤ 4·log(2Q)·logY` once
`log(2Q)+2 ≤ 2logx₁ ≤ 2logY`, so `θ_m·ΔG ≤ (a−ε')(ρ/2)logY` (the M2b
gain); per-block error normalized to `3a(2logN+8)/x₁`; induction mirrors
`sigma_ladder_contraction` exactly (split `Ioc` at `Y_{J+1}`, telescope
`(a−θ)ΔG`, error count +1). Block junk derived from uniform junk via
`Q·⌊N/(2QY)⌋ ≤ N` (nat) + log mono.

IMPORTANT (process): the previous certifications' `log Q > 40/δ+2` filter
made trials vacuous (needs Q > e^82). Re-certified BOTH M2b assembly
(2631 real trials, 0 fails — hQ only feeds window existence, never the
assembly algebra) and M3 (26570 trials, 0 fails, incl. per-block
conversion). Certification scripts must print trial counts from now on.
Build clean (8520 jobs), axioms standard, index regenerated.

NEXT (M4a — ladder corollary with head+tail): mirror
`sigma_window_contraction_of_ratio`. Target: for `x₁ < N` with
`J := Nat.log (2Q) (N/(8·Q·x₁))`-ish maximal usable level:
`Σ_{m∈(x₁,N]}(2logm+2)|R(⌊N/m⌋)| ≤ N·((a−θ_m)(G(N)−G(x₁)) + C_Q·logN + …)`
— tail `(x₁(2Q)^{J+1}, N]` priced at ratio `a` with G-mass
`≤ log(16Q²)·(2logN+2)` (since maximality forces `N/Y_{J+1} < 16Q²`);
ladder-error `(J+1)·3a(2logN+8)/x₁ ≤ C·log²N/x₁` — absorb both into a
single `C(Q,x₁)·logN·(1 + logN/x₁)`-type junk. Also needs
`Nat.log`-based maximal-J facts (cf. `SigmaContractionCorollary`'s
`J := Nat.log (2Q) (N/x₁)` plumbing — reuse its pow/Nat.log lemma usage).
Then (M4b) assemble the exact Abel fiber transfer with
`FiberVariationBound` + `SelbergWeightEvaluation`; (D) ratio recursion;
(E) iteration to ψ ~ x.

### (M4a) DONE — m-window contraction in closed form (`MWindowContraction.lean`)
`RHTower.m_window_contraction_of_ratio`: with a cutoff parameter `c`
satisfying J-FREE hypotheses `8Q ≤ c`, `2/ρ ≤ c/(2Q) − 1`,
`x₀ ≤ c/(2Q) − 1`, `c·x₁ ≤ N`, and junk absorption for all
`t ≥ c/(2Q) − 1`:

`Σ_{m∈(x₁,N]} (2·log m + 2)·|R(⌊N/m⌋)|
   ≤ N·( (a−θ_m)·(G(N) − G(x₁)) + (2logN+1)·3a(2logN+8)/x₁
        + 8(2logN+8)/x₁ + 8·log c·(2logN+2) )`.

Key resolution this brick surfaced: for small ρ the ladder CANNOT run to
`Y ≈ N/(8Q)` — the block width hypothesis `2/ρ ≤ ⌊N/(2QY)⌋` caps usable
blocks at fiber floor `≈ c/(2Q)`. Hence the cutoff `c`: ladder height
`J := Nat.log (2Q) (⌊N/(cx₁)⌋)` gives top-block fiber floor
`⌊N/(2QY_J)⌋ ≥ c/(2Q) − 1` (floor bound via `Nat.div_add_mod` + `mod_lt`
+ nlinarith) so all three per-block hypotheses discharge from the J-free
`c`-form; maximality gives `N < c·Y_{J+1}`, so the tail `(Y_{J+1}, N]`
has log-length ≤ log c, priced by crude `abs_psiRemainder_le` (ratio 8)
at G-mass ≤ log c·(2logN+2). Block count `J ≤ 2logN` via
`(2Q)^J ≤ N` + `L ≥ 1/2` (`Real.log_two_gt_d9`). `θ_m ≤ a/8 ≤ a` keeps
the main coefficient monotone under `G(Y_{J+1}) ≤ G(N)`.
Certified: 33128 trials, 0 fails, incl. all hypothesis-derivation facts
as asserts. Build clean (8521 jobs), axioms standard, index regenerated.

NEXT (M4b — the assembled fiber transfer): connect
`selberg_second_inequality` (|R(N)|log²N ≤ Σ_{m≤N}W(m)|R(⌊N/m⌋)| +
800NlogN + 2900N) to the m-window contraction. Chain:
(i) Abel: Σ W(m)|R(⌊N/m⌋)| = Σ V(m)Δg + exact smooth part; per card the
smooth part is Σ_{m∈Icc 2 N}(φ(m)−φ(m−1))g(m) with increments in
[2logm, 2logm+2] (SelbergWeightEvaluation `abs_selberg_weight_summatory`
gives |V(t) − t·G'(t)-ish| ≤ 420t; FiberVariationBound pays the transfer
error 2NlogN+9N once, scaled by 420).
(ii) Head `m ≤ x₁`: crude |R(⌊N/m⌋)| ≤ 8⌊N/m⌋ ≤ 8N/m:
Σ_{m≤x₁}(2logm+2)·8N/m ≤ 8N·(G(x₁)+C) — O_{x₁}(N)·logx₁ junk.
(iii) m-window contraction on (x₁, N].
Target: Σ_{m≤N}W(m)|R(⌊N/m⌋)| ≤ (a−θ_m)N·log²N + C(Q,c,x₁)·N·logN.
Then (D) divide by log²N in selberg_second_inequality → ratio recursion
a ↦ a − θ_m(a) + o(1); (E) iterate: fixed point forces a → limsup|R|/N
≤ ε for every ε (θ_m(a) > 0 whenever a > ε'(δ,ρ,κ) and δ,ρ,κ free).
First read SelbergWeightEvaluation.lean + SelbergSecondInequality.lean
exact statements before designing M4b — the Abel bookkeeping must match
what is already banked.

### (M4b) DONE — Selberg fiber transfer (`SelbergFiberTransfer.lean` + `HTGeometry/DiscreteAbelIcc.lean`)
New general infrastructure: `HTGeometry.sum_mul_eq_partial_mul_diff` —
discrete Abel summation on `Icc 1 N` (Σ F·g = Σ V·Δg + V(N)g(N+1),
V = partial sums), proven by induction with `Finset.sum_Icc_succ_top`.

`RHTower.selberg_weight_fiber_transfer` (same hypotheses as M4a):
`Σ_{m≤N} W(m)·|R(⌊N/m⌋)| ≤ N·( (a−θ_m)(G(N)−G(x₁)) + J₁ )`,
`J₁ := (2logN+1)·3a(2logN+8)/x₁ + 8(2logN+8)/x₁ + 8logc(2logN+2)
      + 8G(x₁) + 66 + 840logN + 3780`.
Chain: (i) Abel with W (boundary |R(⌊N/(N+1)⌋)| = |R(0)| = 0);
(ii) V(m) = 2mlogm ± 420m (`abs_selberg_weight_summatory` per-m) — the
±420m × fiber variation pays 420·(2NlogN+9N) once
(`sum_mul_abs_fiber_diff_le`); (iii) Abel BACK with the exact
antiderivative F'(k) = 2klogk − 2(k−1)log(k−1) (partial sums telescope
to 2mlogm via `Finset.sum_range_sub`); (iv) increments ≤ 2logm+2
(`log_succ_sub_log_le`); (v) head `m ≤ x₁` at crude ratio 8 via the
BANKED `sum_log_div_le` + `sum_inv_le` (ScaleSigmaSum) — G(x₁)+6 mass,
total 8G(x₁)+48 ≤ +66 (first head attempt with {1,2}-literal splitting
hit cast-literal rw failures; the corpus-lemma route is both shorter and
robust — corpus reuse won again); (vi) M4a window on (x₁, N].
Head/increment constants certified (3000 trials + exhaustive m ≤ 2·10⁵).
Build clean (8523 jobs), axioms standard on both, index regenerated.

NEXT (D — the ratio recursion): combine `selberg_second_inequality`
(|R(N)|log²N ≤ Σ W|R| + 800NlogN + 2900N) with
`selberg_weight_fiber_transfer`:
|R(N)|/N ≤ (a−θ_m)·(1 − G(x₁)/log²N + 2/logN·…)·(log²N-normalizations)
+ (J₁ + 800logN + 2900)/log²N. Target statement (clean form): under the
M4a hypotheses ∃ explicit C(a,Q,c,x₁) with
∀ N ≥ N₀(c,x₁): |R(N)|/N ≤ (a − θ_m) + C·(1/logN + logx₁²/log²N + …).
Simplest Lean shape: |R(N)| ≤ (a−θ_m)·N + C·N/logN·(explicit), i.e.
prove `abs_psiRemainder_ratio_step`: |R(N)|·log²N ≤ (a−θ_m)·N·log²N +
C·N·logN with C := 3a(2·…)/x₁-terms + 8logc·2 + … + 800 + junk — fold
J₁·(…) into C·logN via logN ≥ 1 for N ≥ 3 and 1/x₁ ≤ 1. Then (E):
iterate a ↦ a−θ_m(a)+o(1) down to any ε' + margin: fixed-point argument
+ archimedean choice of parameters (δ,ρ,κ,Q,c,x₁ free), yielding
∀ε>0 ∃N₀ ∀N≥N₀ |R(N)| ≤ εN — elementary PNT. The κ-junk hypothesis
hjunkc must be DISCHARGED at that point: log N + 1 + 2√t·logt ≤ κt for
t ≥ c/(2Q)−1 — needs c chosen ≥ f(κ, N)… careful: threshold grows with
N (log N term) — for fixed c must check t ≥ (c/2Q)−1 covers: 2√t·logt ≤
(κ/2)t for t ≥ T₀(κ) (sqrt-log growth lemma — check corpus: hjunk1 in
v-space used the same shape: `2√t·logt ≤ κ/2·t` hypothesis discharged
where? SEARCH corpus for the discharge lemma before building: maybe
never discharged yet — then (E) needs the sqrt-log threshold lemma +
logN+1 ≤ (κ/2)t for t ≥ (2/κ)(logN+1) — c must depend on N?? NO: c/(2Q)
−1 ≥ (2/κ)(logN+1) requires c ~ logN — c is allowed to depend on N in
the final iteration (choose c := c₀ + ⌈K·logN⌉; the J₁ junk has 8logc·
(2logN+2) = O(loglogN·logN) still o(log²N) ✓). Design (E) around
N-dependent c.

### (D) DONE — ψ-ratio recursion step (`PsiRatioRecursionStep.lean`)
`RHTower.psi_ratio_recursion_step` (M4a hypotheses verbatim):
`|R(N)|·log²N ≤ (a − θ_m + 12a/x₁)·N·log²N + C·N·logN`,
`C := 80a + 32·log c + 8·G(x₁) + 8466`.
Proof: `selberg_second_inequality` + `selberg_weight_fiber_transfer`,
then the fold `hfold` (h1..h6, each sub-log² term ≤ coefficient·logN
using logN ≥ 1 from N ≥ 64 = 8·8 ≤ c·x₁ and exp 1 < 3). θ ∈ [0, a]
re-derived internally (hLhalf via `Real.log_two_gt_d9`). NOTE: the
per-piece Lean constants sum to 8466, not the certified 8386 — the
python cert tested the final inequality (slack-pooled), the Lean proof
sums per-piece worst cases; statement uses 8466. Lesson recorded:
certify the DECOMPOSITION (each hᵢ), not only the final inequality.
50000-trial cert on the folding; build clean (8524 jobs), axioms
standard, index regenerated.

NEXT (E — the iteration to ψ ~ x). Design (N-dependent parameters):
(E1) junk discharge lemma: ∀ κ>0 ∃T₀ ∀t ≥ T₀ (t:ℝ): 2√t·logt ≤ (κ/2)t —
sqrt-log vs linear growth. CHECK CORPUS FIRST (HTGeometry may have
sqrt/log asymptotics; `Real.isLittleO`-free explicit form preferred:
√t·logt ≤ (κ/4)t ⟺ logt ≤ (κ/4)√t; use log t ≤ 2(√t − 1) ≤ 2√t
[Real.log_le_sub_one_of_pos at √t: log t = 2 log √t ≤ 2(√t−1)] — gives
2√t·logt ≤ 4t·... wait: log t = 2log√t ≤ 2(√t−1) < 2√t ⟹ 2√t·logt ≤
4t — NOT enough (need εt). Sharper: log√t ≤ √√t-type bootstrap:
log u ≤ u^{1/2}·(2/e)-ish… standard: log u ≤ (2/κ')·u^{1/2} for the
needed range via log u = 4 log u^{1/4} ≤ 4(u^{1/4}−1) ≤ 4u^{1/4} ⟹
2√t logt = 2√t·4·t^{1/4}·(t^{−1/4}·logt/4·t^{1/4})… cleanest: logt ≤
4·t^{1/4} (from log = 4log(t^{1/4}) ≤ 4(t^{1/4}−1)); then 2√t·logt ≤
8·t^{3/4} ≤ (κ/2)t ⟺ t^{1/4} ≥ 16/κ ⟺ t ≥ (16/κ)⁴ ✓ EXPLICIT T₀.
Then logN + 1 ≤ (κ/2)t for t ≥ (2/κ)(logN+1) — c must grow ~ logN:
choose c := c(N). (E2) single-pass ratio improvement: given ratio a at
floor x₀, choose δ,ρ,κ per target, Q with logQ > 40/δ+2, x₁ ≥
max(8, 8/ρ, e^{(log2Q+2)/2}, 48a/θ-ish), c(N) := max(8Q, ⌈2Q(2/ρ+2)⌉,
⌈2Q((2/κ)(logN+1)+(16/κ)⁴+2)⌉) — c depends on N: then hcx₁N needs
c(N)x₁ ≤ N — holds for N ≥ N₁ (c ~ logN); conclude ∃x₀' ∀N≥x₀':
|R(N)| ≤ (a − θ/2)N-type. (E3) iterate countably: a₀ = 8 (crude), aₖ₊₁
= aₖ − θ(aₖ)/2 → ε'⁺; diagonal over δ,ρ,κ → 0: ∀ε ∃x₀ ∀N≥x₀ |R N| ≤ εN.
Final target statement: `psiRemainder_ratio_tendsto_zero`:
∀ ε > 0, ∃ x₀, ∀ N ≥ x₀, |psiRemainder N| ≤ ε*N (elementary PNT).
Then step 5 (short-interval primes for the parent card).

### (E1) DONE — sqrt-log junk discharge (`HTGeometry/SqrtLogLinearDomination.lean`)
`HTGeometry.two_sqrt_mul_log_le_of_quartic_ge`: κ>0, t ≥ (16/κ)⁴ ⟹
`2√t·log t ≤ (κ/2)t`. Built on the BANKED
`log_le_four_quarter_root_sub_one` (QuarterRootTelescopeSum — corpus
search hit, no re-derivation): with s := √√t, log t ≤ 4s,
2√t·logt ≤ 8s³ ≤ (κ/2)s⁴ = (κ/2)t once s ≥ 16/κ (clear the division:
16 ≤ κs before nlinarith — division inside product hints kills
ring-normalization). Sub-1 case: log ≤ 0 trivial.
`HTGeometry.add_two_sqrt_mul_log_le_of_threshold`: κ>0,
T ≥ max((16/κ)⁴, (2/κ)y) ⟹ ∀t≥T: y + 2√t·logt ≤ κt — the EXACT shape
of hjunkc (y := logN+1, t cast from ℕ). 200k-trial cert. Build clean
(2082 jobs), axioms standard.

NEXT (E2 — single-pass ratio improvement). Statement target:
`psi_ratio_improve`: {a δ ρ κ : ℝ} {Q x₀ x₁ : ℕ} (params as in D) →
∃ x₀' : ℕ, ∀ N ≥ x₀', |R(N)| ≤ (a − θ/2 + 12a/x₁)·N  — by choosing
c := c(N) per N inside the proof:
  c(N) := max(8Q, ⌈2Q·(max(2/ρ, (x₀:ℝ)) + 2)⌉, ⌈2Q·((16/κ)⁴ +
           (2/κ)(logN+1) + 2)⌉ )   [so c/(2Q)−1 ≥ all three thresholds]
  - hρc, hx₀c ✓ by construction; hjunkc ✓ from E1-threshold lemma with
    T := c/(2Q)−1 ≥ max((16/κ)⁴, (2/κ)(logN+1));
  - hcx₁N : c(N)·x₁ ≤ N holds for N ≥ N₁ since c(N) = O(logN);
  - D gives |R(N)|log²N ≤ (a−θ+12a/x₁)N·log²N + C(N)·N·logN with
    C(N) = 80a + 32log(c(N)) + 8G(x₁) + 8466 = O(loglogN);
  - divide by log²N: |R(N)| ≤ (a−θ+12a/x₁)N + C(N)N/logN; and
    C(N)/logN ≤ θ/2 for N ≥ N₂(θ) (loglogN/logN → 0 — needs an explicit
    Archimedean lemma: ∀ε>0 ∃M ∀N≥M: (K₁ + K₂·log(K₃+K₄·logN))/logN ≤ ε
    — prove via log z ≤ z and eventually-below; CHECK CORPUS for
    log-over-log limit lemmas, else build in HTGeometry with explicit
    thresholds: log(A+B·logN) ≤ log(A+B) + log(logN)+… ≤ √logN·const for
    logN large via two_sqrt-style bounds? Simpler: log x ≤ 2√x ⟹
    log c(N) ≤ K√(logN) ⟹ C(N)/logN ≤ K'/√logN ≤ θ/2 explicit N₂.)
Then (E3) countable descent + diagonal.

### (E2) DONE — single-pass ratio improvement (`PsiRatioImprove.lean`)
`RHTower.psi_ratio_improve`: params (a δ ρ κ Q x₀ x₁) with STRICT
ε' < a and κ > 0 (no c, no N — both constructed):
`∃ x₀', ∀ N ≥ x₀': |R(N)| ≤ (a − θ/2 + 12a/x₁)·N`,
θ/2 = (a−ε')ρ/(16·log(2Q)).
Construction inside the proof: cutoff c(N) := ⌈2Q(S(N)+2)⌉₊,
S(N) := 2/ρ + x₀ + (16/κ)⁴ + (2/κ)(logN+1) + 2 (SUM of thresholds —
simpler than max); c/(2Q)−1 ≥ S+1 ≥ every component ⟹ hρc, hx₀c, and
hjunkc (via E1 `add_two_sqrt_mul_log_le_of_threshold`) all hold BY
CONSTRUCTION. Growth: c ≤ K₁+K₂logN exactly (2Q(S+2)+1 = K₁+K₂logN by
ring); c·x₁ ≤ N via logN ≤ 2√N + explicit ceil thresholds; recursion
constant ≤ K₃+K₄√logN (log c ≤ 2√c, √subadditivity) ≤ (θ/2)logN past
`exists_nat_log_ge (max (4K₃/θ) ((4K₄/θ)²))`. Division by log²N via
`le_of_mul_le_mul_right`. New aux (all standard axioms):
`log_le_two_sqrt`, `sqrt_add_le_add_sqrt`, `exists_nat_log_ge`.
Cert: 88338 log-space trials, 0 real fails (KCHAIN flags were float
roundoff on an exact ring identity — verified exact in Lean).
FIRST-COMPILE CLEAN (largest brick so far). Build 8526 jobs.

NEXT (E3 — descent + diagonal to elementary PNT):
(E3a) `psi_ratio_descent`: fix target ε > 0. Choose δ := ε/4? Actually:
given ANY a₀ with a base ratio (a₀ = 8 via `abs_psiRemainder_le`, x₀=0),
iterate psi_ratio_improve. Parameter discipline per pass: need ε' < a
(else stop — a ≤ ε' + margin is the win). Fix δ,ρ,κ,Q once per TARGET:
given ε, set δ := min(ε/8, …), ρ ≤ min(1/2, s.t. ρ(log(1/ρ)+3) ≤ ε/8),
κ := ε/8, Q := any with logQ > 40/δ+2 (∃ via exists_nat_log_ge/exp),
x₁ ≥ max(8, 8/ρ, e^{(log2Q+2)/2}, 96a₀/ε?) — need 12a/x₁ ≤ ε/8·… and
UNIFORM over the descent: a stays ≤ a₀ = 8, so x₁ := fixed with
12·8/x₁ ≤ εθ-margin… Contraction: a_{k+1} := a_k − θ(a_k)/2 + 12a_k/x₁
with θ(a) = (a−ε')ρ/(8L). If a ≥ ε'+ε/2: θ(a)/2 ≥ ερ/(32L); choose x₁
also ≥ 96·8·L·… s.t. 12a/x₁ ≤ ερ/(128L) ⟹ net decrease ≥ ερ/(64L) > 0
per pass ⟹ finitely many passes until a < ε' + ε/2 ≤ ε (ε' ≤ 3ε/8 by
param choice: δ+ρ(log(1/ρ)+3)+κ ≤ ε/8+ε/8+ε/8 = 3ε/8 ✓). Induction on
k with ⌈(a₀−ε)/(net-decrease)⌉ steps, or well-founded: cleanest Lean:
prove `∀ n : ℕ, ∃ x₀ₙ, ∀N≥x₀ₙ: |R N| ≤ (8 − n·d)·N ∨ target` — better:
strong statement P(k): ∃x₀ₖ ∀N≥x₀ₖ |R N| ≤ max(ε, 8 − k·d)·N, induct.
(E3b) ρ-existence lemma: ∀ε>0 ∃ρ∈(0,1/2]: ρ(log(1/ρ)+3) ≤ ε (ρ→0
limit; explicit: ρ := min(1/2, ε²/…)? ρ(log(1/ρ)+3): at ρ = e^{−u}:
e^{−u}(u+3) ≤ ε for u large: use ρ := min(1/2, ε/(2(log(2/ε)+3))-ish —
needs care with log(1/ρ) monotonicity; OR avoid: use u := max(3, log(2/ε))
and ρ := e^{−u}: then ρ(u+3) ≤ e^{−u}·2u ≤ … log-space cert first!)
(E3c) Q-existence: Q := ⌈exp(40/δ+3)⌉₊ (log Q > 40/δ+2 via log mono +
log_exp — same pattern as exists_nat_log_ge).
(E3d) x₁-existence: x₁ := max stuff + exp((log2Q+2)/2) ceil.
Final: `psiRemainder_eventually_le`: ∀ε>0 ∃x₀ ∀N≥x₀ |R N| ≤ ε·N.

### (E3) DONE — ★ ELEMENTARY PNT FORMALIZED ★ (`PsiRatioDescent.lean`)
`RHTower.psiRemainder_eventually_le`:
  **∀ ε > 0, ∃ x₀, ∀ N ≥ x₀: |ψ(N) − N| ≤ ε·N**
UNCONDITIONAL, axioms = [propext, Classical.choice, Quot.sound].
Erdős–Selberg, fully formalized from Selberg symmetry through the
m-space contraction ladder, recursion, and descent — no sorries, no
extra axioms, no analytic ζ-input anywhere in the chain.

Assembly: `exists_rho_small` (ρ := min(1/2,(ε/5)²);
ρ(log(1/ρ)+3) ≤ 2√ρ+3ρ ≤ 5√ρ ≤ ε via `Real.div_sqrt`); parameters
δ = κ = ε/8, Q from `exists_nat_log_ge (40/δ+3)`, x₁ := nested
max/ceil (8, 8/ρ, e^{L/2+1}, 6144L/(ερ)); descent invariant
∀k ∃b y: 0<b ∧ (b ≤ 8−k·d ∨ b ≤ ε) ∧ (∀N≥y: |R N| ≤ bN), d :=
ερ/(64L); base = crude `abs_psiRemainder_le`; step = psi_ratio_improve
(active case b > ε gives b−ε' ≥ 5ε/8, contraction ≥ 5·(ερ/(128L)),
head leak ≤ 2·(ερ/(128L)) via x₁-gap); terminal k* := ⌈8/d⌉₊ makes
left disjunct contradict 0 < b. Fix rounds: `rw [hρs]` clobbering
occurrences inside √ (→ `Real.div_sqrt` route); cast-of-max vs
max-of-casts linarith atoms (state nat ineq then cast whole);
explicit N for hMx application; div_le_iff₀ direction.
Cert: 200k trials on ρ-lemma + step arithmetic (invalid ε>8 sampling
caught and fixed in cert harness — active case needs ε < b ≤ 8).
Build clean (8527 jobs). NOTE: 13 lean processes from ANOTHER agent
(MobiusContactGamma* etc.) observed and left running per rules.

### CARD STATUS: core objective COMPLETE (ψ ~ x unconditional).
Remaining for the PARENT card (weighted-euler-tangent-global-graph-
decoupling): step 5 — short-interval primes from ψ ~ x:
(5a) θ vs ψ: θ(x) ≥ ψ(x) − 2√x·log x (banked: mathlib
`Chebyshev.psi_sub_theta_le` used in PsiWindowUpperBound) →
θ(N) = N + o(N).
(5b) window primes: ∀δw>0 ∃x₀ ∀x≥x₀: θ((1+δw)x) − θ(x) ≥ δw·x/2 > 0 ⟹
primes in ((1+δw)-windows ⟹ discharge
`exists_separated_primeLog_nodes` (check its exact statement in
RHTower first: rg "exists_separated_primeLog_nodes").
(5c) parent-card final assembly.

### (5) DONE — unconditional prime window supply (`PrimeWindowSupply.lean`)
Three theorems, all standard axioms, all UNCONDITIONAL:
1. `chebyshevTheta_remainder_eventually_le`: |θ(N) − N| ≤ εN eventually
   (PNT at ε/2 + `Chebyshev.psi_sub_theta_le`/`theta_le_psi` + E1
   quartic sqrt-domination at κ := ε).
2. `exists_prime_log_window`: ∀η>0 ∃R₀ ∀y≥R₀ ∃p prime:
   y ≤ log p ≤ y+η. Window [⌈e^y⌉−1, ⌊e^{y+η}⌋]: θ-mass ≥
   (b−m) − εw(b+m) ≥ De^y/2 − De^y/4 ≥ 1/2 > 0 with εw := D/(8e^η),
   D := e^η−1, for e^y ≥ max(x₀+1, 2/D); positive prime-log sum over
   the filter ⟹ nonempty (`theta_window_eq`). LESSON: never `rw` an
   exp/cast identity that also matches inside ⌊·⌋/⌈·⌉ arguments — pass
   the identity to (n)linarith as an atom-link instead. Also: `h√` is
   NOT a valid identifier (√ is notation) — silent parse misread.
3. `exists_separated_primeLog_nodes_unconditional`: ∀N ∃R₀ ∀R≥R₀:
   N+1 pairwise-(1/(4(N+1)))-separated prime logs in [R, R+1] — the
   hwin hypothesis of the banked `exists_separated_primeLog_nodes`
   discharged by (2) at η := 1/(4(N+1)).
Cert: 200k trials on the window arithmetic. Build 8529 jobs.

### THIS CARD: ALL STEPS COMPLETE. Move to 3-formalized.
The chain elementary-PNT → θ-PNT → window primes → separated
prime-log nodes is fully unconditional in Lean. NEXT (parent card
`weighted-euler-tangent-global-graph-decoupling`, step 5c): consume
`exists_separated_primeLog_nodes_unconditional` in the parent's
oversampling/carrier assembly — read the parent card and
`WeightedEulerPrimeNodeAssembly.lean`'s downstream consumers
(rg "exists_separated_primeLog_nodes" usage sites) to wire the final
(18)/(19) closures.
