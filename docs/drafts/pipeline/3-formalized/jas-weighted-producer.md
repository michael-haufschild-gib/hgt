# JAS weighted producer: every sub-power budget that VK reaches is unconditional

- **ID:** jas-weighted-producer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** jas-goal-loop-2026-10-09.md rows 112–127; card jas-diagonal-bochner-level-one.md
- **Statement:** Fix a dressing g on the strip: bounded, nonvanishing at the zeros, with g(s̄) = conj g(s) and g(1−s) = g(s). Weight the JAS aggregate by g(ρ)/(ρ(1−ρ)). Then (i) RH ⟺ dressed product positivity at level 1 on large primes or on Huxley windows; (ii) for the Gaussian dressing g = e^{τ(s−½)²} with τ small, dressed positivity holds unconditionally at budget exp(c(log y)^{1/(1+θ)}) for every θ > 2/3 (VK); (iii) for faster dressings, the budget is y^{o(1)}; (iv) budget y^λ for some λ > 0 ⟺ quasi-RH, for every dressing.

## Goal
The undressed JAS producer stops at budget (log y)^{3/2}. The stopping point is the γ^{−2} tail of the weights 1/(ρ(1−ρ)), not the zero-free region itself. Dressing removes that tail while keeping the RH-equivalence. The aim is to show that every sub-power budget is free, so the whole producer problem sits at a fixed power y^λ, which is quasi-RH. The Gaussian dressing is the Mellin transform of a Gaussian, so the dressed aggregate is still a Weil-positivity test computable from the prime side.

## Gates
- [x] 0 → 1  in-progress: well-posed; mechanism identified
- [x] 1 → 2  fully-proven: paper proof below
- [x] 2 → 3  formalized: 7 modules R:JointAncestryWeighted{Lag,LagGrowth,Bochner,Level,Producer,CosProducer,BudgetLaw}; axioms propext/Classical.choice/Quot.sound

## Paper proof (sketch → complete)
Let v_q = g(ρ_q) w_q with w_q = 1/(ρ(1−ρ)), and Φ_g(L) = Σ v_q e^{(ρ−½)L}. This is real (the conjugation equivalence plus g(s̄) = conj g) and even (the reflection plus g(1−s) = g).
1. **Bochner.** Copy the diagonal Bochner argument with v in place of w: |Σ_P a_p Φ_g(log p)| ≤ Φ_g(0) + V·R·(1 + e^{αu}), where V = Σ‖v‖ ≤ K·W.
2. **Coherence.** ‖v_q‖ ≤ K‖w_q‖, so the undressed termwise bound gives |Φ_g(u+y) − Φ_g(u)| ≤ K·(undressed coherence bound).
3. **Growth criterion.** If Φ_g(L) ≤ M e^{aL} on L ≥ 0 with 0 ≤ a < ½, all zeros satisfy Re ρ ≤ ½ + a. Copy the one-sided Landau machinery with the pole series G_g(s) = Σ v_q/(s − (ρ−½)). The residue at ρ₀ − ½ is m(ρ₀)·g(ρ₀)w(ρ₀) ≠ 0 because v is constant on the fibre and nonzero.
4. **Windows.** As in JointAncestryDiagonalBochnerLevel this gives RH ⟺ dressed positivity at level 1.
5. **Producer.** Re Agg_g ≥ C(Re Φ_g(0) − Σ‖v_q‖(e^{E_q} − 1)), with E_q = Σ_P p^{−(σ−|β_q−½|)}.
   - Zeros below height T have E_q ≤ B y^{−ω(T)}.
   - Zeros above T have ‖v_q‖ ≤ sup_{|γ|>T}|g|·‖w_q‖.
   - Gaussian: |g| ≤ e^{τ/4}e^{−τγ²}, so T ≈ √B; VK gives ω(T) ≥ c(log T)^{−θ}, hence log B ≲ log y/(log B)^θ.
   - Re Φ_g(0) > 0 for small τ, by dominated convergence (Φ_g(0) → Φ(0) = poleSharpConstant).

## Lean plan
- JointAncestryDressedLag: dressing structure, Φ_g, real, even, bounds, coherence.
- JointAncestryDressedLagGrowth: pole series, Laplace identity, growth criterion.
- JointAncestryDressedBochner: dressed aggregate, Bochner bound.
- JointAncestryDressedLevel: RH ⟺ dressed positivity at level 1.
- JointAncestryDressedProducer: generic producer, then Gaussian/VK and faster dressings.

## Log
- 2026-10-12: created; mechanism analysis in ledger row 128.
- 2026-10-12: formalized. Lean theorems:
  - `riemannHypothesis_iff_exists_jasWeightedProductPositiveAbove_one`: RH ⟺ level-1 positivity, for any dressing positive on the line.
  - `xiZeroHalfPlaneBound_of_jasWeightedProductPositiveAbove`: level σ ≥ 1 gives half-plane σ−1, for every dressing.
  - `exists_gaussWeighted_positive_expLogBudget`: Gaussian dressing, budget exp((log y)^A) for every A < 3/5.
  - `exists_cosWeighted_positive_budget`: g_κ = exp(|κ|(1−cos 3(s−½))), budget exp(log y·(log log y)^{−θ'}) for every θ' > 2/3.
  - `exists_halfPlane_lt_half_iff_exists_jasWeightedBudgetPositive`: quasi-RH ⟺ weighted budget positivity at some y^λ, λ > 0.
  - Note: the predicates are named "Weighted" because the corpus already uses "dressed" for the level-σ dressing of JAS.
- Survivor insight: the polylog stop (log y)^{3/2} of the undressed producer came from the tail of the zero weights. Weighted JAS reaches every budget y^{(log log y)^{−θ'}} unconditionally, so the producer problem inside JAS is exactly the power gap y^{o(1)} → y^λ, i.e. quasi-RH. For analytic dressings bounded on the strip the decay is at most doubly exponential (Phragmén–Lindelöf on a strip of width 1), so (log log y)^{−2/3} is the natural limit given VK (heuristic, not formalized).
