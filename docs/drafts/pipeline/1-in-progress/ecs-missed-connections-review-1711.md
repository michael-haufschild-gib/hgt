# ECS missed connections of review 1711 (E-M10–E-M21)

- **ID:** ecs-missed-connections-1711
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper → Lean), goal loop
- **Source:** docs/reports/review-1711/route-ecs.md §8
- **Statement:** formalize each corpus connection E-M10–E-M21 of the ECS route as unconditional Lean theorems about the critical state, with corollaries.

## Goal
Each E-M item names corpus results that ECS does not import. The task is the theorem the connection gives, not a re-export. Order: easiest first.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven (per item)
- [ ] 2 → 3  formalized (per item)

## Items

| Item | Target theorem | Module (ECS/) | Status |
|---|---|---|---|
| E-M20 | ¬AAL ⇒ Θ attained by an isolated top; then moments finite exactly for b < 17 − 2Θ, endpoint infinite, and the window masses ∫_{W_ν}abs F·e^{−8u} have exact rate Θ − ½ (≤ C e^{aνℓ} for every a > Θ − ½ at all levels; syndetic excursions above C e^{aνℓ} for every a < Θ − ½, gap = size of the top). Unattained Θ ⇒ AAL | Decay/WithoutTheAbscissaLawTheWindowMassesHaveTheRateOfTheZeros.lean | formalized (`criticalState_exact_window_rate_of_not_asymptoticAbscissaLaw`, `criticalState_endpoint_regimes`) |
| E-M16 | transport of the ladder to the window picture: for 0 < r ≤ R_m every confined Gram matrix of window tests has ≤ #{i : R_i < r} negative squares, and the rungs below r span a negative space; at r ≤ R_k no window family carries k + 1 negative squares (the window ladder dominates the ECS ladder). The counts of the other pictures agree by transitivity (not restated) | Index/TheLadderBoundsTheNegativeSquaresOfEveryWindow.lean | formalized (`IsCriticalLadder.hermNegIndex_confinedGram_le`, `IsCriticalLadder.fullEnergy_sum_neg`, `IsCriticalLadder.hermNegIndex_confinedGram_le_of_le`) |
| E-M11 | totality of the orbit of the state in the energy norm | — | not started |
| E-M14 | ¬AAL (⟺ ψ(x) − x a single finite oscillation, ZCG) ⇒ the heated prime side F⁺_ε(T) = a⁻¹Σ_{bottom} LF(z)e^{εz²−zT} + O(e^{κ₂T}), a finite oscillation at rate Θ − ½ with the frequencies of the top; ¬AAL ⇒ real-amplitude positivity fails above every X for σ ∈ (Θ−½, Θ+½); B13 ⟺ (finite layer ⇒ ψ − x is not a single finite oscillation). The ψ-wave and positivity rows are the peer E-J15 module | Modes/WithoutTheAbscissaLawThePrimeSideIsAFiniteOscillation.lean | formalized (`criticalState_heatedBeyondWall_finiteOscillation`, `not_jasRealPositiveAbove_of_not_asymptoticAbscissaLaw`, `b13_iff_finiteOffLine_not_primeErrorIsFiniteOscillation`) |
| E-M15 | rigidity rows of the model table | — | not started |
| E-M12 | mean squares of the mode series (= E-J12) | — | not started (peer item E-J12) |
| E-M19 | stability of the window problem: a negative window test, normalized, is within C(R*(H) − W₀) of ±F in W₈ and Q_{W₀}; near-critical window tests converge to the state; R₁(A) ≥ W₀ + c∫_{u<−A}F²e^{−8u}, so no window attains W₀ | Index/TheWindowThresholdsExceedTheCriticalRatioByTheMassBeyondTheWindow.lean | formalized (`criticalState_window_stability`, `criticalState_tendsto_of_windowTests`, `criticalState_windowThreshold_ge`, `criticalState_lt_windowThreshold`) |
| E-M17 | a space in which (★) is a reproducing formula | — | not started |
| E-M18 | Turán bounds with coefficients for mode sums | — | not started |
| E-M13 | size of F⁺ from the prime number theorem | — | not started |
| E-M21 | functional model of the translates | — | not started |
| E-M10 | pointwise edge law (= E-J14) | — | not started (peer item E-J14) |

Peers: the E-J loop (card ecs-just-work-items-review-1711.md) owns E-J10–E-J15. New modules only; one import line each in the ECS umbrella.

## Paper proofs

### E-M20
Let Θ = sup Re ρ. (i) If AAL fails, AAL fails at an isolated top (not_asymptoticAbscissaLaw_iff_hasIsolatedTop): a finite nonempty set S of zero copies on Re = Θ₀ > ½, all others ≤ Θ₂ < Θ₀. Every ζ-zero with Re ρ > Θ₀ would lie in the strip, hence be a zero copy, so Θ = Θ₀ is attained. Unattained Θ therefore gives AAL. (ii) Attained Θ: the moment law is exact (integrable_sq_mul_exp_iff_of_attained), so M(17 − 2Θ) = ∞. (iii) Upper bound, every state: for a > Θ − ½ put b = 16 − 2a < 17 − 2Θ, so M = ∫F²e^{−bu} < ∞. On W_ν = [−(ν+1)ℓ, −νℓ], abs F·e^{−8u} = (abs F·e^{−bu/2})·e^{−au} ≤ e^{a(ν+1)ℓ}(1 + F²e^{−bu})/2, so the window mass is ≤ e^{aℓ}(ℓ + M)/2 · e^{aνℓ}. (iv) Excursions: with the isolating bump ψ₀ on (−ℓ, 0) the level sums of the tower at base ℓ with weights LF(z)ψ̂₀(z) equal −a·∫ψ₀(u+νℓ)e^{−8u}F, bounded by B times the window mass (criticalState_levelSum_laplaceTest, norm_statePairing_shift_le). The top modulus is R = e^{ℓ(Θ−½)}, the rest ≤ e^{ℓ(Θ₂−½)}; for every 0 ≤ a < Θ − ½ the syndetic window lemma (eventually_forall_window_exists_lt_norm_levelSum) with ρ = e^{aℓ} < R gives in every k = #S consecutive levels a ν with C·e^{aνℓ} < window mass.

### E-M14
Under ¬AAL take the isolated top S on Re = Θ (Θ = zetaZeroAbscissa by E-M20), Θ₂ < Θ the bound of the rest. The reflection q ↦ 1 − q maps S to a finite set B of centred zeros on Re z = −(Θ − ½); every other centred zero has Re z ≥ −κ₂, κ₂ = max(Θ₂ − ½, 0) < Θ − ½. The heated zero series a(F⁺_ε(T) − (e^{−8u}F)_ε(T)) = Σ_q LF(z_q)e^{εz_q² − z_qT} converges absolutely; the modes off B are bounded by K e^{κ₂T}‖LF(z)(−1 − z)⁻¹‖ (summable), and the heated confined state is bounded for T ≥ 0. Hence F⁺_ε(T) − a⁻¹Σ_B LF(z)e^{εz² − zT} = O(e^{κ₂T}). Real-amplitude row: the top zero q₀ has maximal distance Θ − ½ from the line (reflection bounds Re q ≥ 1 − Θ), so not_jasRealPositiveAbove_of_maximal_offLine applies for Θ − ½ < σ < Θ + ½. B13 row: RH ⇒ AAL ⇒ ¬finite oscillation (ZCG); conversely, under a finite layer the zeros approach the line, so AAL gives RH.

### E-M19
For a window test H with Q(H) < 0: a(R*(H)) = −Q(H)/M₈(H), so Q_{R*}(H) = Q(H) + a(R*)M₈(H) = 0 and Q_{W₀}(H) = (a(W₀) − a(R*))W₈(H) ≤ a(1)(R* − W₀)W₈(H)/W₀² (R* ≥ R₁(A) ≥ W₀). Normalize G = cH, W₈(G) = W₈(F). The second critical ratio R₂ > W₀ gives Q_{W₀}(X) ≥ (a(W₀) − a(R₂))W₈(X) on the W₈-complement of F, hence W₈(G − sF) ≤ 2Q_{W₀}(G)/(a(W₀) − a(R₂)) for a sign s, and Q_{W₀}(G − sF) = Q_{W₀}(G). Both are ≤ C(R* − W₀). G vanishes left of −A, so W₈(G − sF) ≥ ∫_{u<−A}F²e^{−8u} =: τ(A); taking the infimum over H, R₁(A) ≥ W₀ + τ(A)/C. τ(A) > 0 because F has both signs on every ray.

### E-M16
Let 0 < r ≤ R_m and suppose a half-line family has N + 1 negative squares, N = #{i : R_i < r}. Realification (exists_real_negative_orthogonal_family) gives X ∈ H with Q_r(X) < 0, W₈-orthogonal to the N rungs below r. Put c_i = W₈(Φ_i, X)/W₈(Φ_i) and Z = X − Σ_{R_i ≥ r} c_iΦ_i; then Z is W₈-orthogonal to all rungs, Q_r(Z) ≥ 0 (floor), and Q_r(X) = Q_r(Z) + Σ_{R_i ≥ r} c_i²(a(r) − a(R_i))W₈(Φ_i) ≥ 0, a contradiction. Conversely Q_r(Σ_{R_i<r} c_iΦ_i) = Σ c_i²(a(r) − a(R_i))W₈(Φ_i) < 0 for c ≠ 0. If r ≤ R_k, monotonicity of the rungs gives #{i : R_i < r} ≤ k.

## Conjecture ledger

## Log
- 2026-11-17 — created in 1-in-progress
