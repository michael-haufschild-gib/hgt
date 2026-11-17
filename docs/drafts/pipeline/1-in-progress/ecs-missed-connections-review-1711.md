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
| E-M16 | transport of negative vectors between index pictures | — | not started |
| E-M11 | totality of the orbit of the state in the energy norm | — | not started |
| E-M14 | ¬AAL (⟺ ψ(x) − x a single finite oscillation, ZCG) ⇒ the heated prime side F⁺_ε(T) = a⁻¹Σ_{bottom} LF(z)e^{εz²−zT} + O(e^{κ₂T}), a finite oscillation at rate Θ − ½ with the frequencies of the top; ¬AAL ⇒ real-amplitude positivity fails above every X for σ ∈ (Θ−½, Θ+½); B13 ⟺ (finite layer ⇒ ψ − x is not a single finite oscillation). The ψ-wave and positivity rows are the peer E-J15 module | Modes/WithoutTheAbscissaLawThePrimeSideIsAFiniteOscillation.lean | formalized (`criticalState_heatedBeyondWall_finiteOscillation`, `not_jasRealPositiveAbove_of_not_asymptoticAbscissaLaw`, `b13_iff_finiteOffLine_not_primeErrorIsFiniteOscillation`) |
| E-M15 | rigidity rows of the model table | — | not started |
| E-M12 | mean squares of the mode series (= E-J12) | — | not started (peer item E-J12) |
| E-M19 | the state as a limit of window states | — | not started |
| E-M17 | a space in which (★) is a reproducing formula | — | not started |
| E-M18 | Turán bounds with coefficients for mode sums | — | not started |
| E-M13 | size of F⁺ from the prime number theorem | — | not started |
| E-M21 | functional model of the translates | — | not started |
| E-M10 | pointwise edge law (= E-J14) | — | not started (peer item E-J14) |

Peers: the E-J loop (card ecs-just-work-items-review-1711.md) owns E-J10–E-J15. New modules only; one import line each in the ECS umbrella.

## Paper proofs

### E-M20
Let Θ = sup Re ρ. (i) If AAL fails, AAL fails at an isolated top (not_asymptoticAbscissaLaw_iff_hasIsolatedTop): a finite nonempty set S of zero copies on Re = Θ₀ > ½, all others ≤ Θ₂ < Θ₀. Every ζ-zero with Re ρ > Θ₀ would lie in the strip, hence be a zero copy, so Θ = Θ₀ is attained. Unattained Θ therefore gives AAL. (ii) Attained Θ: the moment law is exact (integrable_sq_mul_exp_iff_of_attained), so M(17 − 2Θ) = ∞. (iii) Upper bound, every state: for a > Θ − ½ put b = 16 − 2a < 17 − 2Θ, so M = ∫F²e^{−bu} < ∞. On W_ν = [−(ν+1)ℓ, −νℓ], abs F·e^{−8u} = (abs F·e^{−bu/2})·e^{−au} ≤ e^{a(ν+1)ℓ}(1 + F²e^{−bu})/2, so the window mass is ≤ e^{aℓ}(ℓ + M)/2 · e^{aνℓ}. (iv) Excursions: with the isolating bump ψ₀ on (−ℓ, 0) the level sums of the tower at base ℓ with weights LF(z)ψ̂₀(z) equal −a·∫ψ₀(u+νℓ)e^{−8u}F, bounded by B times the window mass (criticalState_levelSum_laplaceTest, norm_statePairing_shift_le). The top modulus is R = e^{ℓ(Θ−½)}, the rest ≤ e^{ℓ(Θ₂−½)}; for every 0 ≤ a < Θ − ½ the syndetic window lemma (eventually_forall_window_exists_lt_norm_levelSum) with ρ = e^{aℓ} < R gives in every k = #S consecutive levels a ν with C·e^{aνℓ} < window mass.

## Conjecture ledger

## Log
- 2026-11-17 — created in 1-in-progress
