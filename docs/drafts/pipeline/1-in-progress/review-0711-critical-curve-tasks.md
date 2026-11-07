# Review-0711 §2.1 critical-curve tasks (A9–A14)

- **ID:** review-0711-critical-curve
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0711/obstacles-summary.md), "Critical curve"
- **Statement:** Each task A9–A14 gets a complete unconditional Lean theorem, easiest first.

## Status

| Task | Status | Lean |
|---|---|---|
| A14 frequency-integral identity; Gaussian moments in the typical-height sign | done | `ArithmeticPolarization/WeilsFormIsTheAverageOfItsFrequencyPackets.lean`: `integral_re_W_frequencyPacket`, `∫ Re W(f ⋆ φ_X) dX = 2π‖φ‖₂² Re W(f)`; `volume_neg_frequencyPacket_pos`. `ArithmeticCastelnuovoSeveri/TheBadHeightsOfTheLocalSignHaveGaussianTails.lean`: `exists_weilPositive_quadrature_moment` (bad measure `209 k^k(4δ²)^k T`, `kδ ≤ 8M²`), `exists_weilPositive_quadrature_exp_rare` (`418 e^{−5M²/δ} T` for `δ ≤ 1/(64M²)`), `eventually_weilPositive_loglog_aperture` (aperture `K log log T`, bad measure `≤ T^{1−1/(64K)}`). Axioms: propext, choice, Quot.sound |
| A11 finish CACT critical-ratio modules | owned by a non-Claude agent (both [S] files edited 13:42–14:35); not touched | — |
| A10 compactness assembly | open | — |
| A13 growing-period charges beyond gcd profiles | done (growth up to an ineffective unbounded scale) | `ArithmeticCouplingTheory/ChargesBeyondTheGcdProfilesAreCoercive.lean`: `jumpEnergy_ge_beyond_gcd` (`J_N(F) ≥ η²(log N)²/(16M²)` for `M`-periodic `F` with gcd defect `η`, every `M ≤ M₀(N)`), `tendsto_admissiblePeriod_atTop` (`M₀(N) → ∞`, `M₀ ≤ log log N`), `eventually_completeWeilEnergy_ge_beyond_gcd` (`W(u) ≥ (1−ε)J(u)` on `1 ≤ c ≤ (log N)^{1/4}`, all critical ratios), `eventually_completeWeilEnergy_coercive_beyond_gcd` (`W(u) ≥ η² log N/(256V²(log log N)²)‖u‖²`). Inputs: Mertens in progressions (`ArtinMertens`), two-moment bound. Open strengthening: periods `M ≤ (log N)^{β}` need Mertens in progressions uniform in the modulus (Siegel–Walfisz-type lower bounds for `L(1,χ)`), absent from corpus and Mathlib. Axioms: propext, choice, Quot.sound |
| A12 low-packet polar Schur payment against the top window | classified: at every ratio it implies RH | `CriticalArithmeticCorrelationTheory/TheLowPacketPaymentAtEveryRatioIsTheRiemannHypothesis.lean`: `PolarPaymentAt R A` (`S(h)²/D(R) ≤ pencil_R(H)` on `[−A,0]`); `polarPaymentAt_of_eventually_nonneg` (PSD along one critical sequence of ratio `R` ⇒ payment on every window); `le_windowThreshold_of_polarPaymentAt` (payment ⇒ `R ≤ R₁(A)`); `le_windowThreshold_of_eventually_nonneg` (PSD at `R` ⇒ `R ≤ inf_A R₁(A)`); `riemannHypothesis_of_polarPayment_on_top_windows` (payment at every `R` on `(1/8)log(R+1)+C₀` ⇒ RH); `riemannHypothesis_of_eventually_nonneg_at_every_ratio`; survivor `exists_polarPaymentAt_on_every_window` (band `R ≤ (2K)⁸`). Axioms: propext, choice, Quot.sound |
| A9 explicit `K₀`, horizon, profile, Beurling schedule | open | — |

## A12 no-go closure
- **Killing theorem:** payment at every ratio on windows of length `→ ∞` gives `R₁(A) = ⊤` for every `A`, i.e. RH (`riemannHypothesis_of_polarPayment_on_growing_windows`). A12 "at every ratio" is not finite work.
- **Positive survivor:** at one ratio the payment is necessary for positivity and bounds the ratio, `R ≤ inf_A R₁(A)`; it holds on every window below `(2K)⁸`.
- **Insight:** the positivity interval of the complete matrix along the critical curve is contained in `(0, inf_A R₁(A)]`, and `inf_A R₁(A) = ⊤ ⇔ RH`. The forward direction at one ratio (payment on the top window ⇒ PSD) is the A10 assembly.

## A14 plan

- Identity: `‖χ‖² Re W(f,f) = ∫ Re W(f ∗ χ̌_X, f ∗ χ̌_X) dX` from `re_W_eq_integral_nuX` (spectral density
  `ν_X`, independent of the window once the support fits) and Fubini; `χ̌` compactly supported.
- Moments: `D_N = P_N + E_N` (primes / proper prime powers). `E_N` absorbed by its sup. For `P_N`,
  `|P_N|^{2k} = |P_N^{(k)}|²` (`dirichletPowerConvolutionDirPoly_convPow`), coefficient mass
  `≤ k^k (Σ_p |a_p|²)^k` (`sum_normSq_convPow_le_of_prime_support`), mean value on any interval of
  length `T` once `N^k ≤ T`. Jensen on the probability weight `w/(π/A)` moves the moment inside
  `primeField`. Bad measure `≲ T (8kM⁴λ²)^k` at `A = λ log T`, `k ≍ 1/(2λ)`.

## Log
- 2026-11-07 — created
