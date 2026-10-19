# Bi-scale uncertainty: 100-contribution conjecture loop (goal of 2026-10-19 evening)

- **ID:** biscale-goal-100-loop-2026-10-19
- **Stage:** 1-in-progress
- **Type:** research programme ledger
- **Goal:** 100 novel, significant, field-native contributions to `BiScaleUncertainty`, each with an unconditional Lean proof (standard axioms, wired, no heartbeat raises), via an endless conjecture → proof/refutation → lesson loop.
- **Rules:** corpus search tool before conjecturing; no `hgtl7`; no numerical experiments; one foreground Lean process; `lake --old env lean <file>` audits; no full/umbrella builds; field README read-only; clean scratch files.
- **Relation to earlier programme:** `biscale-100-contribution-programme-2026-10-18` (paused at 8). This ledger counts only contributions made under the present goal.

## Count: 6 / 100

## Ledger

| # | Contribution | Module(s) | Status |
|---|---|---|---|
| 1 | **Linear Krein smoothing and the linear logarithmic modulus.** Progression smoothing `S h(x)=m⁻²Σ_{i,j<m}h(x+(i−j)λ)` obeys `|h−Sh| ≤ h(0)−Sh(0)` (no square root; `h−Sh` is positive definite via two-point combinations `f(·+x)±f`), and moves ≤ `2h(0)/m` per lag. With the Lévy increment bound this gives, for every compact `C²` source, `log(1/|x−y|)·|h(x)−h(y)| ≤ 32√e𝒥+2h(0)` (Krein: only the square root of this rate), the inverse-linear integer-log interpolation law `T|h(T)−h(log⌈e^T⌉)| ≤ 32√e𝒥+2h(0)`, the blind tail law `|T||h(T)| ≤ 32√e𝒥+2h(0)` and uniform `L²` blind tails `∫_T^∞h² ≤ (32√e𝒥+2h(0))²/T` (previously divergent). | `LinearKreinSmoothingAndInverseLinearGridTail`, `LinearLogarithmicModulusSharpness` | Lean ✓, axioms standard, wired. Sharpness: at every scale a modulated bump has `𝒥+h(0) ≤ 8 log(1/d)(h(0)−h(d))`, so the rate `1/log(1/d)` with linear energy dependence is optimal. |
| 2 | **Prime-gap → blind-tail transfer.** A node of the blind set in every window `(e^T, e^T+e^{θT}]` gives `(1−θ)T|h(T)| ≤ 32√e𝒥+2h(0)`. With the corpus's unconditional Hoheisel supply (`θ=71/100`), every compact `C²` source blind at the logarithms of the primes (hence every source on the Weil-blind prime-power cone) has, beyond an absolute threshold, `(29/100)T|h(T)| ≤ 32√e𝒥+2h(0)` and `∫_T^∞h² ≤ (100/29)²(32√e𝒥+2h(0))²/T`. Prime-distribution input now controls the BSU blind geometry. | `PrimeBlindInverseLinearTail` | Lean ✓, axioms standard, wired |
| 3 | **Logarithmic Beurling–Turán window law.** If `h(mδ)=0` for `1≤m≤M` then `|∫_0^{(M+1)δ}h| ≤ 12δ(4+log(M+1))h(0)`. The corpus law `≤ δ√(M+1)h(0)` (`DisjointCollarCliqueDivergenceAndTuransProblem`, called "sharp") is not sharp. Mechanism (new in BSU): spectral density `ρ=|f̂|²` from the corpus Weil-test inversion; arithmetic zeros make every spectral Dirichlet energy flat, `∫ρ(ξ)D_{M+1}(θ−2πδξ)dξ=(M+1)h(0)` for all phases `θ`; a covering of the frequency circle by `O(M)` arcs with weights `K/max(1,n)` turns this into a harmonic sum. Reuses `WeilWorkPBAPSpectralMeasure.testSpectralDensity`, `AutocorrelationKrein.weilTest_eq`, `SubexpExcursion.re_dirSum_ge`. | `LogarithmicTuranWindowLaw` | Lean ✓, axioms standard, wired |
| 4 | **Pole invisibility on gapped blind grids (answers README §5 open question: the polar constraint does NOT improve the single-prime bathtub).** For a node set `𝒩` with arbitrarily far logarithmic gaps of half-width `1/5` (e.g. powers of any integer `q≥2`), the distant pair `b(u)−σb(u−T)` of the corpus bump is `𝒩`-blind, has pole `2(1−σe^{T/2})(1−σe^{−T/2})m₊m₋` of either sign and size `≍e^{T/2}`, and archimedean part (without pole) bounded uniformly in `T`. Hence every pole mass is carried at arbitrarily small archimedean cost, every `𝒩`-blind mixture is `ε`-close in archimedean energy to a zero-pole `𝒩`-blind mixture, and zero-pole positivity fails on every gapped node set — while on the full integer grid it is RH (`riemannHypothesis_iff_zeroPoleBlindPositiveOn_all`). The boundary of the README trap "finitely many grid zeros + polar balance" is gaps vs density, not finite vs infinite. | `PoleInvisibilityOnGappedBlindGrids` | Lean ✓, axioms standard, wired |
| 5 | **Square-root node density threshold for pole visibility; no finite set of primes suffices.** If, along arbitrarily far windows `X≤log n≤X+1`, a node set has `K` nodes with `M(K+1)(1+log(K+1))≤e^{X/2}` for every `M` (sub-square-root window density), then a pigeonhole node-free point at distance `1/(2(K+1))` hosts the distant pair of the bump compressed by `L=K+1`: blind on the node set, pole `≍e^{X/2}/L²` of either sign, archimedean part `O((1+log L)/L)` (corpus compression bound). Pole transport cost `O(L(1+log L)e^{−X/2})→0`, so zero-pole and pole-free infima coincide and zero-pole positivity fails. The `S`-smooth integers (any finite `S`) have `≤(⌊(X+1)/log 2⌋+1)^{|S|}` nodes per window, so `¬ZeroPoleBlindPositiveOn {n : primeFactors n ⊆ S}` for every finite `S`, while all integers (`≍e^X` nodes per window, beyond `e^{X/2}`) give RH. The pole weight `e^{x/2}` makes square-root node density critical. | `SquareRootDensityPoleInvisibility` | Lean ✓, axioms standard, wired; formal lint passed |
| 6 | **The logarithmic Beurling–Turán window law is attained (README §5 open question).** Quarter-shifted spectrum: with `A=(M+1)δ`, `ω_k=2π(k+¼)/A`, the mixture `C=(M+1)⁻¹Σ_{k≤M}cos(ω_k x)` vanishes at every `mδ` (telescoping `2sin(θ/2)cos((k+¼)θ)` closes since `(M+1)θ∈2πℤ`), and every atom contributes `A/(2π(k+¼))>0` to the window, so `∫_0^A C ≥ (δ/2π)log(M+2)`. A stretched corpus bump envelope (increment `≤M_b|x|` uniformly, mass `≍R`) and `exists_scalar_spectral_envelope` give one compact `C²` source with exact zeros and `∫_0^{(M+1)δ}h ≥ (δ/4π)log(M+2)h(0)`. Two-sided: best constant between `log(M+2)/(4π)` and `12(4+log(M+1))`. | `LogarithmicTuranWindowSharpness` | Lean ✓, axioms standard, wired |

## Conjecture log (successes and failures, with lessons)

- **C1 (linear Krein smoothing; inverse-linear grid interpolation).** Conjecture: averaging the
  correlation over a lag progression removes the square root of Krein's increment inequality,
  `|h(x) − S h(x)| ≤ h(0) − S h(0)`, and with lag equal to the integer-log mesh gap at `T` and
  `m = ⌈T⌉` this gives `T|h(T) − h(log⌈e^T⌉)| ≤ C₁ 𝒥 + C₂ h(0)` for every compact `C²` source —
  rate `1/T` instead of the corpus rate `T^{-1/2}`
  (`InfiniteGridUniformTail.autocorr_logarithmicCeilNode_error_sq_le`). Consequence on the
  integer-log blind cone: `|h(T)| = O((𝒥+h(0))/T)` and uniform `L²` tails `∫_{T}^∞ h² ≤ C²/T`
  (the old bound gives divergent `L²` tails). **Proved** (contribution 1), generalized to the
  universal linear logarithmic modulus. Lesson: averaging over a lag progression turns the
  quadratic Krein control into a linear one; the Lévy energy pays the averaged origin defect.

- **Novelty check for 1 (search, user request):** the second-difference law
  `|h(s+h)+h(s−h)−2h(s)| ≤ defect` already exists for Sonin sources
  (`RHTower.CCMGammaCenteredTransportControl.abs_ccmActualHeadAutocorrelation_centered_le_defect`).
  Contribution 1's new content is the progression-averaged linear logarithmic modulus, its
  sharpness and the grid/blind consequences; no corpus result gives a `1/log(1/d)` modulus
  linear in the Lévy energy (searches: "second difference autocorrelation linear bound",
  "autocorrelation modulus Levy energy").
- **C3 search record:** "autocorrelation spectral measure Bochner charFun", "Fejer kernel
  arithmetic progression zeros", "Turan window logarithmic cancellation". BSU had never used the
  spectral density of a source; the corpus spectral density for Weil tests and the Dirichlet-sum
  lower bound were reused.
- **Open (sharpness of 3):** is `log M` attained? Needs a source with arithmetic-progression
  zeros and spectral mass correlated with `sgn sin((M+1)δ·2πξ)`; complementary-pair trains
  (Golay-type) give exact even-lag zeros but bounded total window sum — need long trains.

- **C4 (REDISCOVERED, not counted).** Conjecture: dyadic blindness forces spectral flatness
  `|f̂|² ≤ log 2·‖f‖²` and the exact bathtub floor `𝒥 ≥ (ℓ/π)∫_0^{π/ℓ}A`. Search found
  `RHTower.BlindSymbolSlackPrimePowerPeriodization` (`twoPeriodMean_mul_massOf_le`, periodic
  equidistribution `integral_periodic_eq_of_blind`), and the flatness is the classical
  orthonormal-shift characterization. Lesson: the PBAP corpus already owns single-prime bathtubs;
  the remaining slack (≈1.59) is the pole constraint. Open question recorded: does the polar
  constraint improve the dyadic bathtub when only the powers of 2 are blind?

- **C5 (proved, contribution 4).** Searched: "polar enforcement mixture blind powers of two",
  "smooth numbers S-units logarithmic grid gaps", "zero pole blind symbol slack single prime".
  Reused `ArchimedeanPoleValueFunction` (ZeroPoleBlindPositive, adjBump, node calculus),
  `WeilPoleWeightForcedOne.exists_blind_arch_add_mul_pole_neg`, `DistantCopyPolarEnforcement`
  (`subtractCopy` API), `weilArchRe_ofReal_eq_pole_add_gamma_add_biScaleLevyEnergy`.
  Next: S-smooth node sets for finite `S` with ≥2 primes have no fixed-width gaps (consecutive
  S-units get log-close), so the same no-go needs compressed bumps of width `≍ D^{-|S|}` placed
  in pigeonhole gaps; energy cost `≍ log D` vs pole `≍ e^{D/2}D^{-|S|}`.

## Frontier notes (from corpus search)

- PBAP (prime-blind archimedean positivity) is the prime-free half of RH (`RH = PBAP + (N1)`,
  `WeilPositivityPrimeBlindDuality`); the BSU blind cone is its native habitat. Nonnegative-cone
  PBAP reduces to the window inequality `WindowPositive` (margin ≈ 10⁻³, numeric).
- Corpus already has: Lévy–Khintchine symbol (`GammaHardyPhaseRateLevyKhintchine`), spectral
  realization of finite receivers (`FiniteSpectralEnvelopeRealization`), clique sphere duality,
  Beurling–Turán window `√(M+1)` bound (not sharp: true order appears to be `log M`).
</content>
</invoke>

## Log

- 2026-10-19 — At the user's request (superseding this card's "field README
  read-only" rule), `BiScaleUncertainty/README.md` was rewritten as a
  foundational introduction: why (four structures on one state, the Weil–Lévy
  identity and the blind cone, the square-root barrier in field coordinates,
  the meaning of "bi-scale"), what (sources and correlations, archimedean
  weights, polar objects, the signed prime–polar measure and hyperbolic gauge,
  multipliers, allocation objects, producers, the discrete side, glossary),
  how (thirteen mechanisms), traps, frontier, working conventions. No module
  map, dates or status inside the README. Lean sources untouched; the umbrella
  docstring still speaks of "five fundamental mechanisms, and nine structural
  traps".
