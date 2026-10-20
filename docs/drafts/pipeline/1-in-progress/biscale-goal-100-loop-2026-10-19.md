# Bi-scale uncertainty: 100-contribution conjecture loop (goal of 2026-10-19 evening)

- **ID:** biscale-goal-100-loop-2026-10-19
- **Stage:** 1-in-progress
- **Type:** research programme ledger
- **Goal:** 100 novel, significant, field-native contributions to `BiScaleUncertainty`, each with an unconditional Lean proof (standard axioms, wired, no heartbeat raises), via an endless conjecture → proof/refutation → lesson loop.
- **Rules:** corpus search tool before conjecturing; no `hgtl7`; no numerical experiments; one foreground Lean process; `lake --old env lean <file>` audits; no full/umbrella builds; field README read-only; clean scratch files.
- **Relation to earlier programme:** `biscale-100-contribution-programme-2026-10-18` (paused at 8). This ledger counts only contributions made under the present goal.

## Count: 17 / 100

## Ledger

| # | Contribution | Module(s) | Status |
|---|---|---|---|
| 1 | **Linear Krein smoothing and the linear logarithmic modulus.** Progression smoothing `S h(x)=m⁻²Σ_{i,j<m}h(x+(i−j)λ)` obeys `|h−Sh| ≤ h(0)−Sh(0)` (no square root; `h−Sh` is positive definite via two-point combinations `f(·+x)±f`), and moves ≤ `2h(0)/m` per lag. With the Lévy increment bound this gives, for every compact `C²` source, `log(1/|x−y|)·|h(x)−h(y)| ≤ 32√e𝒥+2h(0)` (Krein: only the square root of this rate), the inverse-linear integer-log interpolation law `T|h(T)−h(log⌈e^T⌉)| ≤ 32√e𝒥+2h(0)`, the blind tail law `|T||h(T)| ≤ 32√e𝒥+2h(0)` and uniform `L²` blind tails `∫_T^∞h² ≤ (32√e𝒥+2h(0))²/T` (previously divergent). | `LinearKreinSmoothingAndInverseLinearGridTail`, `LinearLogarithmicModulusSharpness` | Lean ✓, axioms standard, wired. Sharpness: at every scale a modulated bump has `𝒥+h(0) ≤ 8 log(1/d)(h(0)−h(d))`, so the rate `1/log(1/d)` with linear energy dependence is optimal. |
| 2 | **Prime-gap → blind-tail transfer.** A node of the blind set in every window `(e^T, e^T+e^{θT}]` gives `(1−θ)T|h(T)| ≤ 32√e𝒥+2h(0)`. With the corpus's unconditional Hoheisel supply (`θ=71/100`), every compact `C²` source blind at the logarithms of the primes (hence every source on the Weil-blind prime-power cone) has, beyond an absolute threshold, `(29/100)T|h(T)| ≤ 32√e𝒥+2h(0)` and `∫_T^∞h² ≤ (100/29)²(32√e𝒥+2h(0))²/T`. Prime-distribution input now controls the BSU blind geometry. | `PrimeBlindInverseLinearTail` | Lean ✓, axioms standard, wired |
| 3 | **Logarithmic Beurling–Turán window law.** If `h(mδ)=0` for `1≤m≤M` then `|∫_0^{(M+1)δ}h| ≤ 12δ(4+log(M+1))h(0)`. The corpus law `≤ δ√(M+1)h(0)` (`DisjointCollarCliqueDivergenceAndTuransProblem`, called "sharp") is not sharp. Mechanism (new in BSU): spectral density `ρ=|f̂|²` from the corpus Weil-test inversion; arithmetic zeros make every spectral Dirichlet energy flat, `∫ρ(ξ)D_{M+1}(θ−2πδξ)dξ=(M+1)h(0)` for all phases `θ`; a covering of the frequency circle by `O(M)` arcs with weights `K/max(1,n)` turns this into a harmonic sum. Reuses `WeilWorkPBAPSpectralMeasure.testSpectralDensity`, `AutocorrelationKrein.weilTest_eq`, `SubexpExcursion.re_dirSum_ge`. | `LogarithmicTuranWindowLaw` | Lean ✓, axioms standard, wired |
| 4 | **Pole invisibility on gapped blind grids (answers README §5 open question: the polar constraint does NOT improve the single-prime bathtub).** For a node set `𝒩` with arbitrarily far logarithmic gaps of half-width `1/5` (e.g. powers of any integer `q≥2`), the distant pair `b(u)−σb(u−T)` of the corpus bump is `𝒩`-blind, has pole `2(1−σe^{T/2})(1−σe^{−T/2})m₊m₋` of either sign and size `≍e^{T/2}`, and archimedean part (without pole) bounded uniformly in `T`. Hence every pole mass is carried at arbitrarily small archimedean cost, every `𝒩`-blind mixture is `ε`-close in archimedean energy to a zero-pole `𝒩`-blind mixture, and zero-pole positivity fails on every gapped node set — while on the full integer grid it is RH (`riemannHypothesis_iff_zeroPoleBlindPositiveOn_all`). The boundary of the README trap "finitely many grid zeros + polar balance" is gaps vs density, not finite vs infinite. | `PoleInvisibilityOnGappedBlindGrids` | Lean ✓, axioms standard, wired |
| 5 | **Square-root node density threshold for pole visibility; no finite set of primes suffices.** If, along arbitrarily far windows `X≤log n≤X+1`, a node set has `K` nodes with `M(K+1)(1+log(K+1))≤e^{X/2}` for every `M` (sub-square-root window density), then a pigeonhole node-free point at distance `1/(2(K+1))` hosts the distant pair of the bump compressed by `L=K+1`: blind on the node set, pole `≍e^{X/2}/L²` of either sign, archimedean part `O((1+log L)/L)` (corpus compression bound). Pole transport cost `O(L(1+log L)e^{−X/2})→0`, so zero-pole and pole-free infima coincide and zero-pole positivity fails. The `S`-smooth integers (any finite `S`) have `≤(⌊(X+1)/log 2⌋+1)^{|S|}` nodes per window, so `¬ZeroPoleBlindPositiveOn {n : primeFactors n ⊆ S}` for every finite `S`, while all integers (`≍e^X` nodes per window, beyond `e^{X/2}`) give RH. The pole weight `e^{x/2}` makes square-root node density critical. | `SquareRootDensityPoleInvisibility` | Lean ✓, axioms standard, wired; formal lint passed |
| 6 | **The logarithmic Beurling–Turán window law is attained (README §5 open question).** Quarter-shifted spectrum: with `A=(M+1)δ`, `ω_k=2π(k+¼)/A`, the mixture `C=(M+1)⁻¹Σ_{k≤M}cos(ω_k x)` vanishes at every `mδ` (telescoping `2sin(θ/2)cos((k+¼)θ)` closes since `(M+1)θ∈2πℤ`), and every atom contributes `A/(2π(k+¼))>0` to the window, so `∫_0^A C ≥ (δ/2π)log(M+2)`. A stretched corpus bump envelope (increment `≤M_b|x|` uniformly, mass `≍R`) and `exists_scalar_spectral_envelope` give one compact `C²` source with exact zeros and `∫_0^{(M+1)δ}h ≥ (δ/4π)log(M+2)h(0)`. Two-sided: best constant between `log(M+2)/(4π)` and `12(4+log(M+1))`. | `LogarithmicTuranWindowSharpness` | Lean ✓, axioms standard, wired |
| 7 | **The single-integer bathtub is exact and the pole does not move it (README §5 open question).** For every integer `q ≥ 2`, with `m_q=(log q/π)∫_0^{π/log q}γ`: (i) blindness only at the powers `q^j` gives `nodeArchOnly ≥ m_q·mass` (corpus bathtub generalized from `q=2`, all-node blindness dropped); (ii) attained at rate `O(1/N)`: midpoint atoms `ω_k=(k+½)π/(Nℓ)` have `Σ_k cos(ω_k jℓ)=0` for `1≤j<2N` (telescoping), cosine/sine modulations of a stretched envelope with correlation radius `<2Nℓ` are blind at all `q^j`, symbol `= h(0)Σγ(ω_k)` up to envelope energy (uniform in frequency), midpoint sum `≤ N m_q + γ(π/ℓ)−γ(0)`; (iii) distant pairs carry any pole mass at small archimedean cost and small mass. Hence `ZeroPoleBlindSymbolSlackOn (q-powers) M ⟺ BlindSymbolSlackOn (q-powers) M ⟺ M ≥ −m_q`; for `q=2` the corpus constant `m₂` is exact; `m_q ≤ m₂` (the prime 2 leaves the smallest gap). | `ExactSingleIntegerBlindSymbolSlack` | Lean ✓, axioms standard, wired |
| 8 | **One multiplicatively independent node strictly improves the single-integer bathtub; the full grid beats the dyadic constant.** For `q,n ≥ 2`, `ℓ=log q`, `t=log n`, folded radius `ρ(r)=‖rℓ mod 2π‖/ℓ`: blindness at all `q^j` makes `∫G cos(tρ) = s∫G` (`s=sin(πt/ℓ)/(πt/ℓ)`), blindness at `n` gives `∫G cos(rt)=0`; the cosine defect is paid pointwise by the fold defect, `|cos(rt)−cos(tρ)| ≤ C(γ(r)−γ(ρ))`, via the crossing slope `κ=(π/8ℓ)/(1/16+π²/ℓ²)²` of `γ` across `π/ℓ` (first Gauss term) and the fold gap `κπ/ℓ` beyond `2π/ℓ`. Hence `A(c) ≥ (m_q+|s|/C)·mass`. Incidence dichotomy: a node that is a power of `q` changes nothing (slack exactly `−m_q`); any other node gives a strict explicit gain (`s≠0` iff `n∉q^ℕ`). Corollary `BlindSymbolSlack(−m₂−η₂₃)`, `η₂₃>0`: strictly better than the corpus's best unconditional constant `−m₂`. Also: on every gapped node set the zero-pole slack equals the slack (`GappedNodeSet.insert`). Shared spectral-density API factored out (`CombinationSpectralDensity`); contribution 7 refactored onto it. | `IncidenceGainOfTheSingleIntegerBathtub`, `CombinationSpectralDensity` | Lean ✓, axioms standard, wired |
| 9 | **Removal law: each power node is priced by one Fourier coefficient of the folded symbol.** Exact slack on `{q^j : j ≥ 1, j ≠ d}` is `−(m_q − |φ_d|)`, `φ_d = ∫F(z)cos(dz)dz/2π = (ℓ/π)∫_0^{π/ℓ}γ(v)cos(dℓv)dv` (`F` = folded symbol); same with zero pole mass (gapped). Lower bound: one free frequency — if all cosine moments at `nℓ` vanish except `n = d`, the phase measure is exactly `(∫G + 2c cos dz)dz/2π` (Fourier uniqueness on the circle, positive measures made comparable by adding `2|c|`·Haar), positivity of that density forces `2|c| ≤ ∫G` (continuous a.e.-zero argument), so the folded symbol integrates to `≥ (m_q − |φ_d|)∫G`. Upper bound: translated pairs `f ↦ f ± f(·−dℓ)` multiply the spectral density by `2 ± 2cos(dℓr)`, keep all other power nodes blind, double the mass and move the symbol by `±φ_d` up to the bathtub defect (reuses contribution 7). Far nodes are cheap: `|φ_d| ≤ (γ(π/ℓ) − γ(0))/d`. | `PowerNodeRemovalLaw` | Lean ✓, axioms standard, wired |
| 10 | **Orbit law: exact slack on `{q^j : d ∤ j}` is `−min_z F_d(z)`, `F_d(z) = (1/d)Σ_{k<d}F(z + 2πk/d)` (orbit average of the folded symbol under rotation by `2π/d`).** Lower bound: vanishing of all phase-measure Fourier coefficients off `dℤ` makes the phase measure rotation invariant (Fourier uniqueness; new shared `exists_phase_measure` factored out of the removal-law module), so the folded symbol integrates to its orbit average `≥ min F_d`. Attainment by an EXACT finite design: atoms at the folded radii of the orbit `θ* + 2πk/d` of a minimizer; `Σ_k cos(α + 2πjk/d) = 0` for `d ∤ j` (telescoping with `sin(πj/d) ≠ 0`) makes the cosine mixture vanish at every `jℓ`, `d ∤ j`, for every envelope — no truncation or Riemann-sum error; wide envelope gives `min F_d + ε`. Same with zero pole mass. Consequence: the powers of `q^d` are worth exactly `m_q − min F_d ≥ 0`. | `PowerOrbitLaw` | Lean ✓, axioms standard, wired |
| 11 | **Power-grid moment theorem: for EVERY exponent set `J ⊆ ℕ`, the exact blind symbol slack on `{q^j : j ∈ J, j ≥ 1}` is `−V_q(J)`, `V_q(J) = inf{∫F dν : ν probability on ℝ/2πℤ, ∫cos(jz)dν = 0 ∀ j ∈ J}`** (`F` folded symbol); same with zero pole mass. Blind slack on any set of powers of one integer is exactly a circle moment problem for the folded archimedean symbol. Lower bound: normalized phase measure is admissible (zero-mass case handled). Upper bound: new design theory (`CircleCosineDesigns`): finite designs `(w,θ)`; quadrature designs on `N > 2K` points with weights `(1 ± cos jθ_k)/N` have moment `±½` at `j`, `0` elsewhere in `[1,K]`; any probability measure's finitely many moments + value lie in the closed convex hull of the traced curve (`Convex.integral_mem`), so a design matches them up to `η`; a `λ`-mixture of quadrature designs makes the moments vanish EXACTLY at cost `O(λ)`. Then cosine/sine modulations at folded radii of the design angles under an envelope with correlation radius `< (K+1)ℓ` are blind at all of `J` (≤ K by the design, > K by the envelope), energy `O(1/K)`. Three solved cases as corollaries: `V_q(ℕ) = m_q`, `V_q(ℕ∖{d}) = m_q − |φ_d|`, `V_q({d ∤ j}) = min F_d`. | `CircleCosineDesigns`, `PowerGridMomentTheorem` | Lean ✓, axioms standard, wired |
| 12 | **Signed single-integer bathtub (no blindness assumed): `A(c) = m_q·mass(c) + Σ_{j≥1} φ_j √(q^j)·v_c(q^j) + (1/2π)∫G(γ − F∘phase)`, remainder ≥ 0.** Every power node is priced by the cosine coefficient `φ_j` of the folded symbol in an exact SIGNED identity (finite sum: node values vanish beyond the support, `exists_nodeVector_pow_eq_zero`); equality iff the spectral density lives on the fundamental period. Mechanism: the phase measure of a compact combination has finitely many nonzero Fourier coefficients `ν̂(j) = π√(q^j)v_c(q^j)`, so by Fourier uniqueness it IS the trigonometric-polynomial density `(∫G + 2Σ ν̂(j)cos jz)dz/2π` (`integral_mul_periodic_eq_of_cos_finite`, finitely-many-free-frequency identification). Contains 7 (blind), 9 (one free node) as special cases; README rule "state theorems for signed correlations". | `SignedPowerBathtub` | Lean ✓, axioms standard, wired |
| 13 | **Band spectrum = zero width (frontier "the band").** For `0 ≤ α < 1/2`: every Xi zero has `Re ρ ≤ 1/2 + α` ⟺ ∀β>α `∫_0^L Ẽ² = O(e^{2βL})` ⟺ ∀β>α `laplaceEnergy N = O((N+2)^{2β})` ⟺ ∀β>α band energy `∫_{|ξ|≤√(N+2)} S_N = O((N+2)^{2β})`. Endpoint: RH ⟺ `∫_0^L Ẽ² ≤ C(1+L)` (closes README §5 "RH ⟹ band not in the corpus": Cramér dyadic `RHTower.dyadic_chebyshev_mean_square_of_riemannHypothesis` summed over dyadic blocks through the gauge dictionary) ⟺ every subexponential band; hence SELF-IMPROVEMENT: `∫_0^L Ẽ² = e^{o(L)}` forces `O(L)`. Mechanism (band ⟹ width): resolvent `Q(t) = e^{-t}(∫_0^t e^hẼ − 2/3)` bounded by `(C+1)e^{βt}` via `2|ab| ≤ μa² + b²/μ` at `μ = e^{(β−1)t}` (no Cauchy–Schwarz), then corpus exponential-width resolvent continuation. Width ⟹ band: generalized von Koch `ChebyshevErrorPowerSpectrum`. Laplace/spectral transfer through the field's two-sided comparisons and the band theorem. | `BandSpectrumZeroWidthLaw` | Lean ✓, axioms standard, wired |
| 14 | **Band slope ≥ zero energy.** If `∫_0^L Ẽ² ≤ C(1+L) + K` (any offset `K`) then for every finite family of distinct critical ordinates `γ_k`, with `n_k` the order of `(s−1)ζ(s)` at `ρ_k = 1/2 + iγ_k`: `Σ_k n_k²/|ρ_k|² ≤ C`; each zero has `n² ≤ C(1/4 + γ²)`. Quantitative form of band ⟹ RH: the band constant dominates the zero energy (Cramér's limiting constant under RH is `Σ m²/|ρ|²`, so this is the sharp direction). Mechanism: Abel means against critical characters. Band ⟹ RH ⟹ `|Ẽ| ≤ C_ε e^{εt}` ⟹ Laplace transform holomorphic on `Re z > 0` (tilted bounded Abel tail) ⟹ equals `−(ζ_u'/ζ_u(z+½)+1)/(z+½)` (identity theorem); logarithmic residue ⟹ `σL(σ+iγ) → −n/ρ`; IBP against the primitive of `Ẽ²` ⟹ `σ∫e^{-σt}Ẽ² ≤ C(1+σ)`; characters Abel-orthonormal (`σ/(σ+iΔ)`); pointwise `2|ab| ≤ a²+|b|²` with `a_k = −conj(n_k/ρ_k)` ⟹ Bessel. | `BandSlopeZeroEnergyLaw` | Lean ✓, axioms standard, wired |
| 15 | **The band's leading constant reads the extremal zeros; the barrier is never sublinear.** (a) Extremal-line law: if `∫_0^L Ẽ² ≤ Ce^{2βL} + K` with `0<β<1/2`, then for distinct `γ_k` with `n_k` the order of `(s−1)ζ(s)` at `ρ_k = 1/2+β+iγ_k`: `Σ n_k²/|ρ_k|² ≤ 2βC` (rate ↔ width was 13; leading constant ↔ extremal zero energy is new). (b) Unconditional: `¬ ∀ c>0 ∃K ∀L, ∫_0^L Ẽ² ≤ c(1+L)+K` — Hardy's theorem (`RHTower.exists_Xi_zero_gt`) gives a critical zero of order ≥ 1, the slope law (14) forbids slope `< 1/|ρ|²`: the square-root barrier is exactly linear, never `o(L)`. (c) Off-line floor: a zero of order `n` at `Re ρ = 1/2+β` forces `∫_0^L Ẽ² > Ce^{2βL}+K` somewhere whenever `2βC|ρ|² < n²`. Mechanism: tilted error `e^{-βt}Ẽ` has Abel energy `σ∫e^{-(2β+σ)t}Ẽ² ≤ C(2β+σ)+Kσ` (IBP, antiderivative `−Ce^{-σT}/σ − Ke^{-aT}/a`), Abel coefficients `σL(β+σ+iγ) → −n/ρ` on the extremal line (continuation holomorphic on `Re z > β` from zero width β), then the abstract Abel–Bessel inequality (`sum_norm_sq_le_of_abel`, refactored out of 14 together with half-plane-β Laplace tools). | `BandExtremalLineLaw` (+ refactor of `BandSlopeZeroEnergyLaw`) | Lean ✓, axioms standard, wired |
| 16 | **Probe resolution law: a compact source sees each zero with weight `|f̂(γ)|²`.** For a compact `C¹` source `f` with gauge derivative `g = f' − f/2`, the stationary gauge convolution `Φ_f(τ) = ∫_0^∞ Ẽ(t)g(t−τ)dt` (the packet of `f` away from the cutoff) satisfies, under RH: `∫_0^L Φ_f² ≤ C(1+L)+K` ⟹ `Σ_k n_k²|f̂(γ_k)|² ≤ C` (`f̂(γ) = ∫e^{iγv}f`). The bare band weighs a zero by `n²/|ρ|²` (14); a probe by `n²|f̂(γ)|²` — the gauge derivative cancels the height damping exactly: `ĝ(iγ) = −ρ f̂(γ)` (IBP, `integral_exp_mul_gaugeDerivative`). Mechanism: `e^{-zτ}Φ_f = (e^{-z·}Ẽ1_{>0}) ⋆ (e^{-z·}ǧ)`, so mathlib's `integral_convolution` factorizes the full-line Laplace transform as `ĝ(z)L(z)`; the `τ ≤ 0` part lives on `[−w,0]` (support radius) and vanishes after multiplying by `σ`; Abel coefficients `σL_Φ(σ+iγ) → ĝ(iγ)(−n/ρ) = n f̂(γ)`; the abstract Abel–Bessel lemma concludes. Generic IBP/Abel-energy lemmas of 14 refactored to arbitrary locally-L² `F`. | `ProbeResolutionLaw` | Lean ✓, axioms standard, wired |
| 17 | **Probe Parseval law (exact): a compact source's packet is an almost periodic zero series.** Unconditional packet explicit formula: for real `f ∈ C²_c` vanishing outside `[−w,w]` and every `τ > w`, the stationary prime–polar packet `P_f(τ) = Σ_n Λ(n)n^{-1/2}f(log n − τ) − ∫_0^∞2cosh(x/2)f(x−τ)dx` satisfies `Σ_ρ m_ρ e^{iγ_ρτ}f̂(γ_ρ) = A_f(τ) − P_f(τ)` absolutely, `A_f(τ) = (1/2π)∫e^{irτ}f̂(r)γ(r)dr → 0` (Riemann–Lebesgue) — from Zeta23's unconditional explicit formula `EF_lit_zetaZeroConfig` applied to the translate (negative logs drop out, the two pole terms are exactly the polar density of ν). Under RH: `(1/L)∫_w^L P_f² → Σ_ρ m_ρ²|f̂(γ_ρ)|²` — the probe band slope of 16 is attained exactly (Parseval for absolutely convergent almost periodic series with injective real frequencies, proved generically: `tendsto_mean_normSq_tsum`). So every compact C² probe reads exactly its weighted zero energy; its packet is bounded under RH. | `ProbeParsevalLaw` | Lean ✓, axioms standard, wired |

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

- **C13 (proved, contribution 13).** Band spectrum = zero width; see row 13. Searched:
  "Cramer mean square psi", "explicit formula psi sum over zeros", RH criteria with
  `normalizedLogError`/`laplaceEnergy`. Reused `dyadic_chebyshev_mean_square_of_riemannHypothesis`
  (RHTower, previously unused), the exponential-width resolvent continuation
  (`xiZeroHalfPlaneBound_of_criticalMellinChebyshevResolventSource_exponentialBound`), generalized
  von Koch (`chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound`).

- **C14 (failed: duplicate, NOT counted).** Polynomial-horizon window moments of divisor-sieve
  signals: `|window − period| ≤ ‖c‖₁^m/H` uniformly in phase, sharp 1/(2H) witness, Möbius bound
  `‖c‖₁ ≤ N²·max|s|`, global sixth-root recovery at N-free horizon `2K⁶/ε`, local Hölder
  equivalence (period ⟺ window) transferring the parity exponents 1, 1/3, 1/5, 1/6 and their
  sharpness. Built and compiled, then found that the BezoutValuationIncidence field already owns
  the core: `PolynomialWindowTranslatedMomentTransfer` (same tuple/CRT law),
  `PolynomialHorizonRecoveryFromArbitraryPhaseWindows` (top-anchor recovery from windows),
  `TranslatedMomentTransferHierarchySharpness` (horizon `N^{m±o(1)}`). Module deleted.
  Lesson: before building anything on the arithmetic-observation side, `rg` the whole
  `GaloisForLFunctions/` tree (other fields, uncommitted files) — the research index may lag
  behind other agents' new modules.

- **C15 (proved, contribution 14).** Band slope ≥ zero energy; see row 14. Searched: "mean square
  Chebyshev error lower bound sum over zeros", "Abel mean Laplace transform residue zero
  ordinate", "Bessel inequality zero ordinates", "multiplicity bound zeta zero from mean square" —
  nothing similar. Reused `HTGeometry.logDeriv_residue_of_meromorphicOrder`,
  `RHTower.analyticOnNhd_ccmAbelLaplaceTail_of_bounded`, `RHTower.integral_Ioi_translate`
  (GaloisForLFunctions.RHTower), `RHTower.zetaResidueUnit_ne_zero_of_riemannHypothesis`,
  `criticalNormalizedChebyshevErrorContinuation(_eq_laplace)`, and contribution 13's
  `exists_abs_normalizedLogError_le_of_xiZeroHalfPlaneBound`.

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
