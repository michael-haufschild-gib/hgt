# Trans-Metzler Weil Positivity

Namespace `GaloisForLFunctions.TransMetzlerWeilPositivity` (subfolder `BoundedOverlap/` uses `…TransMetzlerWeilPositivity.BoundedOverlap`); umbrella `TransMetzlerWeilPositivity.lean`; 34 modules. Nothing is assumed: RH and finite off-line support appear only as hypotheses of stated implications or as one side of an equivalence. Modules end with `#print axioms`.

## 1. Motivation

The complete Weil form of ζ is tested on atomic families: `N` copies of one profile at `log n`, width `c/N`. Below touching (`c ≤ 1`) a diagonal sign gauge makes the atomic Markov form Metzler; for `c > 1` the top-collar triangle frustrates every gauge. The programme asks four questions. Does unconditional positivity survive past this Metzler wall? At which overlap do twisted sources (Liouville, sign gauges, single prime flips) fail while ζ survives? What can the zero side alone say at fixed overlap? How slowly can an overlap schedule grow and still be equivalent to RH? It answers all four. Positivity crosses `c = 1` by a tiny explicit margin. Twins fail far below touching. Zero-side data alone is insufficient. The RH-equivalent overlap is exactly `L(log L)²`, `L = log log N`, for the logarithmic Denjoy–Carleman profile class. The programme also shows why the full matrix at growing overlap is hard: the non-ratio prime correction is unbounded past touching, and the Gram floor vanishes.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Plateau profile | `transMetzlerProfile` | `plateau (1/1000)`: smooth, supported in `[0,1]`, positive on `(0,1)`, 8000-Lipschitz |
| Constants | `deltaZero`, `cZero`, `rhoZero`, `etaZero` | `10⁻¹⁸`, `1 + 10⁻¹⁸` (ratio at width `c/N`), `1 + ½·10⁻¹⁸` (ratio in units of `atomSpacing N`), `1/1000` |
| Main matrix | `transMetzlerMainMatrix w c N` | renormalized prime matrix + center at `c` + self part; reference for perturbation |
| Certified range | `certifiedOverlapIncrement`, `certifiedOverlapFloor δ` | overlap excess `δ` admitted by the reference + coercivity bounds; floor `1/25 − 2000δ·loss` |
| Young boundary | `transMetzlerOptimizedOverlapFloor`, `transMetzlerCertifiedBoundary` | optimized floor over all Young parameters; its unique zero `c_* > 1 + 10⁻¹⁶` |
| Robin–Euler ratio | `robinEulerThreshold φ` | `exp(β(φ)/‖φ‖²)/(2π)`; twin breakdown threshold |
| Twisted form | `weilQuadTw ε f` (SSHA) | complete Weil form with source `ε(n)Λ(n)` |
| Atomic shift Gram | `atomicShiftWeilGram φ w N` | complex Hermitian Weil Gram of shifted atoms |
| Steklov average | `steklovAvg a f` | `(2a)⁻¹∫_{−a}^{a} f(x+t)dt`; Fourier multiplier `sinc(2πaξ)` |
| Log-DC weight | `dcLogWeight q` | `q!·log(q+3)^{2q}`; submultiplicative |
| Fixed profiles | `steklovDCProfile`, `sincProfile` | infinite Steklov iterates / infinite box convolution; `∫|φ^{(q)}| ≤ A·12^q·W_q` |
| Rate and scale | `dcRate κ N`, `dcScale N` | overlap `N/κ_N` over `ℓℓ₂²`; `L(log L)²` |
| Critical overlap | `dcCriticalOverlap B N`, `sincCriticalOverlap N` | least `c ≥ 1` with tail² `· log N ≤ 1` (majorant / exact Fourier tail) |
| Successor fiber | `weightedDownwardDivisorFiber`, `plateauSuccessorFiber c N` | Schur-weighted divisor fiber of row `N` into product `N+1` |
| Factorial horizon | `factorialSuccessorHorizon Y` | `2·Y! − 1`; every prime `≤ Y` gives a successor edge |
| Prefix Schur complement | `plateauPrefixSchur` | tail − mixedᴴ·prefix⁻¹·mixed after splitting `[1,M] ⊔ (M,N]` |
| Height coordinates | `completeWeilMatrixAtHeight φ N T`, `superGevreyHeight` | width `T⁻¹`; `T = N/c` |
| Prime-square trial | `primeSquareTrial p n` | `1 − 2[p|n] + 2[p²|n]`; prime parity through valuation 2 |

External: `completeWeilMatrix`, `normalizedFullWeilHorizonMatrix`, `poleDefect`, `fullWeilNonRatioMatrix`, `completeWeilAdjunctionEnergy` (RAPT); `atomDilate`, `weilQuad`, `dilate` (SSHA); `atomicTest`, `atomSpacing = log(1 + 1/N)` (ArithmeticElectrostatics); `isolatedPairConfig` (SquareRootThreshold); `finiteFlip`, `cofiniteFlip` (ArithmeticCountingPositivity).

## 3. Language

- Overlap `c`: width `c/N` (or `ρ·atomSpacing N`). Touching `c = 1`. Metzler wall: for `ρ > 1` no unimodular gauge makes `atomicMarkovGram` Metzler.
- Sub-horizon dilution: test only `n ≤ M_N = ⌊θN⌋`; then width `c/N` is a fraction of the local spacing and the form is a Markov (separated) form.
- Receiver: an overlap schedule whose eventual atomic nonnegativity is equivalent to RH. Window: the set of tests a bounded schedule controls.
- Length/height: length `N`, height `T = N/c`, bandwidth `log N/log T`.
- Pole coordinates: coefficients `F(n)/√n`; the prime form becomes `2Σ_m (1/m)Σ_t (Λ(t)/t)F(m)F(tm)`.

## 4. Mechanisms

**A. Crossing the Metzler wall**
1. Overlap at width `≤ 5/(4N)` only joins adjacent pairs `|n − j| = 1` in the top third `3n > N`; top-third mass `≤ (poleDefect + ‖x‖²)/log(N/3)`.
2. Perturbation: complete matrix − main matrix `≤ (2000δ + C/log(N/3))(poleDefect + ‖x‖²)` for widths in `[1/(2N), (1+δ)/N]` (`exists_perturbation_bound_transMetzler`); successor pairs `(kn, kn ± 1)` pay `δ + 2/N` via Chebyshev.
3. Main matrix: charge deficit `1 − q ≥ 1/128000` ⇒ coercivity `−2100000‖x‖² + poleDefect/1024000` up to `c ≤ 1 + 1/512000`; Ramanujan quasimodes with energies `> 1/20` ⇒ eigenvalue floor `1/25`; convex combination ⇒ `‖x‖²/60 + poleDefect/1.0752·10¹⁴`.
4. The reserve pays the perturbation for `δ ≤ 10⁻¹⁸`; no gauge is used.

**B. Optimizing the certified range**
1. Reference floor = conductor-one adjunction energy (self finite part + pole shift); no eventual floor can exceed it (conductor one attains it).
2. Young family: center cost split by parameter `λ`; optimizing gives `L(c) = f − 2000(c−1)(1 + root²)`, strictly decreasing on `[1, 1/q₀)` with a unique zero `c_*`; exact rational certificate `L(1 + 10⁻¹⁶) ≥ 1/200`.

**C. Twin breakdown**
1. Fejér–Abel: `Σ_{d≤M} cos(dθ)/d ≥ −4` ⇒ archimedean center kernel `≥ −(17/4)Σ n x_n²`; cross error `≤ 56M²` on vectors with `n x_n² ≤ 4`.
2. Witness: project `ω(n)/√n` onto the pole hyperplane `Σ x_n/√n = 0`; for pole-free `ω` (bounded `Σ ω(n)/n`) the twisted prime form reaches `(log M − γ − ε)Σx²`.
3. Sub-horizon dilution `M = ⌊(c'/c)N⌋` turns `log(1/(2πc')) + β/‖φ‖²` into `−log(c'/c_RE) < 0` times `log M`, beating `O(1)` center and cross terms.
4. Single prime flip: the twist changes only the prime matrix at separated widths; `primeSquareTrial` cancels the first prime correlation `4 log p/p`, leaving tail cost from `p³`; a three-conductor Ramanujan packet limit gives a negative margin at ratio `99/100`; zero padding transfers it to all larger ratios.

**D. Zero side**
1. Finite off-line support bounds the Hermitian negative index of `atomicShiftWeilGram` by `#rightZeros`, uniformly in `c`, `N`, `φ` (Krein index of `zetaKernel`).
2. One real zero contributes linearly in `c` on `x ≡ 1` (Cauchy–Schwarz `N² ≤ Σn^σ·Σn^{−σ}`).
3. A two-atom dipole `x₁ = 1, x₂ = −1` kills the whole lattice `½ + 2πik/log 2`; one off-line pair then makes `Re W < 0` at every `c`.

**E. RH receivers via Denjoy–Carleman synthesis**
1. Steklov averages cost one radius per derivative; summable radii `a_m = 1/(4(m+3)log²(m+3))` give a smooth limit with `∫|φ^{(q)}| ≤ A·12^q·W_q`.
2. Euler–Maclaurin synthesis of order `2⌈log log κ⌉ + 2` with quadrature ratio `≤ 24·rate⁻¹·B_φ·B + o(1)`; ratio `< e⁻¹` makes the error `O(log⁻²κ)`.
3. Mollify a negative test by the profile (stays negative, inherits the weight bounds), synthesize it on block `[N/B, N]`: any stable form is globally nonnegative iff eventually nonnegative on atomic families at super-Gevrey overlap.
4. Bounded rate `K`: window radius `½ log K + O(1)` (`B = ⌈1 + e^{2R+2}⌉`). RH = union over `K`.
5. Critical overlap: Fourier majorant `μ_B(c) = inf_q B^q W_q/c^q`, `log(1/μ_B(c)) ≍ c/log²c`; the sinc profile's tail `∫_c^{2c}|φ̂|² ≥ c·e^{−Kc/log²c}` (Jensen on sinc products, `π log 2` per period of `−log|sin|`) shows this is exact. Hence `c*_N ≍ L(log L)²`.

**F. Obstructions at growing overlap**
1. Divisor fiber: with Schur weights all divisors of `ℓ` share one lag and sum to `log ℓ`; the successor fiber grows like `log N` at every `c > 1`, is positive iff `c > N log(1+1/N)`, and tends to 0 at touching.
2. Factorial horizons `2Y! − 1`: one unit coordinate collects `Σ_{p≤Y}(log p)²/p → ∞`; the non-ratio prime matrix is eventually bounded iff `c ≤ 1`.
3. Adjacent dipole: synthesized mass / coefficient mass `= 1 − C_φ(t)/C_φ(0)`, `t ≤ 2/c`; no uniform Gram floor along `c_N → ∞`. The Gram is nondegenerate at every fixed width.
4. Prefix payment: the prefix block at `[1,M]` equals the complete matrix at overlap `cM/N`; one horizon makes it PosDef for all `cM ≤ N`; the full obligation is exactly the Schur complement.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| For every `ρ > 1` the plateau eventually frustrates every unimodular gauge | `transMetzlerProfile_frustrated_of_one_lt` | proved |
| Perturbation `(2000δ + C/log(N/3))(poleDefect + ‖x‖²)` | `exists_perturbation_bound_transMetzler` | proved |
| PosDef for every `c ∈ (0, 1 + 10⁻¹⁸]`; there is `c > 1` with PosDef; PosDef and frustrated at `rhoZero·atomSpacing N` | `eventually_completeWeilMatrix_posDef_of_mem_Ioc`, `exists_gt_one_eventually_completeWeilMatrix_posDef`, `eventually_transMetzler_atomSpacing_posDef_and_frustrated` | proved |
| PosDef on the full certified range `δ < certifiedOverlapIncrement` | `eventually_completeWeilMatrix_posDef_certified` | proved |
| Young family certifies a positive floor exactly for `1 ≤ c < c_*`; `c_* > 1 + 10⁻¹⁶`; floor `1/400` there | `transMetzler_young_positive_certificate_iff`, `transMetzlerCertifiedBoundary_explicit_lower`, `eventually_completeWeilMatrix_floor_at_explicit_young_ratio` | proved |
| Liouville twin negative at every `c > c_RE(φ)`; plateau `c_RE < ½`; thin plateaus `→ e/(2π)`; twin nonnegative below `fixedWidthRatio` | `eventually_liouville_weilQuadTw_neg_of_gt_robinEuler`, `eventually_liouville_weilQuadTw_neg_transMetzlerProfile`, `exists_plateau_liouville_weilQuadTw_neg_of_gt_exp_div_two_pi`, `liouville_weilQuadTw_nonneg_of_le_fixedWidthRatio` | proved |
| Every pole-free sign gauge and every cofinite flip breaks above `c_RE` | `eventually_signGauge_weilQuadTw_neg_of_gt_robinEuler`, `eventually_cofiniteFlip_weilQuadTw_neg_of_gt_robinEuler` | proved |
| Flipping the prime 11 breaks at every ratio `≥ 99/100` (incl. `2`, `cZero`) | `eventually_elevenFlip_negative_of_ratio`, `eventually_elevenFlip_negative_cZero` | proved |
| Finite off-line ⇒ uniform negative index `≤ #rightZeros`; tempered pair countermodel at every `c` | `hermNegIndex_atomicShiftWeilGram_le_of_finiteOffLine`, `isolatedPairConfig_atomic_negative_every_ratio` | proved (first is an implication) |
| Stable form ≥ 0 ⇔ eventual atomic nonnegativity at super-Gevrey overlap | `nonneg_iff_atomicFamilies_nonneg_of_stable_superGevrey`, `riemannHypothesis_iff_atomicFamilies_nonneg_of_superGevrey` | proved |
| RH ⇔ `steklovDCProfile` receiver at `L(log L)^β`, `β > 2`, and at `L(log L)² log log L` | `riemannHypothesis_iff_steklovDCProfile_nonneg_superGevrey`, `riemannHypothesis_iff_steklovDCProfile_nonneg_endpoint` | proved |
| Bounded rate `K` sees window `24eB⌈1+e^{2R+2}⌉ < K`; RH ⇔ all bounded rates; every divergent rate is a receiver | `nonneg_of_atomicFamilies_nonneg_of_rate`, `riemannHypothesis_iff_forall_bounded_rate`, `riemannHypothesis_iff_nonneg_of_divergent_rate` | proved |
| `c*_N ≍ L(log L)²` (majorant and exact sinc tail); rate law in critical units | `eventually_dcCriticalOverlap_le`, `eventually_le_dcCriticalOverlap`, `eventually_sincCriticalOverlap_le`, `eventually_le_sincCriticalOverlap`, `riemannHypothesis_iff_forall_sincCritical_multiple` | proved |
| Sinc tail `∫_c^{2c}|φ̂|² ≥ c·exp(−(8π/3+3000)c/log²c)` | `exp_mul_le_integral_norm_fourier_sincProfile_sq` | proved |
| Non-ratio prime matrix eventually bounded ⇔ `c ≤ 1` | `eventually_bounded_fullWeilNonRatio_action_iff` | proved |
| Successor fiber `~ log N` for `c > 1`; positive iff `c > N log(1+1/N)`; `→ 0` at touching | `plateauSuccessorFiber_atTop`, `plateauSuccessorFiber_pos_iff`, `tendsto_plateauSuccessorFiber_one` | proved |
| No uniform Gram floor along `c_N → ∞` | `no_uniform_plateau_atomic_mass_floor` | proved |
| Full PSD ⇔ prefix Schur complement PSD (prefix paid for `cM ≤ N`) | `eventually_completeWeil_posSemidef_iff_prefixSchur` | proved |
| Receiver bandwidth `→ 1`; `N < T^α` for all `α > 1` | `tendsto_superGevrey_bandwidth`, `eventually_superGevrey_length_lt_height_rpow` | proved |
| Positivity of the full matrix at any growing overlap | — | open |

## 6. Tools

**Developed**
- Top-collar adjacency and `poleDefect/log(N/3)` mass payment (`top_adjacent_of_log_gap_le`, `sum_sq_top_third_le`).
- Convex combination of eigenvalue floor and coercivity (`eventually_transMetzlerMainMatrix_floor_and_defect`).
- Uniform Fejér–Abel bound and center-kernel floor (`neg_four_le_sum_cos_div`, `sum_archimedeanCenterKernel_ge`).
- Pole-hyperplane witnesses for any bounded-harmonic sign twin (`exists_bounded_hyperplane_signTwin_witness`).
- Steklov calculus: derivative, Fourier multiplier, mass preservation, mean-zero two-average bound (`fourier_steklovAvg`, `abs_boxStek_two_le_of_meanZero`).
- Log-DC synthesis (`exists_dcLogSynthesis`) and the mollify-then-synthesize receiver argument.
- Fourier-tail majorant `μ_B` with two-sided bounds; Jensen for finite sinc products (`integral_prod_sinc_sq_ge`).
- Interval Montgomery–Vaughan band mass `∫_N^{101N}|Σx_n n^{it}|² ≥ 48N Σx²` (`dirichletPoly_highBand_mass`).
- Zero padding and rational ratio transfer (`atomicTest_zero_padding`); variable-ratio packet limits (`tendsto_ramanujanPacketTest_weil_variable`).
- Prime-square trial with Ramanujan expansion and flip tail bound (`primeSquareTrial_ramanujan`, `tendsto_primeSquareFlipBound`).

**To build**
- A replacement for coefficient-mass floors at growing overlap (synthesized-mass normalization).
- Control of the unbounded non-ratio correction against the archimedean terms past `c = 1` (the complete matrix keeps them; the bound alone diverges).
- A Schur-complement estimate for the tail after the paid prefix.
- Profiles outside the log-DC class to test whether `L(log L)²` can be lowered.

## 7. Open questions

1. Does ζ's complete matrix stay positive on a macroscopic range `c ≥ 2` (successor shells `kn ± r`, `r < c`)? Any proof must be selective: the 11-flip already fails at `99/100`.
2. Is the Young boundary `c_*` an actual sign change of the complete matrix, or only the end of this certificate family?
3. Is `L(log L)²` optimal among all smooth compactly supported profiles? Denjoy–Carleman non-quasianalyticity allows weights down to `Σ 1/(m log m)`-type divergence; the receiver argument needs `ratio < e⁻¹` at order `≈ log log κ`.
4. Can the positive Schur complement after the paid prefix be shown at overlap `c_N = r_N c*_N`? This is exactly RH.
5. Does finite off-line support plus ζ's zero density `log T/(2π)` force fixed-`c` positivity?

## 8. Traps

| Trap | Fact |
|---|---|
| "Crossing `c = 1` needs a new gauge" | No gauge exists for `ρ > 1`; positivity comes from the defect reserve and Ramanujan quasimodes. |
| "Past touching the non-ratio prime correction is a small perturbation" | Past `c = 1` it is controlled only relative to `poleDefect`; in Euclidean norm it is unbounded along factorial horizons for every fixed `c > 1`. |
| "`c_*` is where positivity fails" | `c_*` ends the certified Young family; failure beyond it is not proved. |
| "Twins survive to touching" | Liouville fails above `c_RE < ½`; every pole-free sign gauge and cofinite flip fails above `c_RE`; the 11-flip fails at `99/100`. |
| "Zero-side data decides fixed overlap" | `isolatedPairConfig` is tempered with one off-line pair and fails at every `c`. |
| "A bounded overlap rate proves RH" | A single `K` sees a window of radius `½ log K + O(1)`; RH needs all `K` or a divergent rate. |
| "`β > 2` is a technical loss" | `c*_N ≍ L(log L)²` exactly for the log-DC class; the endpoint `L(log L)² log log L` is reached. |
| "Coefficient mass controls synthesized mass" | Adjacent dipoles lose mass like `c⁻²`; no floor along `c_N → ∞`. |
| "Height can replace length" | `T_N = N/c_N` only up to asymptotic equivalence; `log T ~ log N`. |
| "Successor fiber turns on at `c > 1`" | It turns on at `c > N log(1+1/N) < 1`; at touching it is positive but `O(log N/N²)`. |
| Conditional statements | `weilQuad_atomicTest_nonneg_of_riemannHypothesis` and the finite off-line index bound are implications, not results about ζ. |

## 9. Context

**Uses**

| Programme | Imports | Role |
|---|---|---|
| RenormalizedArithmeticPotentialTheory | 11 | complete matrix, `poleDefect`, Ramanujan quasimodes, non-ratio matrix |
| HTGeometry | 9 | uniform limits of derivatives, Fourier decay, Montgomery–Vaughan, Young optimization |
| CriticalArithmeticCorrelationTheory | 9 | successor shells, touching autocorrelation, uniform quasimodes through touching |
| SpacingScaleHarmonicAnalysis | 8 | atoms, plateaus, DC profiles, EM synthesis, overlap coordinates |
| RHTower | 4 | Mertens, `(log p)²/p` lower bound, Weil–RH equivalence |
| ArithmeticLorentzianGeometry, ArithmeticCountingPositivity | 3 each | Metzler frustration, atoms; sign gauges, cofinite flips |
| SquareRootThreshold, SelectiveMultiscaleArithmeticPositivity | 2 each | tempered configurations; harmonic hyperplane |
| HeckeKreinToeplitz, ArithmeticIndexDescent | 1 each | Krein index of `zetaKernel`; real/complex Gram bridge |

**Used by**: CriticalArithmeticCorrelationTheory (2), CompletedArithmeticForms (2), EffectiveArithmeticHodgeTheory (1), RenormalizedArithmeticPotentialTheory (1), SpacingScaleHarmonicAnalysis (1), MainTheorems.

| Neighbour | Relation |
|---|---|
| CriticalArithmeticCorrelationTheory | carries positivity to every fixed overlap; imports the twin breakdown for selectivity |
| RenormalizedArithmeticPotentialTheory | owns the complete matrix; imports the prime-flip complete form and tail bound |
| CompletedArithmeticForms | imports the prefix Schur reduction and the Young optimization (`WeilPrefixIndex`, `WeilPrefixPayment`) |
| EffectiveArithmeticHodgeTheory | imports the Steklov super-Gevrey schedule |
| SpacingScaleHarmonicAnalysis | supplies Gevrey receivers (lowered here to `L(log L)²`); imports the band-mass bound for its Gamma reserve |

## 10. Big picture

The programme fixes the two ends of the atomic route. At bounded overlap, positivity of ζ's complete form is real, unconditional, and selective: it survives past the Metzler wall where no sign gauge helps, while Liouville, every pole-free gauge, and even a single flipped prime fail at the same or smaller overlap. The selectivity is driven by exact pole matching and by the arithmetic of the first prime correlations, not by zero information, which alone cannot decide anything at fixed overlap.

At growing overlap, RH is exactly a statement about the overlap `L(log L)²` (or any divergent multiple of it), and a bounded multiple sees only a window of logarithmic radius. Between the two ends sit three proved obstructions: the non-ratio prime correction becomes unbounded as soon as `c > 1`, the Gram floor collapses, and the remaining obligation after paying a prefix is a Schur complement that retains every arithmetic and archimedean term. An RH proof along this route must show positivity of that Schur complement at overlap `≈ log log N (log log log N)²`, and it must do so with an argument that fails for every twisted source.
