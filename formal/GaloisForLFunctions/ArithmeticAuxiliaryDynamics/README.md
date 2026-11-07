# Arithmetic Auxiliary Dynamics (AAD)

Namespace `GaloisForLFunctions.ArithmeticAuxiliaryDynamics`; umbrella `ArithmeticAuxiliaryDynamics.lean`.
Every theorem is unconditional. RH and zero-free strips appear only inside implications and equivalences.

## 1. Motivation

Every sign route to RH uses a positive form, a passive medium or an operator. This field asks what is left when all of them are removed. Over `𝔽_q` something is left: Stepanov's proof constructs an auxiliary, forces it to vanish beyond its size, and reads purity from the count, with no Hodge index. The vertical periodicity of the zeros does the rest, and a curve has it automatically.

AAD studies how the rational integers force zeros of `ζ` by two operations with no sign:

- **Construction.** An integer object forced to vanish beyond its size.
- **Transport.** A vertical return moving a zero to new heights.

The split matches RH. Construction aims at the count (ZAL side), transport at one-offs (AAL side). A proof in this field would be Weil's theorem in Stepanov's order over `ℤ`.

The central object is the **producer**: an integer stencil whose factorial ratio is an integer vanishing at primes to a controlled order. The field computes what producers can and cannot do. Its results are these.

- **The scale is exact at its top.** A rate `K^{-a}` forces `Re ρ ≤ 1 − a`, and rates up to `K^{-1/2}` give RH. No faster rate exists.
- **The construction is explicit.** Integer producers on polynomial alphabets reach the Vinogradov–Korobov rate, and under RH every rate `K^{-a}`, `a < 1/5`.
- **Parity costs nothing in the coefficients.** Parity neutral producers reach the same scales.
- **The linear theory is blind to purity, even over a curve.** There it stops at the trivial bound.
- **Transport lacks exactly one bound.** A bounded phase return at a zero forces infinitely many zeros.

What remains has to be nonlinear in the primes, which is the subject of the continuation RigidArithmeticOfCuts.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Stencil | `c : ℕ →₀ ℤ` | the ratio `∏ ⌊n/k⌋!^{c(k)}`, or the Dirichlet polynomial `D_c(s) = Σ c(k) k^{-s}` (`dirichletPoly`) |
| Multiplicity | `stepWeight c r` | `g(r) = Σ c(k) ⌊r/k⌋`, the order of the auxiliary at primes of `(n/(r+1), n/r]` |
| Increment | `increment c r` | `h = c * 1`, the discrete derivative of `g` |
| Producer | `IsProducer c m B` | balanced (`D_c(1) = 0`), `g ≥ 0`, `g ≥ m` on `[1, B)` |
| Alphabet | `AlphabetLE c K` | letters in `[1, K]` |
| Slope, excess, rate | `stencilSlope`, `excess`, `normSlope`, `rate` | `D_c′(1)`; `T = slope − m(1 − 1/B)`; `A = slope/(m(1−1/B))`; `ε = A − 1` |
| Peak, peak ratio | `peak`, `IsProducer.peakRatio` | `w = −D_c(0) = sup g`; `x = w/m` |
| Coefficient moments | `coeffMass`, `firstMoment`, `harmonicMass` | `Σ|c(k)|`; `Σ|c(k)|k`; `Σ|c(k)|/k` |
| Window sums | `windowSum`, `smoothSum`, `IsMeanZero` | the iterated sum `I_L^A f`, and periodic sequences of mean zero |
| Best rate | `bestRate K`, `HasRate f` | `A(K) − 1`; a family of producers of rate `≤ f(K)` |
| Möbius part | `mobiusPart T r` | `F_T(r) = −Σ_{b≤T} (μ(b)/b)(r mod b)` |
| Entangled letters | `entangled`, `moebiusWeight`, `IsMoebiusStencil` | letters `G P`, `P ≤ T` prime, all of weight `T/G` |
| Harmonic letters | `harmonicEntangled`, `harmonicWeights`, `harmonicCoefficient` | letters `G P` of weight `T/(P G)`, with total `Z = (T/G) Σ 1/P` |
| Mertens level | `IsMertensLevel δ` | `|M(y)| ≤ δ(T) y` on `y ≥ T`, `|m(T)| ≤ δ(T)`, and `δ(T) log T` small |
| Fake prime measure | `IsFakePrimeMeasure K u` | nonnegative `u` with `Σ u(r)(r mod k) = log k`, `k ≤ K`: the dual variables |
| Program | `IsFeasible`, `saw`, `objective`, `lpValue` | the real linear program of the best slope at a window |
| Parity balance | `parityBalance c`, `HasParityNeutralRate` | `D_{cλ}(1) = Σ c(k) λ(k)/k`, twice the sawtooth mass on letters with `Ω` odd |
| Spike | `neutralWeight`, `neutralCoefficient` | `F_T(⌊r/n⌋) − F_T(⌊r/(n+1)⌋)`, with `λ(n) = −1`, `λ(n+1) = +1` |
| Ledger | `ledger c a n` | `Σ_{d≤n} a(d) g(⌊n/d⌋)`; degree `j` is `a = Λ^{∗j}` |
| Liouville twin | `liouvilleWeight`, `twinFn` | the weight `−λΛ`, equal to `Λ` on odd prime powers and `−Λ` on even ones |
| Hecke dilation | `dilate j c` | `T_j : g ↦ g(⌊r/j⌋)` |
| Gauge twist, Adams | `gaugeTwist c ω`, `logMoment`, `adams j c` | `Σ c(k) ω(k) k^{-s}`; its derivatives; the letter `k` becomes `k^j` |
| Curve data | `frobeniusTraceR`, `curveCountR`, `weilPoly`, `IsPure` | power sums of a Frobenius pair, counts, numerators |
| Carlitz factorial | `carlitzSize`, `carlitzOrder` | `∏_{f monic, deg f = n} f` over `𝔽_q[T]` |
| Returns | `zetaReturnSet`, `ReturnsOnDisc`, `ReturnExponentLE` | shifts with `ζ(· + iτ) ≈ ζ` on a disc; their exponent |
| Phase returns | `IsPhaseReturn`, `TranslatesBoundedOn` | `τ_j → ∞` with `n^{-iτ_j} → 1` for all `n`; boundedness of translates on a domain |
| Hurwitz limit | `phaseAt`, `exists_gauge_point` | limits of translates, read as points of the gauge torus |

External: `stepWeight`, `IsBalanced`, `stencilSlope`, `stencilErrorConst` (ArithmeticKreinLangerTheory); `nairLattice_eq` (ArithmeticOfSquareRootPrecision); `GaugeTorus` (ArithmeticGaugeTheory); `zetaReturnSet`, `AsymptoticAbscissaLaw` (RHTower); `exists_abs_mertensM_le_vk_rate` (BezoutValuationIncidence); `mobiusMertens_subpower_of_zeroFree` (RHTower).

## 3. Language

- **Size against multiplicity.** The ledger: an auxiliary vanishing to order `m` on a set has size at least `m` times the counted mass.
- **Rate.** The excess of the normalized slope over the main term.
- **Peak.** The largest multiplicity, reached far out on the period.
- **Forced jump.** The increment `c(1)` at an integer divisible by no letter.
- **Entanglement.** Letters sharing a common factor, so that a small residue at one letter fixes `r` modulo that letter.
- **Mertens level.** The size of `M(y)/y` and `m(T)` from `T` on.
- **Certificate.** A producer with `ε ‖s‖ < 1` certifies `ζ(s) ≠ 0` on `Re s = 1`.
- **Parity neutral.** Parity balance `0`.
- **Degree.** The convolution power of `Λ` a ledger uses. Degree one is linear in `Λ`.
- **Return exponent.** The power of `T` in the measure of the returns in `[0, T]`.
- **Fibre over the identity.** A return is a limit of translates whose gauge point is `1`.
- **Siegel half, Liouville half, integrality exponent.** As in ArithmeticOfSquareRootPrecision.

## 4. Mechanisms

**Construction.**

1. **Rigidity.** `c = μ * h`, so the coefficients are the Möbius inversion of the increments. Two stencils with the same multiplicity on `[1, B]` have the same letters in `[1, B]`, and a constant window forces `c = m μ` on the window.
2. **Forced jumps.** At a rough `r`, `h(r) = c(1)`. All primes beyond the alphabet jump, and each costs slope. All multiplicity lives in fractional parts: `g(r) = −Σ c(k) {r/k}`.
3. **Palindrome.** `g(L − 1 − r) + g(r) = w` on a period, so `sup g = −D_c(0)` and the mean of `g` is `w/2`.
4. **Coefficient mass.** The pronic series weighs `g(r)` by `r^{-2}`, inversion needs `r^{-1}`: `Σ|c(k)| ≤ 2K (m(1 + log K) + (K + 1) T)`.
5. **Mellin.** `D_c(s) ζ(s) = Σ g(r)(r^{-s} − (r+1)^{-s})` on `Re s > 0`, proved by exact partial sums along multiples of a period.
6. **Mollifier.** A producer inverts `ζ` on `Re s = 1` by an integer Dirichlet polynomial: `‖D_c ζ(s) − m(1 − B^{-s})‖ ≤ ‖s‖ T`.
7. **Uncertainty.** At a zero, interpolating between `s = 1` (slope) and `s = 0` (peak): `m ‖1 − B^{-ρ}‖ ≤ ‖ρ‖ (4 + 1/β) w^{1−β} T^β`.
8. **Smoothing.** A window sum of a `k`-periodic sequence of mean zero is bounded by `k` times its size, for every window length, and is again periodic of mean zero. So `|I_L^A g(n) − L^A w/2| ≤ K^A Σ|c(k)|`. With `L = 3K`, `A ≍ log K`, this gives the peak law `w ≤ 100 (1 + log K)² (K T + m)`.
9. **Entanglement.** With letters `G P`: if `r mod G P < G` then `r ≡ s` modulo `G P`, where `s = r mod G`, and otherwise `r mod G P ≥ s + G`. So every `r` is compared with its near point `s`.
10. **Harmonic weights.** Only the `T/P` squarefree `b ≤ T` divisible by `P` see a failure at `P`. The weight `T/(P G)` pays exactly for that: `F_T(r) + Σ_P W_P (r mod G P) ≥ F_T(s) + Z s` for every `r`.
11. **Near law.** By the hyperbola method, `|F_T(s) − 1| ≤ s (|m(T)| + 2η (1 + log s))` when `|M(y)| ≤ η y` on `y ≥ T`.
12. **Hecke mixing.** `D_{c₁ + a T_j c₂}(s) = D_{c₁}(s) + a j^{-s} D_{c₂}(s)`, so positive dilations stay in the cone and add `(a/j) slope(c₂)` to the slope. The twist picks up `λ(j)`.
13. **Adjacent dilates.** With `λ(n) = −1`, `λ(n + 1) = +1`, the difference `T_n − T_{n+1}` adds parity balances and subtracts slopes, so parity per unit of slope grows by `2n`. On multiplicities it is a spike at `r = n`.
14. **The order law.** `(f′/f)^j f` has a pole of order `j − n` at a zero of order `n` when `j > n`, and it is regular when `j ≤ n`. This holds for every analytic `f`.

**Transport.**

15. **Propagation.** A return on a disc with locally bounded translates spreads to the whole upper quadrant, by Vitali and the identity theorem.
16. **Phases.** Dirichlet coefficients are read off at large `Re s`, so every phase returns, and a limit of translates is a point of the gauge torus.
17. **Pole.** The translates converge to `ζ` on `Re s > 1`, so they cannot stay bounded near `s = 1`.
18. **Minimum modulus.** A return of strength `m/2` on an isolating disc puts a zero in the translated disc, so the returns are counted by zeros.
19. **Propagation from the right.** Phase returns always exist and converge on `Re s > 1`. With bounded translates on a connected domain they converge on all of it, and Rouché moves the zero.

**Inherited from neighbouring programmes.**

- **Extremal position.** Under `¬RH` a zero of maximal angle is attained, and Hadamard factors compare in one direction there: `exists_zero_of_maximal_angle` (RigidArithmeticOfCuts).
- **Exact functional equation as rigidity.** A small critical-line defect forces the rational primes: `beurlingSystem_rigidity_of_small_critical_line_defect` (ArithmeticPositiveDuality).
- **Gamma speed as dominance.** Finite carriers are real above a horizon, where the Gamma speed beats the Euler speed: `re_carrier_speed_ge` (ZeroConfigurationGeometry).
- **Nair lattice.** `ψ(n + 1)` is the best integrality bound for integer polynomials of degree `≤ n`: `isGreatest_log_inv_nairIntegral` (ArithmeticOfSquareRootPrecision).

## 5. The questions and their answers

| # | Question | Answer | Lean |
|---|---|---|---|
| 1 | What replaces Frobenius? | Over `𝔽_q[T]` the stencil `1 − qX` is exact: size `q^n`, multiplicity `1_{deg P ∣ n}`, rate `0`, because `1/ζ` is a polynomial and norms are quantized. Over a curve the same stencil reads only `P(1)`, and at genus one nonnegativity at every extension is exactly `|a| ≤ q + 1`, that is `1 ≤ |α| ≤ q` for real roots: the strip, not the line. Purity is the opposite inequality: `N_n ≤ qⁿ + 1 + C q^{n/2}` for the curve and its twist holds iff `a² ≤ 4q`. Stepanov's auxiliary supplies that upper bound through the twist `x ↦ x^q`, which is nonlinear in the points. Over `ℤ` the linear replacement is `1/ζ` truncated to a finite stencil, with rate at least `c/(√K log K)`. No nonlinear replacement is known. | `carlitzOrder_sub`, `card_pow_eq_sum_irrDeg`, `coeff_balanced_stencil_mul`, `curveCountR_nonneg_iff`, `abs_root_bounds`, `exists_impure_of_stencil`, `isPure_iff_upper_bound`, `exists_half_floor` |
| 2 | What is the exact rate `A(K) − 1`? Is it a capacity? | `c₁/(√K (1 + log K)) ≤ A(K) − 1 ≤ exp(−(log K)^α)` for all `α < 3/5`. It is polynomial iff `ζ` has a zero-free strip. At each window it is a finite linear program with exact duality, attained on the dual side by a fake prime measure. The dual constraints are arithmetic sawteeth, not potentials, so it is not a capacity. | `exists_half_bracket_bestRate`, `exists_hasRate_rpow_iff`, `exists_extremal_fake_measure` |
| 3 | Where does the factor 2 of sieve parity go? | On the monotone cone, `1_{λ=−1} = (1−λ)/2` moves it to `Σ c(k) λ(k) L(⌊x/k⌋)`, and that cone is disjoint from producers. A single Hecke factor `1 + j^{1−s}` with `λ(j) = −1` neutralizes the parity balance of any producer and multiplies its normalized slope by exactly `2`. A difference of adjacent dilates does the same at slope cost `≈ 1/n`, so parity neutral producers reach the Mertens level: every rate `exp(−(log K)^α)`, `α < 3/5`, and polynomial parity neutral rates exist iff there is a zero-free strip. So the factor `2` is an artefact of one Hecke factor. A linear parity constraint on the coefficients is free, and parity is not read through them. | `two_mul_card_le_mean`, `eq_zero_of_balanced_of_increment_nonneg`, `IsProducer.parity_neutral_of_odd`, `exists_neutral_producer`, `hasParityNeutralRate_vk`, `exists_hasParityNeutralRate_rpow_iff` |
| 4 | Why do primes recur at a zero, if they do? | Phase returns always exist, so the primes recur along them freely. On any bounded return at a zero they must, and the limit is the identity of the gauge torus. What fails is the size of `ζ`: if finitely many zeros lie right of `σ`, every phase return has unbounded translates on every connected domain joining a zero right of `σ` to `Re s > 1`. Conversely, one bounded phase return at each zero gives AAL. Whether bounded phase returns exist at a zero is the exact open input. | `exists_isPhaseReturn`, `tendsto_phaseDefect_zero`, `tendsto_phase_one_of_limit_zeta`, `not_translatesBoundedOn_of_finite`, `IsPhaseReturn.infinite_zeros`, `asymptoticAbscissaLaw_of_boundedReturns` |
| 5 | Is a single off-line zero a contradiction with `N(x) = ⌊x⌋`? | Not by a linear identity. The mode of a zero is annihilated in every linear ledger, whose truncation moves by at most `w/β`, uniformly in `n`. A quadratic ledger does see a simple zero, as a pole with coefficient `a D_c(ρ)`, but the order law holds for every analytic function. So seeing a zero is not excluding it: any contradiction needs arithmetic input that meromorphy does not imply. | `hasSum_ledgerMode_eq_zero`, `IsProducer.norm_ledgerMode_self_le`, `exists_ladder_at_zero`, `tendsto_ladder_of_lt` |
| 6 | Does an explicit parity-selective auxiliary beat Vinogradov–Korobov? | Explicit integer producers reach it on polynomial alphabets, with or without parity neutrality. A rate with `α > 3/5` would give a zero-free region of exponent `1/α − 1 < 2/3`, wider than the classical one. The known families are certified by `M(x)`, so beating VK by a stencil requires a certificate that does not pass through `M(x)`. None is known. | `exists_moebius_producer_of_level`, `hasRate_vk`, `hasParityNeutralRate_vk`, `exists_re_le_of_hasRate_exp` |
| 7 | What nonlinear functional sees a zero mode and survives the Liouville twin? | The quadratic ledger does both. It has a pole at each simple zero, and its value on `Λ` exceeds its value on `−λΛ` by at least `4 m log 2 Σ log p` over primes with `4p ≤ n < 4pB`, against `2 w ψ(√n)` for the linear ledger. The separation goes through prime squares, which are known, so it carries no new information about the primes. A functional that separates the twin through the primes themselves is not known. | `exists_ladder_at_zero`, `lseries_ladder`, `IsProducer.ledger_twin_gap`, `IsProducer.abs_ledger_twin_le` |
| 8 | What is the fake prime measure closest to the true one, for each `K`? | At each window `B` at most the period there is an extremal one, supported on one period, of largest window mass among all consistent measures. That mass over the pronic mass `1 − 1/B` is the exact best normalized slope. At the best window it lies between `1 + c₁/(√K (1 + log K))` and `1 + exp(−(log K)^α)` times the pronic mass. Its explicit form is open. At infinite level only the pronic measure is consistent. | `exists_extremal_fake_measure`, `exists_extremal_gap`, `exists_extremal_bracket`, `IsFakePrimeMeasure.hasSum_slack`, `forall_isFakePrimeMeasure_iff` |

## 6. The scale of the rate

| Input | Output | Lean |
|---|---|---|
| zero-free strip `Re s > Θ`, `Θ < 1` | every rate `K^{-a}`, `a < (1 − Θ)/(3 − Θ)` | `hasRate_of_zeroFree_sharp` |
| RH | every rate `K^{-a}`, `a < 1/5` | `hasRate_of_riemannHypothesis_sharp` |
| rate `K^{-a}` | `Re ρ ≤ 1 − a` | `re_le_of_hasRate_rpow_half` |
| rates `K^{-a}` for all `a < 1/2` | RH | `riemannHypothesis_of_hasRate_half` |
| any `a > 1/2` | impossible | `not_hasRate_rpow_of_half_lt` |
| every producer on `[1, K]` | `ε ≥ c₁/(√K (1 + log K))` | `exists_half_floor` |
| certificate at height `τ` | `√K (1 + log K) ≳ |τ|` | `exists_necessary_alphabet_half` |
| rate `exp(−(log K)^α)` | `Re ρ ≤ 1 − c (log ‖ρ‖)^{1−1/α}` | `exists_re_le_of_hasRate_exp` |
| VK bounds for `M` and `m` | rate `exp(−(log K)^α)`, `α < 3/5` | `hasRate_vk` |

So under RH the exponent of the rate lies in `[1/5, 1/2]`. The two directions match on the exponent `α = 3/5` at the VK scale, and up to a constant in the exponent at the polynomial scale.

## 7. Pillar theorems

| Theorem | Lean |
|---|---|
| Rigidity: `c = μ * h`; the window fixes the letters below it | `coeff_eq_moebius_increment`, `coeff_eq_of_constant_window`, `coeff_eq_of_stepWeight_eq` |
| Forced jumps and the rough floor | `increment_of_isRough`, `IsProducer.sum_rough_le_excess`, `exists_floor_normSlope` |
| Palindrome; peak; mean `w/2` | `IsProducer.stepWeight_reflect`, `IsProducer.stepWeight_le_peak`, `IsProducer.two_mul_sum_range_stepWeight` |
| Coefficient mass law; sharp Chebyshev bound | `IsProducer.coeffMass_le`, `IsProducer.psi_le_sharp` |
| Mellin transform of a stencil | `hasSum_mellin` |
| Mollifier and certified non-vanishing on `Re s = 1` | `IsProducer.norm_mollifier_le`, `IsProducer.le_norm_dirichletPoly_mul_zeta` |
| Uncertainty law; absolute constant `ε x ≥ c₀` | `IsProducer.uncertainty_law`, `IsProducer.zero_law`, `exists_uncertainty_constant` |
| **The smooth mean value and the peak law** | `abs_smoothSum_stepWeight_sub_le`, `IsProducer.peak_le_window`, `IsProducer.peak_le` |
| **The half scale: floor, reading, RH at the end of the scale** | `exists_half_floor`, `re_le_of_hasRate_rpow_half`, `riemannHypothesis_of_hasRate_half`, `not_hasRate_rpow_of_half_lt`, `exists_half_bracket_bestRate` |
| Rational weights clear exactly to integer stencils | `exists_stencil_of_weights`, `exists_producer_of_weights` |
| The explicit Möbius producer | `moebiusWeight_nonneg`, `exists_moebius_producer`, `exists_moebius_producer_of_level` |
| **Harmonic entanglement and the one-fifth rate** | `abs_mobiusPart_sub_le`, `mobiusPart_add_harmonicEntangled_ge`, `exists_harmonic_producer`, `hasRate_of_zeroFree_sharp`, `hasRate_of_riemannHypothesis_sharp` |
| **A Mertens level gives a rate; polynomial rate ⇔ zero-free strip** | `eventually_producer_of_level`, `exists_hasRate_rpow_iff` |
| **Explicit integer producers at the VK rate** | `isMertensLevel_vk`, `hasRate_vk` |
| **Exact LP duality; the extremal fake prime measure and its distance from the truth** | `IsFakePrimeMeasure.le_normSlope`, `exists_producer_of_feasible`, `exists_extremal_fake_measure`, `exists_extremal_bracket` |
| **Parity: the factor of two, and parity neutral producers at the Mertens level** | `IsProducer.parity_neutral_of_odd`, `exists_liouville_pattern`, `exists_neutral_producer`, `exists_neutral_producer_of_level`, `hasParityNeutralRate_vk`, `exists_hasParityNeutralRate_rpow_iff` |
| Disjoint cones; parity ledger | `eq_zero_of_balanced_of_increment_nonneg`, `meanValue_pos`, `two_mul_coeff_one_mul_card_le` |
| Blindness of the linear ledger to zeros and to the twin | `hasSum_ledgerMode_eq_zero`, `IsProducer.norm_ledgerMode_self_le`, `IsProducer.abs_ledger_twin_le` |
| **The ledger ladder: the order law, its generating function, the twin gap** | `tendsto_ladder_of_lt`, `tendsto_ladder_of_le`, `exists_ladder_at_zero`, `lseries_ladder`, `sum_Icc_mul_incrementFn`, `IsProducer.ledger_twin_gap` |
| No positive Hecke amplification | `stepWeight_dilate`, `IsProducer.add_dilate`, `IsProducer.normSlope_add_dilate` |
| Multiplicity and zero estimates on the gauge torus; Adams duality | `exists_logMoment_ne_zero`, `analyticOrderAt_gaugeTwist_lt`, `sum_divisor_gaugeTwist_le`, `gaugeTwist_adams`, `card_support_adams` |
| Siegel's lemma with parity constraints | `exists_stencil_of_constraints`, `exists_parity_stencil`, `not_isProducer_of_support` |
| No early return of a producer's letters | `IsProducer.harmonicMass_le`, `IsProducer.le_of_phase_return` |
| Returns are returns of the primes; the pole's price | `tendsto_translateDiff_zero`, `tendsto_phaseDefect_zero`, `not_bounded_near_pole` |
| Hurwitz limit set embeds in the gauge torus | `exists_tendsto_phase`, `exists_gauge_point`, `coeff_eq_zero_of_hasSum_zero` |
| The transport count; the return exponent reads the zero | `volume_returnSet_le_zeroCount`, `riemannZeta_eq_zero_iff_returnExponent`, `returnExponent_jump` |
| **The missing input of transport** | `exists_isPhaseReturn`, `IsPhaseReturn.tendstoLocallyUniformlyOn`, `IsPhaseReturn.infinite_zeros`, `not_translatesBoundedOn_of_finite`, `asymptoticAbscissaLaw_of_boundedReturns` |
| Frobenius as a factorial stencil; exact ledger | `carlitzOrder_sub`, `carlitzSize_eq_sum_order`, `card_pow_eq_sum_irrDeg` |
| **The curve stencil stops at the trivial bound; purity is an upper bound** | `coeff_balanced_stencil_mul`, `coeff_curve_tail`, `curveCount_nonneg_iff`, `curveCountR_nonneg_iff`, `abs_root_bounds`, `exists_impure_of_stencil`, `isPure_iff_upper_bound` |
| Battery: golden obeys transport and fails the count; continuous counts have no multiplicity | `goldenL_shift`, `goldenL_deepZero`, `golden_fails_count`, `continuous_multiplicity_eq_zero` |
| The prime kernel as a commutator of logarithmic dilations | `timeMultiply_commutator`, `dilationSum_primeRaise`, `iterate_primeRaise_eq_mobius` |

## 8. Tools

**Developed.**

- Stencil calculus: increments, Möbius inversion, palindrome, moments of coefficients, Hecke action.
- **Size bounds for signed stencils past sup-norm**: the smooth mean value and peak law, the coefficient mass law, the uncertainty law.
- **An explicit positivizer**: entangled letters with harmonic weights turn a signed Möbius sawtooth into an integer producer on the alphabet `T²/δ`, up to logarithms.
- `exists_stencil_of_weights`, `exists_producer_of_feasible`: exact clearing of rational weights, and rational approach to any real feasible weight.
- **LP duality**: fake prime measures as certificates of floors, with no gap at any window.
- Dictionary between rates and zero-free regions in both directions.
- **Zero and multiplicity estimates on the gauge torus**: order below the number of letters at every point of plane and torus; zeros in a disc of radius `r` about a point far to the right at most `(log(2Σ|c(k)|/|c(1)|) + 2 r log K)/log 2`, uniformly in the gauge point. On the torsion grid, full multiplicity costs support `2^{qr}` (`arithmeticAuxiliary_multiplicity_vanishes_iff`, ArithmeticHarmonicAnalysis).
- **Siegel's lemma with parity constraints**: balanced, parity balanced integer stencils on `(B, K]` of height `((K − B) K!)^{2/(K − B − 2)}`.
- **A parity neutralizer**: the spike `T_n − T_{n+1}` at a Liouville pattern, which exists in every `[N, 4N]`.
- **Effective Kronecker at arithmetic scale**: if `ε ‖s‖ ≤ ½` at `s = 1 + iτ`, a simultaneous return of the letters with phase defect `θ` forces `m(1 − 1/B)/2 ≤ θ L₁ ‖ζ(s)‖`, where `L₁ = Σ|c(k)|/k`.
- **Universality at prescribed base points, in rigid form**: a global limit of translates on the quadrant is determined by a gauge point. Its quantitative form at typical heights, where a simultaneous almost period of the phases up to `M` is a return shift, is `exists_headPhaseReturnSet_zetaReturn_typicalHeight` (RHTower).
- **Transport count**: returns against zeros, with the jump of the return exponent at tolerance `≍ r^D`.
- **Ledgers that are not blind**: the ladder of degrees.

**To build.**

- A certificate of a producer's rate that does not pass through `M(x)`.
- A smaller alphabet at a given level. The family has peak `≍ K ε`, which the peak law allows, and the uncertainty law only asks for `1/ε`. Closing that gap would raise the RH rate.
- A local form of the transport theorem: returns on a disc with polynomially bounded translates and polynomially small error.
- Arithmetic input for a nonlinear ledger: a bound on `Σ_d Λ^{∗j}(d) g(⌊n/d⌋)` that is not implied by meromorphy.
- Pointwise bounds below the VK length, and a metric geometry of Beurling systems near the integers (RigidArithmeticOfCuts).

**A tool that does less than it appears to.** Siegel's lemma exists here, and it does not produce auxiliaries. By rigidity a window has no free parameter below it, a stencil with no letter `1` is never a producer, integrality is free, and the condition `g ≥ 0` is an inequality on a whole period. The problem is a real linear program.

## 9. Open research topics

1. **Certification without Möbius sums.** The Möbius producer is explicit, and its rate is certified by `M(x)`. Is there a family with non-constant multiplicity on its window whose rate has an independent proof?
2. **The exact exponent.** Under RH the exponent of the rate lies in `[1/5, 1/2]`. The obstruction on the construction side is that a level `δ ≍ T^{-1/2}` forces `T ≍ δ^{-2}`, and the far letters have peak `≍ T²`. Is there a positivizer with peak near `1/ε`? Does a rate at `1/2` hold for any family?
3. **Parity through the primes.** Parity neutrality in the coefficients is free. The twin gap goes through prime squares. What functional separates a twin that agrees with `Λ` on all prime powers up to a level?
4. **Nonlinear arithmetic input.** The ladder sees zeros, and nothing bounds its modes. Which degree-two statement over `ℤ` has no analogue for a general meromorphic function?
5. **Bounded phase returns.** Is there, at a zero right of `½ + h`, a phase return whose translates are bounded on a connected domain joining the zero to `Re s > 1`? One at each zero gives AAL. Any such sequence carries a spike at the pole.
6. **Curves.** Purity is the upper bound for the curve and its twist. Write Stepanov's auxiliary in ledger language: which degree in the points is the twist `x ↦ x^q`, and what is its analogue at the integers? Over a curve the linear theory stops at the trivial bound, so this is the actual model.
7. **The extremal measure.** Describe the extremal fake prime measure explicitly. A limit as `K → ∞` that keeps all moments is the pronic measure, so how do the extremal measures lose moment mass to infinity, and at what rate in `K`?

## 10. Traps

| Trap | Fact |
|---|---|
| The size of a stencil is its alphabet | The coefficient mass is bounded by alphabet and rate: `Σ|c(k)|/m ≤ 2K(1 + log K + (K+1)ε)` |
| The first moment limits the floor | A sharp cut gives only `K^{-3/4}`. Window sums remove the first moment, and the true end of the scale is `1/2` |
| Rates near `K^{-3/4}` are the RH level | No rate past `K^{-1/2}` exists. Rates up to `K^{-1/2}` give RH, and RH gives at least `1/5` |
| Integrality forces factorial alphabets | Entangled letters give an alphabet `≈ T²/δ`, and clearing rational weights is exact |
| Integer coefficients make this a Diophantine problem | Integrality costs nothing: every rational weight clears, and rational points approach every real feasible cost |
| Uniform far weights are natural | A failure at `P` can only cost `T/P`, and weights `∝ 1/P` drop the total from `π(T) T/G` to `(T/G) log log T` |
| A stencil past VK would be independent of primes | Its rate reads a zero-free region directly, and the known family contains `μ` by rigidity |
| A small peak is compatible with a small rate | `ε x ≥ c₀`: a small rate forces a large peak, and the peak law bounds it by `K ε` up to logarithms |
| The Hecke algebra amplifies | Positive dilations multiply the normalized slope by `1 + a/j` |
| The sieve's 2 obstructs producers | `h ≥ 0` is a different, disjoint cone |
| A parity constraint costs a factor of two | That is one Hecke factor. A difference of adjacent dilates costs about `1/n` |
| Parity neutral means parity broken | The balance is one linear functional of the coefficients. It reads nothing about the primes |
| Exact linear identities see zeros | The mode of a zero is annihilated in the ledger of every balanced stencil |
| A ledger that sees a zero excludes it | The order law holds for every analytic function, and the exact Selberg combination `ζ(A² + A′) = ζ″` is blind again (`riemannZeta_mul_selberg`) |
| The linear ledger reads parity | `g(⌊n/d⌋)` never reads `Ω(d)`, so the twin is within `2 w ψ(√n)` |
| A quadratic separation of the twin is parity breaking | It reads prime squares, which are known |
| Stencils prove Weil over a curve | They reach `|a| ≤ q + 1`. The numerator `(1 − u)(1 − qu)` has all counts nonnegative. Purity is an upper bound on counts, which a stencil's nonnegativity does not give |
| Transport proves purity | The golden fake returns exactly and fails the count |
| Multiplicity survives continuous counts | `Σ c(k) x/k = 0`: all of it is the sawtooth |
| The primes block returns at a zero | Phase returns always exist. What is missing is a bound on `ζ` along them |
| Returns accumulate into a contradiction | Their measure is at most `2r` times the zero count, so strong returns are as rare as zeros |
| Adams operators raise multiplicity | They keep the number of letters and raise the alphabet to a power |
| The rate is a capacity | Sawtooth moments are not potentials |

## 11. Test cases

| Case | Status |
|---|---|
| Weil over `𝔽_q[T]` | The Carlitz stencil is exact: `carlitzOrder_sub`, `card_pow_eq_sum_irrDeg` |
| Weil for curves through Stepanov | `stepanov_count` is proved by the auxiliary, by size against multiplicity (`sum_le_natDegree_of_vanishing`), and the auxiliary is not a stencil. The linear stencil stops at `|a| ≤ q + 1`, and purity is the upper bound `isPure_iff_upper_bound` |
| Kloosterman data | Weil's `2√p` is `kloosterman_weil_bound`. The stencil reads a real trace only up to `|K| ≤ p + 1`, which the trivial bound `|K| ≤ p − 1` satisfies: `curveCountR_nonneg_iff`, `curveCountR_nonneg_of_trivial` |
| Continuous Beurling systems | All multiplicity vanishes: `continuous_multiplicity_eq_zero` |
| Golden | Exact periodic returns with a zero right of `½`, and the count fails: `goldenL_shift`, `goldenL_deepZero`, `golden_fails_count` |
| Liouville twin | Linear ledger blind, quadratic ledger separated through prime squares: `IsProducer.abs_ledger_twin_le`, `IsProducer.ledger_twin_gap` |

## 12. Place in the research

| Direction | Programme | What |
|---|---|---|
| Uses | ArithmeticKreinLangerTheory | stencils, factorial ratios, ledgers, pronic series, ceilings |
| Uses | RHTower | Mertens bounds, `mobiusMertens_subpower_of_zeroFree`, return sets and their dichotomy, residues of `ζ′/ζ`, Stepanov and Weil–Kloosterman function-field sums |
| Uses | BezoutValuationIncidence | Vinogradov–Korobov rates for `M` and `m` |
| Uses | HTGeometry | Vitali on connected domains, Jensen zero counts |
| Uses | ArithmeticOfSquareRootPrecision | golden calibration, Liouville identity |
| Uses | ArithmeticCastelnuovoSeveri | large almost periods of a finite family of phases |
| Used by | ArithmeticKreinLangerTheory | `exists_producer_with_quantitative_cost` takes the coefficient bound and `IsProducer` from here |
| Used by | RigidArithmeticOfCuts | fake prime measures, Hecke action, the VK rate, Mellin transform, twin ledger |

| Neighbour | Relation |
|---|---|
| RigidArithmeticOfCuts | the continuation where the linear theory closes: the cut system and its kernel, uniqueness of the fake prime measure at infinite level, exact and inexact ledgers, the zero of maximal angle |
| ArithmeticProduction | necessary lengths and parity filters; AAD proves the corresponding laws for stencils |
| ArithmeticOfSquareRootPrecision | precision classes; the Nair lattice is the univariate face |
| ArithmeticInnerFunctionTheory | its complement: it keeps positivity, since a Blaschke mass is a positive quantity |
| ArithmeticGaugeTheory, ArithmeticHarmonicAnalysis | the gauge torus and Adams multiplicity; AAD maps limits of translates into the torus |
| ArithmeticDiscreteness | repulsion amplifies a zero; AAD shows the linear ledger does not see it |
| ZeroConfigurationGeometry | the structure of the failure of AAL; `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap` is the world transport must exclude |

Compared with Nyman–Beurling: the signed `L²` distance is RH-equivalent, with `bdDistDiscrete` (RHTower) as its integer-free form. AAD works at `L¹` with `g ≥ 0`, where the uncertainty law is the interpolation between `L¹` and `L^∞`.

## 13. Success criteria and contributions

A contribution belongs to this field only if it

- uses no quadratic form with a sign, no self-adjoint operator and no Hadamard positivity;
- can be read over `𝔽_q`, where Hasse–Weil must come out in the same language;
- separates rational primes from continuous Beurling systems and from discrete near-fakes;
- is tested on the battery of §11;
- states which scale of the rate it moves, or which class of arguments it excludes;
- if it uses a ledger, is not blind to zero modes, so it is not linear in `Λ` read through floors.

The linear theory has answered its questions in the form they were asked. The field succeeds further if it does one of the following.

- Certifies a producer without Möbius sums, past a known zero-free region.
- Proves that no such certificate exists in a stated class.
- Closes the exponent gap `[1/5, 1/2]` under RH.
- Exhibits a bounded phase return at a zero, or excludes one in a stated class.
- Gives a nonlinear statement over `ℤ` that proves Hasse–Weil over `𝔽_q` in the same language and has no analogue for a general meromorphic function.

## 14. Big picture

The linear construction over `ℤ` is exact at the top of its scale. Producers exist explicitly at polynomial alphabet and integrality costs nothing. A Mertens level gives a rate, a rate gives a zero-free region, and the two match at the VK exponent and at the polynomial scale up to constants. A rate `K^{-a}` reads `Θ ≤ 1 − a`, and the scale ends at `a = 1/2`, exactly where the reading reaches `½`. Each window is a linear program with an extremal fake prime measure. Parity neutrality is free at every proved scale.

Rigidity explains why. Every stencil with a constant window contains `μ`, because a window of constant multiplicity is the inverse of `ζ`. So a stencil is `1/ζ` in integer form, and it has no force beyond a bound on `M(x)`, unless a certificate is found that does not pass through `M(x)`.

The curve shows that this is not a defect of the integers. Over a curve a linear stencil reads one value of the numerator, and its window is the critical strip. The linear theory reaches the analogue of `ζ(1 + it) ≠ 0` there too. Purity is a different inequality, an upper bound on counts at square root precision, and Stepanov gets it from a twist inside the auxiliary, which is nonlinear in the points. So the question that remains is what plays the part of that twist over `ℤ`. The ladder of degrees is a first language for it: it sees a zero of order `n` at degree `n + 1`. But the order law is a fact about all analytic functions, and it needs an arithmetic bound that no source supplies.

Transport has a parallel result. Phase returns always exist, so the primes never block a return, and one bound on `ζ` along them would give AAL. Strong returns are counted by zeros, so they are as rare as the zeros they move. On the fake side transport is free and the count fails, which is why neither half can stand alone.
