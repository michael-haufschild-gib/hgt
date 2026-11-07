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
- **The construction is explicit.** Integer producers on polynomial alphabets reach the Vinogradov–Korobov rate, and under RH every rate `K^{-a}`, `a < 1/4`.
- **The rate is the Mertens function.** Any producer of rate `ε` has `|M(n)| ≤ ε n + 12 (w/m) √n + K`, by a three-line identity. With the construction, the scale of the rate and the scale of `M` are one scale.
- **Fake prime measures are profinitely rigid.** At high level every fake prime measure gives each residue class its true mass. Its freedom is archimedean only.
- **Parity costs nothing in the coefficients.** Parity neutral producers reach the same scales.
- **The linear theory is blind to purity, even over a curve.** There it stops at the trivial bound.
- **Transport lacks exactly one bound.** At an aligned shift, a bound on `ζ` polynomial in the aligned length moves a zero. Boundedness is not needed.

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
| Aligned shift | `IsHeadReturn N τ` | the phases of `1, …, N` are within `1/N` of `1` at `τ` |
| Hurwitz limit | `phaseAt`, `exists_gauge_point` | limits of translates, read as points of the gauge torus |
| Slack along floors | `producerSlack` | `g − m 1_{[1,B)}`, which is nonnegative on `r ≥ 1` |
| Class mass, folding | `classMass`, `foldMeasure`, `pronicMeasure` | the mass of a residue class; the measure folded onto `[1, q)`; the true measure `1/(r (r+1))` |
| Shape producer, target mass | `IsShapeProducer c m S`, `targetMass u S` | a producer with `g ≥ m` on an arbitrary finite set `S`; the mass of a measure on `S` |
| Compensation | `largePrimes`, `IsCompensation`, `compCoeff`, `compCount` | the primes in `(2y + 2, y²]`; a nearby product `d_P = m t` of coprime factors `≤ 2y + 2`; the letters `μ + Σ_P μ(·/P) − Σ_P μ(·/d_P)`; the multiplicity `1` plus spikes on `[P, d_P)` |
| Far letters | `compPairs`, `compDefect`, `farModulus` | the odd prime powers `q^e ≤ y²`, `q ≤ 2y + 2`; the mass `D_Q` of the letters `Q` divides; the power of two `G_Q ∣ G` with `G_Q Q ≤ 3G` |

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
15. **The ledger of `μ` is the peak.** `Σ_d μ(d) ⌊N/d⌋ = 1`, so the ledger of `μ` is `−w` once `n ≥ K`. With the slack bound `Σ_{d ≤ n} (g − m 1_{[1,B)})(⌊n/d⌋) ≤ n T + 2 w √n`, this gives `m |M(n) − M(⌊n/B⌋)| ≤ n T + 3 w √n`, and summing over the scales `n/Bʲ` turns `T/m` into the rate exactly.
16. **The harmonic sum from `M` alone.** The hyperbola method at `n = T V` gives `|m(T)| ≤ 2/V + η (2 + log V)` when `|M(y)| ≤ η y` on `y ≥ T`.
17. **Folding and jumps.** A measure of level `q` folds onto `[1, q)` and keeps its moments at the divisors of `q`. If `r ≥ N!`, the residue modulo `m!` jumps at some `m ≥ N`, and a jump makes `r mod (m+1)!` at least `m!`. The moment `log (m+1)!` pays for it, so folded measures are tight, with no input about primes.

**Transport.**

18. **Propagation.** A return on a disc with locally bounded translates spreads to the whole upper quadrant, by Vitali and the identity theorem.
19. **Phases.** Dirichlet coefficients are read off at large `Re s`, so every phase returns, and a limit of translates is a point of the gauge torus.
20. **Pole.** The translates converge to `ζ` on `Re s > 1`, so they cannot stay bounded near `s = 1`.
21. **Minimum modulus.** A return of strength `m/2` on an isolating disc puts a zero in the translated disc, so the returns are counted by zeros.
22. **Propagation from the right.** Phase returns always exist and converge on `Re s > 1`. With bounded translates on a connected domain they converge on all of it, and Rouché moves the zero.
23. **Three circles.** An aligned shift is within `4/N` of `ζ` on `Re s ≥ 2`. A bound `M` on a larger disc interpolates to `(4/N)^{1−t} (2M)^t` at the zero, so `M = N^A` is enough.

**Compensation.**

24. **Large primes leave the alphabet.** With `T = y²`, let `h` jump at a prime `P > 2y + 2` and fall back at a nearby product `d_P = m t` of coprime factors `≤ 2y + 2`, with `d_P ≤ P (1 + 4/y)`. The letters `μ ∗ h` vanish on every `k ≤ T` with a prime factor above `2y + 2`, so every letter is `(2y + 2)`-smooth.
25. **Trivial counting beats the primes.** Past `T` the partial sums of the letters are `M(x) + Σ_P (M(⌊x/P⌋) − M(⌊x/d_P⌋))`. A point `x/n` lies within `4x/(ny)` of at most `4x/(ny) + 1` primes, so the sum over `P` is at most `5x (1 + log x)/y` with no input about primes. The compensation costs `1/y`.
26. **Far letters at one scale.** Only odd prime powers `Q = q^e`, `q ≤ 2y + 2`, can separate `r` from `s = r mod 2^g`. The far letter `G_Q Q`, `G_Q ∣ 2^g`, has size about `3 · 2^g` for every `Q`. It pays while `s < G_Q`, and past that `2Qs ≥ 3 · 2^g`, so the linear term pays. The whole far cost is the weighted defect `Σ_Q Q D_Q ≲ y³`, over `2^g`.

**Inherited from neighbouring programmes.**

- **Extremal position.** Under `¬RH` a zero of maximal angle is attained, and Hadamard factors compare in one direction there: `exists_zero_of_maximal_angle` (RigidArithmeticOfCuts).
- **Exact functional equation as rigidity.** A small critical-line defect forces the rational primes: `beurlingSystem_rigidity_of_small_critical_line_defect` (ArithmeticPositiveDuality).
- **Gamma speed as dominance.** Finite carriers are real above a horizon, where the Gamma speed beats the Euler speed: `re_carrier_speed_ge` (ZeroConfigurationGeometry).
- **Nair lattice.** `ψ(n + 1)` is the best integrality bound for integer polynomials of degree `≤ n`: `isGreatest_log_inv_nairIntegral` (ArithmeticOfSquareRootPrecision).

## 5. The questions and their answers

| # | Question | Answer | Lean |
|---|---|---|---|
| 1 | What replaces Frobenius? | Over `𝔽_q[T]` the stencil `1 − qX` is exact: size `q^n`, multiplicity `1_{deg P ∣ n}`, rate `0`, because `1/ζ` is a polynomial and norms are quantized. Over a curve the same stencil reads only `P(1)`, and at genus one nonnegativity at every extension is exactly `|a| ≤ q + 1`, that is `1 ≤ |α| ≤ q` for real roots: the strip, not the line. Purity is the opposite inequality: `N_n ≤ qⁿ + 1 + C q^{n/2}` for the curve and its twist holds iff `a² ≤ 4q`. Stepanov's auxiliary supplies that upper bound through the twist `x ↦ x^q`, which is nonlinear in the points. Over `ℤ` the linear replacement is `1/ζ` truncated to a finite stencil, with rate at least `c/(√K log K)`. No nonlinear replacement is known. | `carlitzOrder_sub`, `card_pow_eq_sum_irrDeg`, `coeff_balanced_stencil_mul`, `curveCountR_nonneg_iff`, `abs_root_bounds`, `exists_impure_of_stencil`, `isPure_iff_upper_bound`, `exists_half_floor` |
| 2 | What is the exact rate `A(K) − 1`? Is it a capacity? | It is the Mertens function up to a polynomial change of scale: `|M(n)| ≤ 3 ε n` for `n ≥ (D (1 + log K)³ K)²`, and a bound on `M` gives producers on polynomial alphabets. So `c₁/(√K (1 + log K)) ≤ A(K) − 1 ≤ exp(−(log K)^α)` for all `α < 3/5`, and it is polynomial iff `M(n) ≪ n^{1−σ}` iff `ζ` has a zero-free strip. At each window it is a finite linear program with exact duality, attained on the dual side by a fake prime measure. The dual constraints are arithmetic sawteeth, not potentials, so it is not a capacity. | `exists_abs_mertens_le_three_rate`, `hasRate_exp_iff_mertens`, `exists_hasRate_rpow_iff_mertens`, `exists_half_bracket_bestRate`, `exists_hasRate_rpow_iff`, `exists_extremal_fake_measure` |
| 3 | Where does the factor 2 of sieve parity go? | On the monotone cone, `1_{λ=−1} = (1−λ)/2` moves it to `Σ c(k) λ(k) L(⌊x/k⌋)`, and that cone is disjoint from producers. A single Hecke factor `1 + j^{1−s}` with `λ(j) = −1` neutralizes the parity balance of any producer and multiplies its normalized slope by exactly `2`. A difference of adjacent dilates does the same at slope cost `≈ 1/n`, so parity neutral producers reach the Mertens level: every rate `exp(−(log K)^α)`, `α < 3/5`, and polynomial parity neutral rates exist iff there is a zero-free strip. So the factor `2` is an artefact of one Hecke factor. A linear parity constraint on the coefficients is free, and parity is not read through them. | `two_mul_card_le_mean`, `eq_zero_of_balanced_of_increment_nonneg`, `IsProducer.parity_neutral_of_odd`, `exists_neutral_producer`, `hasParityNeutralRate_vk`, `exists_hasParityNeutralRate_rpow_iff` |
| 4 | Why do primes recur at a zero, if they do? | Phase returns always exist, and a shift aligned to length `N` exists below `(7N)^N`, so the primes recur along them freely. On any bounded return at a zero they must, and the limit is the identity of the gauge torus. What fails is the size of `ζ`. Each zero has an exponent `A > 0` such that an aligned shift of length `N` with `|ζ(s + iτ)| ≤ N^A` on a disc reaching past the zero moves it. If finitely many zeros lie right of `σ`, then at every aligned shift past a height `ζ` exceeds `N^A` on that disc. Conversely, slow aligned returns at each zero give AAL. So the exact open input is a polynomial bound in the aligned length, across a disc that crosses `Re s = 1`, at some aligned shift. | `exists_isPhaseReturn`, `exists_isHeadReturn_le`, `tendsto_phaseDefect_zero`, `tendsto_phase_one_of_limit_zeta`, `exists_exponent_transport`, `exists_large_value_of_finite`, `asymptoticAbscissaLaw_of_slowReturns`, `not_translatesBoundedOn_of_finite`, `IsPhaseReturn.infinite_zeros`, `asymptoticAbscissaLaw_of_boundedReturns` |
| 5 | Is a single off-line zero a contradiction with `N(x) = ⌊x⌋`? | Not by a linear identity. The mode of a zero is annihilated in every linear ledger, whose truncation moves by at most `w/β`, uniformly in `n`. A quadratic ledger does see a simple zero, as a pole with coefficient `a D_c(ρ)`, but the order law holds for every analytic function. So seeing a zero is not excluding it: any contradiction needs arithmetic input that meromorphy does not imply. | `hasSum_ledgerMode_eq_zero`, `IsProducer.norm_ledgerMode_self_le`, `exists_ladder_at_zero`, `tendsto_ladder_of_lt` |
| 6 | Does an explicit parity-selective auxiliary beat Vinogradov–Korobov? | Explicit integer producers reach it on polynomial alphabets, with or without parity neutrality. Beating it is exactly beating it for `M`: rates `exp(−(log K)^β)`, `β < α`, hold iff `|M(n)| ≤ n exp(−(log n)^β)`, `β < α`, by elementary proofs in both directions. No certificate can avoid `M(x)`, since any rate bounds `M(x)` and `L(x)` in three lines. The only remaining form of the question is a direct proof that an explicit family has `g ≥ 0`. | `exists_moebius_producer_of_level`, `hasRate_vk`, `hasParityNeutralRate_vk`, `hasRate_exp_iff_mertens`, `IsProducer.abs_mertens_le`, `IsProducer.abs_liouvilleR_le` |
| 7 | What nonlinear functional sees a zero mode and survives the Liouville twin? | The quadratic ledger does both. It has a pole at each simple zero, and its value on `Λ` exceeds its value on `−λΛ` by at least `4 m log 2 Σ log p` over primes with `4p ≤ n < 4pB`, against `2 w ψ(√n)` for the linear ledger. The separation goes through prime squares, which are known, so it carries no new information about the primes. A functional that separates the twin through the primes themselves is not known. | `exists_ladder_at_zero`, `lseries_ladder`, `IsProducer.ledger_twin_gap`, `IsProducer.abs_ledger_twin_le` |
| 8 | What is the fake prime measure closest to the true one, for each `K`? | On residues all of them are: for fixed `k` and class `ι ≢ 0`, every fake prime measure of high level gives the class its pronic mass. Pointwise nothing is determined, since translating an atom by a period keeps every moment. So the freedom is where along a class the mass sits. At each window `B` at most the period there is an extremal measure, of largest window mass; that mass over `1 − 1/B` is the exact best normalized slope. At the best window it lies between `1 + c₁/(√K (1 + log K))` and `1 + exp(−(log K)^α)` times the pronic mass. On a fixed finite set the extremal mass tends at most to the pronic mass, so every finite shape is reached at its pronic cost: every window, and a spike at every integer. Its exact form at finite `K` is open. | `exists_level_classMass_close`, `exists_level_targetMass_le`, `exists_shape_producer`, `exists_spike_producer`, `exists_producer_at_window`, `exists_extremal_fake_measure`, `exists_extremal_bracket`, `IsFakePrimeMeasure.hasSum_slack`, `isFakePrimeMeasure_translate`, `forall_isFakePrimeMeasure_iff` |

## 6. The scale of the rate

| Input | Output | Lean |
|---|---|---|
| `|M(n)| ≤ C n^{1−σ}`, `0 < σ ≤ ½` | every rate `K^{-a}`, `a < 2σ/(3 + 2σ)` | `hasRate_of_power_quarter` |
| zero-free strip `Re s > Θ`, `½ ≤ Θ < 1` | every rate `K^{-a}`, `a < 2(1 − Θ)/(5 − 2Θ)` | `hasRate_of_zeroFree_quarter` |
| RH | every rate `K^{-a}`, `a < 1/4` | `hasRate_of_riemannHypothesis_quarter` |
| rate `K^{-a}` | `Re ρ ≤ 1 − a` | `re_le_of_hasRate_rpow_half` |
| rates `K^{-a}` for all `a < 1/2` | RH | `riemannHypothesis_of_hasRate_half` |
| any `a > 1/2` | impossible | `not_hasRate_rpow_of_half_lt` |
| every producer on `[1, K]` | `ε ≥ c₁/(√K (1 + log K))` | `exists_half_floor` |
| certificate at height `τ` | `√K (1 + log K) ≳ |τ|` | `exists_necessary_alphabet_half` |
| rate `exp(−(log K)^α)` | `Re ρ ≤ 1 − c (log ‖ρ‖)^{1−1/α}` | `exists_re_le_of_hasRate_exp` |
| VK bounds for `M` and `m` | rate `exp(−(log K)^α)`, `α < 3/5` | `hasRate_vk` |
| any producer of rate `ε` on `[1, K]` | `|M(n)| ≤ ε n + 12 (w/m) √n + K` | `IsProducer.abs_mertens_le` |
| any producer of rate `ε` on `[1, K]` | `|M(n)| ≤ 3 ε n` for `n ≥ (D (1 + log K)³ K)²` | `exists_abs_mertens_le_three_rate` |
| a family of rate `f`, `0 < θ < ½` | `|M(n)| ≤ 3 f(⌊n^θ⌋) n` eventually | `HasRate.eventually_abs_mertens_le` |
| rate `K^{-a}` | `M(n) ≪ n^{1−σ}` for `σ < a/2` | `HasRate.exists_abs_mertens_le_rpow` |
| rates `exp(−(log K)^β)`, `β < α` | same for `M(n)/n`, and conversely | `hasRate_exp_iff_mertens` |
| a polynomial rate | a power saving for `M`, and conversely | `exists_hasRate_rpow_iff_mertens` |

So under RH the exponent of the rate lies in `[1/4, 1/2]`. The two directions match on the exponent `α = 3/5` at the VK scale, and up to a constant in the exponent at the polynomial scale.

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
| Harmonic entanglement | `abs_mobiusPart_sub_le`, `mobiusPart_add_harmonicEntangled_ge`, `exists_harmonic_producer` |
| **Smooth compensation of the large primes and the one-quarter rate** | `exists_isCompensation`, `sum_compCoeff_floor`, `sum_floor_sub_le`, `abs_compSum_le`, `abs_compNear_sub_le`, `compCoeff_eq_zero`, `abs_compNear_sub_le_defects`, `compWeighted_le`, `exists_compensated_producer`, `exists_compensated_producer_of_level`, `hasRate_of_power_quarter`, `hasRate_of_riemannHypothesis_quarter` |
| **A Mertens level gives a rate; polynomial rate ⇔ zero-free strip** | `eventually_producer_of_level`, `exists_hasRate_rpow_iff` |
| **A rate bounds the Mertens and Liouville functions, with constant one** | `IsProducer.sum_producerSlack_le`, `IsProducer.abs_sum_le_of_ledger`, `IsProducer.ledger_moebius`, `IsProducer.abs_mertens_le`, `IsProducer.abs_liouvilleR_le`, `exists_abs_mertens_le_three_rate` |
| **The scales of the rate and of `M` coincide, without zeros** | `abs_mobiusHarmonic_le_of_mertens`, `isMertensLevel_of_mertens_exp`, `hasRate_exp_iff_mertens`, `exists_hasRate_rpow_iff_mertens` |
| **Explicit integer producers at the VK rate** | `isMertensLevel_vk`, `hasRate_vk` |
| **Exact LP duality; the extremal fake prime measure and its distance from the truth** | `IsFakePrimeMeasure.le_normSlope`, `exists_producer_of_feasible`, `exists_extremal_fake_measure`, `exists_extremal_bracket` |
| **Parity: the factor of two, and parity neutral producers at the Mertens level** | `IsProducer.parity_neutral_of_odd`, `exists_liouville_pattern`, `exists_neutral_producer`, `exists_neutral_producer_of_level`, `hasParityNeutralRate_vk`, `exists_hasParityNeutralRate_rpow_iff` |
| **Profinite rigidity of fake prime measures; every shape is reached** | `IsFakePrimeMeasure.sum_fold_moment`, `IsFakePrimeMeasure.sum_fold_tail_le`, `tendsto_foldMeasure_pronic`, `exists_level_classMass_close`, `exists_level_targetMass_le`, `exists_extremal_of_target`, `exists_shape_producer`, `exists_spike_producer`, `exists_producer_at_window` |
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
| **The transport of a zero is effective** | `exists_isHeadReturn_le`, `norm_sub_le_of_isHeadReturn`, `exists_exponent_transport`, `exists_large_value_of_finite`, `infinite_zeros_of_slow_returns`, `asymptoticAbscissaLaw_of_slowReturns` |
| Frobenius as a factorial stencil; exact ledger | `carlitzOrder_sub`, `carlitzSize_eq_sum_order`, `card_pow_eq_sum_irrDeg` |
| **The curve stencil stops at the trivial bound; purity is an upper bound** | `coeff_balanced_stencil_mul`, `coeff_curve_tail`, `curveCount_nonneg_iff`, `curveCountR_nonneg_iff`, `abs_root_bounds`, `exists_impure_of_stencil`, `isPure_iff_upper_bound` |
| Battery: golden obeys transport and fails the count; continuous counts have no multiplicity | `goldenL_shift`, `goldenL_deepZero`, `golden_fails_count`, `continuous_multiplicity_eq_zero` |
| The prime kernel as a commutator of logarithmic dilations | `timeMultiply_commutator`, `dilationSum_primeRaise`, `iterate_primeRaise_eq_mobius` |

## 8. Tools

**Developed.**

- Stencil calculus: increments, Möbius inversion, palindrome, moments of coefficients, Hecke action.
- **Size bounds for signed stencils past sup-norm**: the smooth mean value and peak law, the coefficient mass law, the uncertainty law.
- **Explicit positivizers**: entangled letters with harmonic weights turn a signed Möbius sawtooth into an integer producer on the alphabet `T²/δ`. Compensating the large primes by smooth products lowers this to `T^{3/2}/δ`, up to logarithms.
- **The transference from stencils to bounded weights**: `IsProducer.abs_sum_le_of_ledger` bounds the partial sums of any `|a| ≤ 1` whose ledger is small.
- **Folding**: `foldMeasure` reduces a fake prime measure to one period, keeping the moments at the divisors, with tightness from jumps alone.
- **Shape producers**: `exists_shape_producer` majorizes the indicator of any finite set by an integer stencil at its pronic cost. The linear program is written for arbitrary targets (`exists_extremal_of_target`).
- **A local transport theorem**: `exists_exponent_transport`, by three circles and Rouché.
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

- A proof of `g ≥ 0` for an explicit family that uses no bound on `M(x)`.
- A smaller alphabet at a given level. The family has peak `≍ K ε`, which the peak law allows, and the uncertainty law only asks for `1/ε`. Closing that gap would raise the RH rate.
- A quantitative form of profinite rigidity: the level at which classes modulo `k` are within `η`, in terms of the rate.
- Arithmetic input for a nonlinear ledger: a bound on `Σ_d Λ^{∗j}(d) g(⌊n/d⌋)` that is not implied by meromorphy.
- Pointwise bounds below the VK length, and a metric geometry of Beurling systems near the integers (RigidArithmeticOfCuts).

**A tool that does less than it appears to.** Siegel's lemma exists here, and it does not produce auxiliaries. By rigidity a window has no free parameter below it, a stencil with no letter `1` is never a producer, integrality is free, and the condition `g ≥ 0` is an inequality on a whole period. The problem is a real linear program.

## 9. Open research topics

1. **Positivity without Möbius sums.** A rate is a bound on `M(x)`, so no stencil gives a bound on `M(x)` for free. The slope of an explicit stencil is a finite sum. All of the arithmetic is in `g ≥ 0`, and the Möbius family proves that from a bound on `M(x)`. Is there an explicit family whose nonnegativity has a direct combinatorial proof, past the known scale?
2. **The exact exponent.** Under RH the exponent of the rate lies in `[1/4, 1/2]`. A level `δ ≍ T^{-1/2}` forces letters up to `T ≍ δ^{-2}`. Compensation removes the primes above `√T` from detection, but the letters still have mass `≍ T`, and the far modulus must pay a failure at a prime power with no cancellation. So `G ≍ T/δ` and the alphabet is `T^{3/2}/δ`. To go further, a far letter must pay less than the mass the failure could move. Can the worst-case deficit be bounded by `√T`, which is the typical size?
3. **Parity through the primes.** Parity neutrality in the coefficients is free. The twin gap goes through prime squares. What functional separates a twin that agrees with `Λ` on all prime powers up to a level?
4. **Nonlinear arithmetic input.** The ladder sees zeros, and nothing bounds its modes. Which degree-two statement over `ℤ` has no analogue for a general meromorphic function?
5. **Slow aligned returns.** Is there, at a zero right of `½ + h`, an aligned shift of length `N` at which `ζ` is at most `N^A` across a disc joining the zero to `Re s ≥ 2`? Slow returns at each zero and each exponent give AAL. Alignment forces `Σ_{p ≤ N} p^{-σ}` into `log ζ`, so the primes past `N` have to cancel it. Any such sequence carries a spike at the pole.
6. **Curves.** Purity is the upper bound for the curve and its twist. Write Stepanov's auxiliary in ledger language: which degree in the points is the twist `x ↦ x^q`, and what is its analogue at the integers? Over a curve the linear theory stops at the trivial bound, so this is the actual model.
7. **The extremal measure.** On residues the limit is the pronic measure. At finite `K` the extremal measure is known only through its mass. What is its support, and how fast do its class masses converge in terms of the rate?

## 10. Traps

| Trap | Fact |
|---|---|
| The size of a stencil is its alphabet | The coefficient mass is bounded by alphabet and rate: `Σ|c(k)|/m ≤ 2K(1 + log K + (K+1)ε)` |
| The first moment limits the floor | A sharp cut gives only `K^{-3/4}`. Window sums remove the first moment, and the true end of the scale is `1/2` |
| Rates near `K^{-3/4}` are the RH level | No rate past `K^{-1/2}` exists. Rates up to `K^{-1/2}` give RH, and RH gives at least `1/4` |
| Integrality forces factorial alphabets | Entangled letters give an alphabet `≈ T²/δ`, and clearing rational weights is exact |
| Integer coefficients make this a Diophantine problem | Integrality costs nothing: every rational weight clears, and rational points approach every real feasible cost |
| Uniform far weights are natural | A failure at `P` can only cost `T/P`, and weights `∝ 1/P` drop the total from `π(T) T/G` to `(T/G) log log T` |
| Every prime up to `T` must be a letter | Primes above `√T` can be compensated by smooth products a distance `P/y` away. The cost is `1/y`, by counting alone |
| Compensation needs short-interval cancellation of `μ` | The intervals `(x/d_P, x/P]` are so short that the trivial bound suffices |
| A stencil past VK would be independent of primes | Any rate bounds `M(x)` by a three-line identity, and the known family contains `μ` by rigidity |
| The equivalence of rate and zero-free strip needs complex analysis | The rate and the Mertens scale are equivalent by elementary proofs. Only the step from `M` to zeros uses analysis |
| Fake prime measures are free | Their class masses are pinned at high level. Only the placement along a class is free |
| A window has to be large to reach a small rate | Every window `B ≥ 2` is reached by producers of rate tending to `0` |
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
| Transport needs bounded translates | A bound polynomial in the aligned length is enough, by three circles |
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
| Uses | RigidArithmeticOfCuts | uniqueness of the fake prime measure at infinite level, the Liouville floor identity |
| Uses | VerifiedHeightRungs | RH through height `67`, which keeps the transport disc off the pole |
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

- Proves `g ≥ 0` for an explicit family without a bound on `M(x)`, past the known scale.
- Proves that no such proof exists in a stated class.
- Closes the exponent gap `[1/4, 1/2]` under RH.
- Exhibits a slow aligned return at a zero, or excludes one in a stated class.
- Gives a nonlinear statement over `ℤ` that proves Hasse–Weil over `𝔽_q` in the same language and has no analogue for a general meromorphic function.

## 14. Big picture

The linear construction over `ℤ` is exact at the top of its scale. Producers exist explicitly at polynomial alphabet and integrality costs nothing. A bound on `M` gives a rate and a rate gives a bound on `M`, both by elementary proofs. A rate `K^{-a}` reads `Θ ≤ 1 − a`, and the scale ends at `a = 1/2`, exactly where the reading reaches `½`. Each window is a linear program with an extremal fake prime measure, and on residues every fake prime measure of high level is already the truth. Parity neutrality is free at every proved scale.

Rigidity explains why. Every stencil with a constant window contains `μ`, because a window of constant multiplicity is the inverse of `ζ`. So a stencil is `1/ζ` in integer form, and its rate is a bound on `M(x)`: that is a theorem, not an impression. A stencil can only help if its nonnegativity is proved another way.

The curve shows that this is not a defect of the integers. Over a curve a linear stencil reads one value of the numerator, and its window is the critical strip. The linear theory reaches the analogue of `ζ(1 + it) ≠ 0` there too. Purity is a different inequality, an upper bound on counts at square root precision, and Stepanov gets it from a twist inside the auxiliary, which is nonlinear in the points. So the question that remains is what plays the part of that twist over `ℤ`. The ladder of degrees is a first language for it: it sees a zero of order `n` at degree `n + 1`. But the order law is a fact about all analytic functions, and it needs an arithmetic bound that no source supplies.

Transport has a parallel result. Phase returns always exist, so the primes never block a return, and a bound on `ζ` along them, polynomial in the aligned length, would give AAL. Strong returns are counted by zeros, so they are as rare as the zeros they move. On the fake side transport is free and the count fails, which is why neither half can stand alone.
