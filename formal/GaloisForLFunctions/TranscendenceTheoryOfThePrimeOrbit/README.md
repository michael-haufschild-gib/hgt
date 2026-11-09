# Transcendence Theory of the Prime Orbit (TTPO)

Namespace `GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit`; umbrella
`TranscendenceTheoryOfThePrimeOrbit.lean`; 13 modules. Specification: §2.11 of
[the review-0811 obstacles summary](../../../docs/reports/review-0811/obstacles-summary.md).

Throughout, `ω_t = (p^{−it})_p` is the point of the prime orbit at height `t`, `‖x‖` the distance of
`x` to `ℤ`, `ν ∈ ℤ^P` an integer vector, `Λ_ν = Σ ν_p log p` its linear form, `|ν|₁` its height.
A `δ`-return of `P` at `t` is `‖t log p/2π‖ ≤ δ` for all `p ∈ P`.

## 1. Motivation

The sign-free part of the curve proof over `ℤ` is in the corpus (elimination at the exceptional rank,
free self-improvement at the integer degrees, finite-rank Euler–FE purity). What it lacks is a
producer for the crude step, and the crude step fails exactly at early heavy returns of the prime
orbit (proportional saving ⇔ no early heavy return). The sign-free producers in the corpus are
capped: integrality at Chebyshev, Rouché copies at the trivial separation bound, exponential sums at
Vinogradov–Korobov.

A return is a simultaneous approximation, so lower bounds for return times are Diophantine
statements about the numbers `log p`. Transcendence theory is the sign-free discipline for such
statements: linear forms in logarithms, auxiliary functions with integer coefficients,
extrapolation, zero estimates; integrality turns smallness into exact vanishing. TTPO is the theory
of the prime orbit as a Diophantine object. Its main conjecture (B97, `MainConjecture`) is the
quantitative Kronecker theorem: at fixed precision `δ`, no heavy subset of the primes `≤ y` returns
before `exp(y^c)`.

A return has two parameters, and they belong to different mathematics:

- its **depth** `δ`, at a fixed set of primes, is controlled by linear forms in logarithms;
- its **breadth** `|P|`, at a fixed depth, is controlled by counting.

B97 is a breadth statement at constant depth. TTPO proves the depth law, the breadth cap of every
linear-form argument, the precise survival orders of integrality, and a reciprocity that turns a
return into a statement about the zeros, which then bounds heavy returns by zero-free regions.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Return | `IsDeltaReturn s ℓ δ t` | `‖tℓ_i/2π‖ ≤ δ` for `i ∈ s` (TAPO's `IsReturn` in the cosine normalization: `isDeltaReturn_of_isReturn`) |
| Linear form, height | `linForm`, `formHeight`; `RHTower.Matveev.primeLogForm`, `coeffHeight` | `Σ ν_i ℓ_i`, `Σ|ν_i|` |
| Rounded system | `roundedStep T ℓ` | `2π·round(Tℓ_i/2π)/T`: rank one, exact return at `T` |
| Matching to height `K` | `MatchesToHeight s K ℓ ℓ'` | every form of height `≤ K` changed by at most half its size |
| Explicit Baker exponent | `bakerExponent m W`, `baseU`, `explicitR` | `(10⁴(W+1)(m+2)²)^{30(m+2)²}` for `m+1` logarithms |
| Integer auxiliary, jets | `auxJet N c j t`, `jetMass`, `firstMoment`, `IsSmoothOver` | `Σ c_n(−log n)^j n^{−it}`, `Σ|c_n|(log n)^jΩ(n)`, `Σ c_n v_{p_i}(n)` |
| Rank-one system | `IsRankOne s ℓ L` | every step an integer multiple of `L` (`𝔽_q[T]`: `L = log q`) |
| Heavy subset, main conjecture | `IsHeavy y κ H`, `QuantitativeKronecker`, `MainConjecture` | missing at most `κ` of `Σ_{p≤y} p^{−½}`; B97 |
| Orbit polynomial | `orbitPoly φ t` | `Σ Λ(n) n^{−½−it} φ(log n)` |
| Reciprocity terms | `poleTerm`, `gammaTerm`, `zeroSide`, `modTest`, `decayMass` | `φ̂(±i/2 − t)`, `∫φ̂(τ−t)μ(τ)dτ`, `Σ_ρ m_ρ φ̂(γ_ρ − t)` |
| Heavy-return test | `windowBump`, `heavyTest y`, `heavyWeight` | smooth bump `1` on `[−log 8, −1/10]`, translated to `log y` |
| Zero-side quantities | `localDensity`, `badMass`, `IsBadHeight` | `Σ m_ρ/(1+(t−γ)²)`; the zeros below `T₀` or above `2t` |
| Turán loss | `turanLoss M n` | `2en(6(n+1)(M+2n+2))^n` |

## 3. Language

- **Depth** of a return: its precision. **Breadth**: the number of primes returning together.
- **Diophantine data of height `K`**: the values of the forms `Λ_ν`, `|ν|₁ ≤ K`, up to bounded
  relative error.
- **Survival**: an approximate vanishing at a return forced by integrality to be exact.
- **Reciprocity**: the explicit formula read at height `t`, exchanging the orbit at `t` with the zeros
  near `t`.
- **Pole imitation**: the zeros near `t` reproducing the orbit polynomial at `t = 0`, which carries
  the pole of `ζ`.
- **Depth profile**: an upper bound `d(|γ|)` for `|Re ρ − ½|` above a height, nondecreasing in `|γ|`.
- **Label statement**: a statement about the numbers `log p` only, shared by every Euler product
  over the rational primes.

## 4. Mechanisms

1. **Return–form duality.** At a `δ`-return, `‖tΛ_ν/2π‖ ≤ |ν|₁δ`; a nonzero form excludes returns on
   `2π|ν|₁δ < |t||Λ_ν| < 2π(1 − |ν|₁δ)`. A return of two primes makes the binary form
   `n_p log q − n_q log p`, `n = round(t log/2π)`, of size `≤ δ log pq` with coefficients `≍ t`.
2. **Liouville at bounded height.** `|Λ_ν| ≥ y^{−|ν|₁}` for primes `≤ y`: `Λ_ν = log(a/b)`, `ab ≤ y^{|ν|₁}`.
3. **Explicit Fel'dman.** The number of extrapolation steps `R = L + 2D(⌊log₂(L+D+1)⌋+1)` satisfies
   `4(1000W)^{(m+1)(m+2)}(R+1)^D ≤ 2^R` with no limit argument; every Fel'dman parameter is then a
   power of `U = 10⁴(W+1)(m+2)²`.
4. **Pigeonhole.** `(H+1)^k` vectors in `{0..H}^k` put two forms within `HW/((H+1)^k − 1)`.
5. **Rounding.** `|roundedStep − ℓ| ≤ π/T`, so forms of height `K` move by `≤ Kπ/T`.
6. **Approximate group.** `t` a `δ`-return ⇒ `mt` an `mδ`-return; jets at `0` are copied to `mt`.
7. **Integrality and transcendence at `s = 0`.** `A(0) = Σ c_n ∈ ℤ`; `A′(0) = −Λ_μ`; `A″(0)` at two
   primes is `log²p·(a + bβ + cβ²)` with `β = log q/log p` transcendental (Gelfond–Schneider).
8. **Six exponentials.** `p^{−it}, q^{−it}, r^{−it}` are not all algebraic for `t ≠ 0`.
9. **Reciprocity.** The explicit formula for `u ↦ φ(u)e^{−itu}`, `φ ∈ C²_c(0, ∞)`, is
   `P_φ(t) = π_φ(t) + Γ_φ(t) − Z_φ(t)`; `‖φ̂(γ_ρ − t)‖ ≤ e^{a|Re ρ−½|}C_φ/(1 + |γ − t|)²` for `φ`
   supported in `[−a, a]`; `π_φ(t) = O(t^{−2})`, `Γ_φ(t) = O(log t)` uniformly in `φ` up to `C_φ`.
10. **The pole at `0`.** For the heavy-return test `P_{φ_y}(0) ≥ √y/4` (Chebyshev); at a heavy return
    `Re P_{φ_y}(t) ≥ (1 − 2π²δ²)P_{φ_y}(0) − 6κ√y − 12 log y`.
11. **Fading of far zeros.** Zeros below a fixed height or above `2t` are dominated by
    `Σ m_ρ/(1 + |γ_ρ|²) < ∞` and fade as `t → ∞` (Tannery); the others are counted by the local density
    `≪ log t`.
12. **Rank one.** For steps `d_i L` every multiple of `2π/L` is an exact return and every frozen jet is
    `2π/L`-periodic: the return is the Frobenius.

## 5. Questions and answers

| # | Question (§2.11) | Answer | Lean |
|---|---|---|---|
| Q1 | How early can the primes `≤ y` return to `δ`-precision, and how early can a heavy subset? | **Depth:** every set of `≥ 2` primes `≤ y` (every heavy subset) returns to precision `δ ≤ 1/10` no earlier than `e^{−2}(2δ log y)^{−1/C(y)}/(2 log y)`, `C(y)` an explicit power of `log y`; Dirichlet returns it by `⌈π/2δ⌉^{|P|}`. **Breadth cap:** for `T ≥ 2πKy^K` the rounded system matches every form of height `≤ K` and returns exactly at `T`, so no Diophantine data of height `K` excludes a return there. **Heavy subsets at constant precision:** at every return of a `1/1000`-heavy subset at precision `≤ 1/20` and height `t ≥ T₁`, unconditionally `√y ≤ K(y^{½ − w(2t)} log t + log(2+t))`, `w` the Vinogradov–Korobov width, so no such return occurs at `T₁ ≤ t ≤ exp((log y)^{3/2−ε})`, for every `ε > 0`; under a zero-free strip of width `h` above some height, `log t ≥ c y^{½−h}` (RH: `log t ≫ √y`). | `question_one`; `le_of_isDeltaReturn_of_two_mem`, `exists_isDeltaReturn_le_pow`, `exists_matching_system_with_exact_return`, `heavy_return_bound_vinogradovKorobov`, `eventually_no_heavy_return_before_vk`, `log_ge_of_heavy_return_of_strip` |
| Q2 | How does the lower bound for linear forms in `k` logarithms depend on `k`; uniform for `k ≍ π(y)`? | `|Λ_ν| ≥ exp(−(10⁴(W+1)(k+1)²)^{30(k+1)²}(log|ν|₁ + 2))`: the exponent is `exp(O(k² log kW))`. Every exponent is `≥ k − 1`. At `k ≍ π(y)` the explicit exponent is `exp(O(y²/log y))`, and uniformity is beside the point for constant-precision returns: only forms of height `< 1/2δ` act, Liouville `y^{−|ν|₁}` holds for them, and the breadth cap defeats them past `2πKy^K`. | `question_two`; `abs_primeLogForm_ge_explicit`, `abs_primeLogForm_ge_of_le`, `le_exponent_of_bakerBound`, `exists_small_primeLogForm`, `inv_pow_le_abs_linForm_log` |
| Q3 | Which integer auxiliaries on smooth numbers survive the passage from approximate to exact vanishing? | Jets at a `δ`-return equal the jets at `0` up to `2πδM_j`, and at `mt` up to `2πmδM_j`. **Order 0** survives at constant precision: `|A(it)| + 2πδM₀ < 1` forces `Σ c_n = 0`. **Order 1** survives below the explicit Baker threshold: `|A′(it)| + 2πδM₁ < exp(−C(log|μ|₁+2))` forces all first moments `μ_i = Σ c_n v_{p_i}(n)` to vanish; Dirichlet shows no threshold above `W/H^{k−1}` works. **Order 2** at two primes: an integer quadratic form in `log p, log q` vanishes only trivially, so exact second-order vanishing is three integer identities; an approximate threshold needs a transcendence measure of `log q/log p`, and at three primes even exact vanishing is algebraic independence of logarithms. The orbit meets no algebraic point of three prime coordinates away from `t = 0`, so the norm is never available on the orbit. | `question_three`; `norm_auxJet_nsmul_sub_le`, `sum_coeff_eq_zero_of_small`, `firstMoment_eq_zero_of_small`, `quadratic_log_form_eq_zero`, `not_isAlgebraic_orbit` |
| Q4 | How does Turán's power-sum method give ZAL on the finite-rank remainder of `ψ`? | It does not. Turán's second main theorem sees the finite top part on every thick set of levels with a loss polynomial in the position, so a thick crude count removes an isolated top (AAL); ZAL concerns infinitely many modes, where Wolff towers defeat every power-sum argument on levels. Return bounds cannot supply ZAL either: they are label statements, `ζ(s − h)` is an Euler product over the rational primes violating ZAL, and a route uniform over a class containing it refutes B97. Through reciprocity a zero of depth `h` weighs `y^h` on the orbit polynomial of length `y`, while a return asks for `√y`: return bounds see only zeros of depth near `½`. | `question_four`; `exists_mem_thick_ge`, `not_zerosApproachLine_shift`, `not_mainConjecture_of_uniform_route`, `norm_paperFT_gammaOf_sub_le`; `InfiniteRankWeilTheory.exists_tower_bounded_without_wellFounded` |

## 6. Tools

| # | Tool (§2.11) | Built | Module |
|---|---|---|---|
| T1 | Linear forms in many logarithms with explicit dependence on their number | explicit Fel'dman parameters and exponent `U^{30(m+2)²}`; version for primes `≤ y`; the pigeonhole lower bound `k − 1` | `LinearFormsWithExplicitDependenceOnTheirNumber` |
| T2 | Schneider–Lang extrapolation along the prime orbit | extrapolation of jets along the approximate group of returns (`mt` from `t`); exact extrapolation along the Frobenius in rank one; the orbit avoids algebraic points (six exponentials) | `SurvivalAtADeepReturn`, `TheFunctionFieldCase` |
| T3 | Turán's second main theorem on thick sets of levels | separation-free lower bound at radius `R` with a remainder, on every window of every thick set | `TuranOnThickSetsOfLevels` |
| T4 | Poisson, theta, Farey and Dedekind reciprocity as sign-free forms of the FE acting on heights | the reciprocity of returns `P_φ(t) = π_φ(t) + Γ_φ(t) − Z_φ(t)` with localization, pole decay, Gamma bound and pole imitation; it preserves the height, exchanging the orbit at `t` with the zeros near `t` | `TheReciprocityOfReturns` |

## 7. Criteria and milestones

| Item (§2.11) | Status | Lean |
|---|---|---|
| C1 no sign, spectral decomposition or positivity | every TTPO argument is an identity, a size bound, integrality or transcendence; zero-free regions and local counts enter only as inputs of `AZeroFreeRegionBoundsTheHeavyReturns` | — |
| C2 Stepanov over `𝔽_q` as the degenerate case | rank one gives exact returns at every precision and a `2π/log q`-periodic frozen jet: the Frobenius, which Stepanov's method needs; the rounded system is such a function field with `q = e^{2π/T}`, and `ℤ` has no exact return | `isDeltaReturn_zero_of_isRankOne`, `frozenJet_add_period`, `isRankOne_roundedStep`, `not_isDeltaReturn_zero_pair` |
| C3 two primes and fixed `k` | the depth law for every pair of primes `≤ y`, with explicit `y`-dependence; explicit Baker for every fixed `k` | `le_of_isDeltaReturn_pair`, `abs_primeLogForm_ge_explicit` |
| C4 a producer past the caps | transcendence produces depth only: at constant precision the depth law is a constant and the breadth cap stops every linear-form argument at the Kronecker scale. The surviving producer is reciprocity: heavy returns are bounded by zero-free regions, at VK strength unconditionally (`log R ≥ (log y)^{3/2−ε}` for heavy subsets), past VK under any zero-free strip | `exists_matching_system_with_exact_return`, `eventually_no_heavy_return_before_vk`, `log_ge_of_heavy_return_of_strip` |
| M1 two primes | the depth law for any two primes | `le_of_isDeltaReturn_pair` |
| M2 `k ≍ (log y)^A` logarithms, explicit `k`-dependence | `exp(−U^{30(k+1)²}(log|ν|₁+2))`, `U = 10⁴(⌈k log y⌉+1)(k+1)²` | `abs_primeLogForm_ge_of_le` |
| M3 `log R ≥ (log y)²` | proved for heavy subsets up to `(log y)^{3/2−ε}` (VK); exponent `2` asks, through reciprocity, that no zeros near `t ≤ exp((log y)²)` imitate the pole; the depth-profile theorem reduces it to a zero-free region `Re s ≤ 1 − c(log t)^{−θ}` with `θ < ½`, inverted as for VK | `eventually_no_heavy_return_before_vk`, `heavy_return_bound_of_depthProfile` |
| M4 `log R ≥ y^c` | holds for heavy returns beyond a fixed height under any zero-free strip `Re s ≤ ½ + h`, `c < ½ − h` | `log_ge_of_heavy_return_of_strip` |
| M5 sign-free ZAL | not reachable by power sums or label statements | `question_four` |

## 8. Pillar theorems

| Theorem | Lean |
|---|---|
| Return–form duality, windows, two-step depth form | `dist01_linForm_le`, `not_isDeltaReturn_of_window`, `abs_round_mul_sub_round_mul_le` |
| Liouville at bounded height; the breadth cap | `inv_pow_le_abs_linForm_log`, `exists_matching_system_with_exact_return`, `no_bounded_height_certificate` |
| Explicit linear forms in many logarithms; necessity | `explicitR_spec`, `feldmanLambdaExponent_add_one_le`, `abs_primeLogForm_ge_explicit`, `exists_small_primeLogForm`, `le_exponent_of_bakerBound` |
| The depth law of returns | `exp_le_of_isDeltaReturn_pair`, `le_of_isDeltaReturn_pair`, `le_of_isDeltaReturn_of_two_mem`, `exists_isDeltaReturn_le_pow` |
| Survival at a deep return | `norm_auxJet_sub_le`, `sum_coeff_eq_zero_of_small`, `auxJet_one_zero`, `firstMoment_eq_zero_of_small`, `quadratic_log_form_eq_zero`, `not_isAlgebraic_orbit` |
| The reciprocity of returns | `orbit_reciprocity`, `norm_paperFT_gammaOf_sub_le`, `norm_poleTerm_le`, `exists_norm_gammaTerm_le`, `tendsto_finiteLayer_footprint`, `norm_zeroSide_add_orbitPoly_zero_le` |
| The test of a heavy return | `eventually_orbitPoly_heavyTest_zero_ge`, `eventually_re_orbitPoly_heavyTest_ge`, `decayMass_heavyTest` |
| Zero-free regions bound heavy returns | `norm_zeroSide_le_profile`, `tendsto_badMass`, `heavy_return_bound_of_depthProfile`, `log_ge_of_heavy_return_of_strip`, `exists_vk_depthProfile`, `heavy_return_bound_vinogradovKorobov` |
| Heavy subsets do not return before the VK height | `eventually_vk_decay`, `eventually_no_heavy_return_before_vk` |
| The function-field case | `isDeltaReturn_zero_of_isRankOne`, `frozenJet_add_period`, `isRankOne_roundedStep`, `not_isDeltaReturn_zero_pair` |
| Return bounds are label statements | `riemannZeta_shift_eulerProduct`, `not_zerosApproachLine_shift`, `not_mainConjecture_of_uniform_route` |
| Turán on thick sets | `exists_window_ge`, `exists_mem_thick_ge` |
| The questions and the tools | `question_one` … `question_four`, `the_tools` |

All are unconditional.

## 9. Traps

| Trap | Truth |
|---|---|
| Baker's theorem bounds return times | it bounds the depth of a return of a fixed set; at constant precision the depth law is a constant |
| A uniform Baker bound for `k ≍ π(y)` would give B97 | at precision `δ` only forms of height `< 1/2δ` act; Liouville is sharp for them, and the rounded system satisfies them all and returns at `2πKy^K` |
| Bounded-height Diophantine data distinguish `ℤ` from a function field | below `2πKy^K` the rounded system, a function field over `𝔽_q` with `q = e^{2π/T}`, has the same data to within half |
| Integrality makes small values at returns vanish | order `0` only at constant precision; order `1` only below the Baker threshold; never on the orbit at an algebraic point |
| The explicit formula transports zeros to new heights | reciprocity at height `t` sees zeros through `φ̂(γ − t)`: a finite layer leaves a footprint `O(t^{−2})` |
| Return bounds are statements about `ζ` | they are label statements; `ζ(s − h)` shares them and violates ZAL |
| A return is a large prime sum, hence a zero | a return is the pole copied to height `t`; zeros of depth `h` weigh `y^h`, so returns see only zeros of depth near `½` |
| Turán's method proves ZAL | Turán gives lower bounds on windows of the rank of a finite part; ZAL is about infinitely many modes |
| The spike of `ζ(1 + it)` controls heavy returns | it uses the weights `1/p`, concentrated on small primes; heavy subsets live at the top of the column, where reciprocity with the test `φ_y` acts |

## 10. Open research topics

1. **Breadth beyond the zero-free region.** B97 past VK for heavy returns is the statement that no
   zeros near `t ≤ exp(y^c)` imitate the pole at length `y`; any zero-density input that limits zeros
   of depth near `½` in short height windows moves Q1.
2. **Survival at order two.** Lower bounds for `|a + bβ + cβ²|`, `β = log q/log p`; at three primes,
   algebraic independence of logarithms.
3. **Returns at bounded heights.** The heavy-return bounds hold beyond a fixed height `T₁`; the range
   `[1, T₁]` needs the oscillation of `φ̂(−i/2 − t)` at bounded `t`.
4. **A reciprocity that moves heights.** Every reciprocity built here preserves the height; transport
   to new heights is Euler–FE transport theory (B112).
5. **ZAL from power sums with an arithmetic input** excluding Wolff conspiracies of the zeros.

## 11. Context

| Programme | Interface |
|---|---|
| TailArithmeticOfThePrimeOrbit | returns in the cosine normalization, Dirichlet, first return = extreme value at `σ = 1`, VK bracket for all primes with weights `1/p` |
| PrimeTorusTheory | `dist01`, rounded orbit, savings against size |
| ArithmeticLefschetzStepanovTheory | integrality amplifier on the torsion, Stepanov's construction, exact order costs the degree |
| InfiniteRankWeilTheory | thick sets, well-founded elimination, Wolff towers, ZAL/AAL for configurations |
| RHTower (Matveev, GelfondSchneider, SixExponentials) | effective Baker (Fel'dman), Gelfond–Schneider, six exponentials |
| Zeta23, RHTower | literal explicit formula, Stirling bounds, local zero density, VK zero-free region, Hardy zeros |
| HTGeometry | Turán's second main theorem with weights |
| EulerFETransportTheory | the FE as height reflection; transport (B112) |

## 12. Success criteria and contributions

TTPO succeeds when Q1–Q4 have theorem-level answers, T1–T4 exist in their strongest unconditional
form, each criterion is met or shown unattainable for a named mechanism with its strongest positive
survivor, and the main conjecture is placed between proved bounds and the inputs that would prove it.
That state is reached: §5–§7.

A **contribution** must be unconditional; state its depth and breadth; say whether it uses lower
bounds for linear forms (and of which height), integrality (at which points and orders), counting, or
reciprocity; say whether it holds for every Euler product over the rational primes; and be false on
the rounded system if it claims a return bound past the Kronecker scale.

## 13. Big picture

A return of the prime orbit is a simultaneous approximation to `2πℤ`. Transcendence theory measures
how good one approximation can be, and that is all it measures: it gives a polynomial depth law for
every fixed set of primes, explicit in their number, and nothing at constant precision, where every
statement about forms of bounded height is shared by a function field. Integrality turns approximate
vanishing into exact vanishing only at order `0` at constant precision and at order `1` below Baker's
threshold. What crosses from depth to breadth is reciprocity: the explicit formula read at height `t`
says that a return copies the pole of `ζ` to height `t`, and the zeros near `t` must reproduce it.
Because a zero of depth `h` weighs only `y^h` against the pole's `√y`, zero-free regions bound heavy
returns: the Vinogradov–Korobov region unconditionally, so that no heavy subset returns before
`exp((log y)^{3/2−ε})`, and a strip of width `h` with `log R ≥ c y^{½−h}`.
The main conjecture is thus a zero-density statement in disguise: no configuration of zeros below
`exp(y^c)` imitates the pole at length `y`.
