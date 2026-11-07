# Prime Torus Theory (PTT)

Namespace `GaloisForLFunctions.PrimeTorusTheory`; umbrella `PrimeTorusTheory.lean`.

Throughout, `L = log T`, `ℓ = log L`, and a column is `P(t) = Σ_{p ≤ y} a_p cos(t log p)` with size `S = Σ a_p`.

## 1. Motivation

Over `𝔽_q` the phases of an Euler product are one coordinate: `q^{−s}` is periodic, there is one column, and Schur parameters, Castelnuovo and the Carlitz stencil close. Over `ℤ` the coordinates `p^{−s}` are independent. The height `t` moves one point `ω_t = (p^{−it})_p` along a dense one-parameter subgroup of the infinite torus, and the Gamma base sees only `t`.

Every one-dimensional theory (inner functions, canonical chains, lattice Schur theory, critical Hardy theory, the curve chain) has one causal order and one reflector per step, so it cannot state the walls that concern many independent primes at finite height. Torus theories (gauge torus, Wiener monoid, Bohr points, multiplicative Bochner theory) have no time coordinate, and by Bohr's isometry a fixed function sees the whole torus, so only size survives. Recurrence has a time coordinate, for returns to the identity only.

PTT takes as its object the pair `(t, ω_t)` **at finite time**: how far the orbit has travelled by time `T`, what it has not reached, what a visit costs, and what any certificate can see of this.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Phase system | `PhaseSystem`, `primeSystem`, `harmonicSystem`, `roundedSystem` | steps `ℓ_i`, weights `a_i ≥ 0` |
| Orbit | `orbit`, `poly`, `polyAt` | `ω_t(i) = e^{−itℓ_i}`; `Σ a_i e^{itℓ_i}`; its translate by a torus point |
| Column, size, defect | `column`, `size`, `defect`, `antiDefect` | `P`, `S`, `D = S − P`, `S + P` |
| Bohr and large-value sets | `bohr`, `largeValue` | `{D ≤ r²}`, `{P ≥ θS}` |
| Alignment | `AlignedAt`, `phaseDist`, `topPrimes` | distance of `t log p` to `2πℤ`; the primes above a threshold |
| Near-diagonal energy | `energy`, `shiftedEnergy`, `clockedMoment`, `diagonalMass` | `Σ A_u A_v cos(T₀(λ_u − λ_v)) sinc²(H(λ_u − λ_v)/2)` over pairs of `k`-tuples |
| Resonator | `resonator`, `boxKernel`, `targetCoeff`, `boxModulus` | `Σ_{n∣D} c(n) n^{it}`, a Fejér product |
| Words | `IsWord`, `binomMoment`, `wordLog`, `logForm` | Tarry–Escott words: linear forms in logarithms of integers with vanishing moments |
| Fibres of the hull | `orbitPoint`, `gaugeFibre`, `liouvilleFibre` | `L_ω(s) = Σ ω(n) n^{−s}` |
| Certificates | `AglerDecomposition`, `AglerDecompositionAll`, `TwoPositive`, `pickKernel`, `graph_lift`, `column_outer_factor` | kernel-valued prime conductances; slow coefficients |
| Sign patterns | `pattern`, `cosZeros` | the box of the torus the orbit is in |
| Theta amplitude | `thetaAmp`, `thetaSum` | `e^{x/2} Σ_{n≥1} e^{−πn²e^{2x}}` |

## 3. Language

- **Alignment, entry.** The orbit is near the corner `+1` on a set of primes; it enters the half-space `{P ≥ θS}`.
- **Return.** A height of small defect. **Start of the orbit.** `t = 0`, the corner `ω_0 = 1`, the pole.
- **Corners.** `+1` and `−1`; the Liouville twin is the orbit translated by `−1`.
- **Kronecker scale.** `y ≍ log T`: up to it the orbit reaches every half-space.
- **Mixing time.** `2^{π(y)}/θ(y)`: below it the orbit misses a box of the torus.
- **Diagonal range.** `k ≤ log H / log y`: products of `k` primes separate at resolution `1/H`. **Past the diagonal.** They overflow the boxes.
- **Size horizon.** `y = L²/16`, where `Σ_{n ≤ y} Λ(n) n^{−½} ≈ 2√y` meets the base `½ L`. At `y = L^{2K}` this is the scale `K = 1`. The Rankin saddle of the `y`-smooth numbers up to `T` is at `1 − 1/(2K)`, which is `½` exactly at `K = 1`. Below the horizon size fits under the base and no sign is needed.
- **Saving against size.** A lower bound for `S − sup P`. **Required saving.** What a bound at the level of the base needs: size minus base, which is `≍ εL/ℓ` at `y = (1 + ε)L²/16` at weights `p^{−½}`.
- **Top of the column.** The primes near `y`, where the size sits.
- **Race.** The base against the time the orbit needs to align.
- **Frozen coefficient.** Constant on a window longer than the Kronecker time.

## 4. Mechanisms

**The orbit is a group.**
1. `√D` is subadditive (`sqrt_defect_add_le`), the pretentious triangle inequality. So `D(nt) ≤ n²D(t)`, Bohr sets are approximate groups, `B(r) + B(s) ⊆ B(r + s)`, and returns transport values: `|P(t) − P(s)|² ≤ 2S·D(t − s)`.
2. Halász–Montgomery on the orbit (`sq_sum_column_le`): `(Σ_{t∈A} P(t))² ≤ S Σ_{t,u∈A} P(t − u)`. So `N` heights at level `θ` have differences of average level `θ²`, and a proportion `θ²/2` of the pairs has level `θ²/2`.
3. Descent (`exists_low_return_of_many_large_values`, `card_le_of_no_low_return`). Pigeonholing a large-value set into short intervals gives a large value at a low height. Rare heights are controlled by the first return.
4. Doubling (`defect_two_mul_le_antiDefect`, `three_four_one`). `ω ↦ ω²` sends both corners to `+1`: a visit near `−1` at `t` is a visit near `+1` at `2t`. This is `3 + 4cos + cos 2 ≥ 0` on the orbit.

**The resonator is a finite-time Bohr isometry.**
5. A Fejér product over a set `Y` of primes is `|R(t)|²`, with `R = Σ_{n∣D} c(n) n^{it}`, `D = Π_{p∈Y} p^m`, and unimodular coefficients. Its window integrals have an exact main term and an error bounded by the integrality `|log a − log b| ≥ 1/max(a, b)`, with no input from linear forms in logarithms. So every window of length `2(N+1)(m+1)^y 4^{my}/η` reaches level `m/(m+1)` on the primes up to `y`, with error `η` on any longer polynomial of length `N` (`exists_column_ge`, `exists_column_ge_of_primesUpTo`).

**Integers forbid alignment, with a price.**
6. Unique factorization (`le_of_aligned`). Past the diagonal range two distinct products of `k` primes of a set `G` fall into one box of width `π/t`. Alignment to within `ε` puts `t log(a/b)` within `2kε` of `0`, while `|log(a/b)| ≥ y^{−k}`, so `t ≤ 2kεy^k`. Only the cardinality of `G` enters, so the saving survives deleting primes (`saving_on_any_set_of_primes`, `saving_at_the_top_of_the_column`). The price is a power of `T`.
7. Tarry–Escott words (`exists_not_aligned`, `exists_not_aligned_of_large`). A word `c` with vanishing moments makes `Σ c_a log(x + a)` tiny and slowly varying, so at a suitable `x` the phase `t Σ c_a log(x+a)/2π` is at distance `≥ ¼` from the integers. Alignment of every integer in `[x, x + M]` would put it near an integer. This uses that every integer in a short interval is a product of the generators, so it needs all small primes.
8. Squared words and the logarithmic Hankel form (`logForm`, `exists_band`, `le_sum_primes_phaseDist`, `le_sum_primes_critical`). The phase of `Σ c_a c_b log(x + a + b)` is positive, decreasing and log-convex in `x`, with no cancellation to control. The crossing of `½` is therefore slow, a band of real arguments. Since the word has mass zero the phase is unchanged under `x + h(a+b)`, so the band gives a positive density of misaligned integers. Their mean distance over `n ≤ N` is carried by the primes at weight `1/p`.
9. Height against length (`exp_neg_le_sum_primes_critical`). Words of height `H` trade `ℓ¹` mass for length: order `L` at length `L^A` costs `H^{O(1)}` with `log H ≍ L^{2−A} ℓ`. A word has mass zero, so it cannot see a common rotation of the phases: the same argument bounds `|Σ_{n<N} n^{it}|` (`norm_sum_le_of_large`).

**The energy is the moment.**
10. `clockedMoment_eq`: the Fejér-clocked moment of the orbit is exactly the near-diagonal sum, oscillating at height `T₀`. Through the diagonal range the energy is diagonal (`energy_le`). Every large value contributes (`card_mul_le_clockedMoment`), and the start of the orbit contributes `S^{2k}/(8kΛH)` (`energy_ge_start`): the mixing term forced by Cauchy–Schwarz is the pole.

**Rank.**
11. At rank one (`IsRankOne`) the orbit is periodic whatever the size, exact returns have positive density, and products collide (`tupleStep_eq_of_coeff_sum_eq`). At finite rank `r` the return time is `Q^r` whatever the size (`exists_return_of_rank`). A continuous system has no torus (`tendsto_continuousColumn`).

**The two-point test.**
12. Test a decomposition on `(1, −1)` at `s` and at `s + iτ`, with `τ` a return. Prime coordinates barely move and contribute a nonnegative amount; the Gamma coordinate is tiny at `s + iτ`. What remains is `|S(s)| ≤ |G(s)|` (`two_point_inequality`, `norm_le_of_returns`). With all primes the return errors are dominated by `Σ_p p^{−2σ}`, which converges on `Re s > ½` (`two_point_inequality_all`).
13. At rank one the same test is Schwarz–Pick (`exists_certificate_iff`): the determinant of the quotient kernel is the pseudo-hyperbolic comparison.

## 5. The questions, and their answers

| Question | Answer | Lean |
|---|---|---|
| How long does the orbit need to enter a half-space at `y = L^{2K}`, `K > ½`? Any saving against size? | Every window of length `exp(c_m y₀)` enters level `(m/(m+1)) S(y₀)`: the Kronecker scale, at any length. It never reaches size past that scale. On all primes the saving exceeds `T^{−δ}` for every `δ` at every `K > ½`, is at least `exp(−L^β)`, `β > 2 − 2K`, up to `K = 1`, and at least a constant times `L^{−8}ℓ^{−4}` at `y ≥ 48 L²ℓ`. With every prime up to `L^{A'}` deleted, `1 < A' < 2K`, it is still `T^{−2(2K−A'+1)/(A'−1)−δ}`. Separated visits at level `θ` in a window `H ≥ 4y^k` number at most `16kΛH k!(Σa²)^k/(θ(θS)^{2k})`, which is `H^{1/(2K)+o(1)}` at `H ≍ T`. | `question_one`, `card_largeValue_le` |
| Near-diagonal energy past `k = L/log y`? | It is the clocked moment. Through the diagonal range it is the diagonal. Past it, it contains the diagonal and the start of the orbit, each large value adds a term of the same shape, and interpolation bounds it by size. The positive count never sees a saving: non-alignment lives in the cancellation of the oscillating sum. Diagonal data cannot exclude a return. | `question_two`, `clockedMoment_succ_le`, `diagonal_data_cannot_exclude_return`, `not_mem_largeValue_of_shiftedEnergy_lt` |
| Why is the Gamma coupling at the critical growth `κ = ½`? | The theta amplitude counts integers (Poisson): `f(x)e^{x/2} → ½`. The diagonal cost of the Bernstein test divides by the count of the test integers. So against integers the cost balances exactly, against primes it loses one logarithm, and below `½` it vanishes. Both `½`s are the pole of `ζ`: the centre of the functional equation is half the pole, and `Σ n^{−2σ}` diverges there. | `question_three` |
| Which functions on `X` have a sum-of-squares form with `t`-dependent coefficients? | Pointwise in `t`: all nonnegative ones, tautologically. Frozen on a window past the Kronecker time: only those paying size. Above the size curve: explicit, column by column, with an outer factor. Kernel-valued with returning prime coordinates and a Gamma coordinate: only those dominated by the Gamma coordinate, for finitely many primes and for all primes on `Re s > σ₀ ≥ ½`. So a Schur function carrying the Euler factor `ζ(2s−1)/ζ(2s)` has no such form. At one coordinate: exactly the Schur functions. | `question_four`, `no_decomposition_euler`, `exists_certificate_iff`, `rank_one_law` |
| Over which torus points does the hull extend into the strip, and which carry zeros? | Finite modifications of orbit points: meromorphically, with exactly the translated zeros of `ζ`. The Liouville point: `ζ(2s)/ζ(s)`, holomorphic on `Re s > ½` iff RH. Haar-almost every point: holomorphic on `Re s > ½`, zero-free. RH is the zero-freeness of every nonzero limit of vertical translates. | `question_five` |
| Does a large-value set have additive structure, forcing returns the pole must pay for? | Yes. Differences have level `θ²` on average, and at the corner the set is an approximate group. At weights `1/p` the pole prices each level: `θ S ≤ log(8 log u + 39) + C`, so a height at level `θ` lies above `exp(c(log z)^θ)`, and the number of large values in a window is bounded through the first level the pole permits. At weights `p^{−½}` the pole pays nothing. | `question_six`, `pair_level_le`, `card_le_of_pole` |

## 6. Pillar theorems

All are unconditional. The hull theorems are equivalences with RH and are stated as such.

| Theorem | Lean |
|---|---|
| Group closure, transport, corners | `sqrt_defect_add_le`, `column_sub_sq_le`, `defect_two_mul_le_antiDefect` |
| Large-value structure and descent | `sq_sum_column_le`, `card_pairs_ge`, `exists_low_return_of_many_large_values` |
| Finite-time Bohr isometry | `exists_column_ge`, `exists_column_ge_of_primesUpTo` |
| Pigeonhole non-alignment; power saving on any set of primes and at the top of the column | `le_of_aligned`, `saving_against_size`, `saving_on_any_set_of_primes`, `saving_at_the_top_of_the_column` |
| Non-alignment at every large height, away from every torsion point | `exists_not_aligned_of_large`, `exists_prime_not_near_torsion`, `exists_not_aligned_of_large_of_word` |
| Saving at every length past the Kronecker scale; polylogarithmic past the size horizon | `rpow_neg_le_sum_primes_critical`, `exp_neg_le_sum_primes_critical`, `le_sum_primes_critical`, `le_sum_primes_liouville` |
| The sum of `n^{it}` over `n < N` is shorter than `N` at every length past the Kronecker scale | `norm_sum_le_of_large`, `norm_sum_le_of_length` |
| Moment = energy; start of the orbit; diagonal range; last-moment bound | `clockedMoment_eq`, `energy_ge_start`, `energy_le`, `card_largeValue_le` |
| Rounded orbit: diagonal data cannot exclude a return | `diagonal_data_cannot_exclude_return`, `exists_collision` |
| Discrepancy: low-degree uniform, sparse on boxes | `norm_integral_nPhase_sub_le`, `exists_pattern_not_attained` |
| Agler wall; first and second test; sharpness | `two_point_inequality`, `agler_wall`, `two_primes_first_test`, `agler_wall_all_primes`, `euler_test`, `selfDecomposition` |
| Rank one: Pick criterion, Schur certificate | `exists_certificate_iff`, `twoPositive_pickKernel_comp`, `rank_one_law` |
| Corners and parity | `clockedColumn_eq`, `clockedColumn_neg_one`, `clockedMomentAt_le_energy` |
| Hull | `riemannHypothesis_iff_liouvilleFibre_extends`, `ae_fibre_extends_zeroFree`, `fibre_zero_iff`, `riemannHypothesis_iff_limits_zeroFree` |
| Pole price | `column_le_pole`, `not_mem_largeValue_of_lt`, `card_le_of_pole`, `eventually_not_mem_largeValue` |
| Critical coupling | `tendsto_thetaAmp_left`, `tendsto_thetaAmp_integers`, `tendsto_thetaAmp_div_primeCounting` |

## 7. Tools

**Developed.**
- Metric and additive calculus of the orbit, for any phase system.
- Resonators with unimodular coefficients: main term plus integrality error, for arbitrary finite integer sets.
- Pigeonhole with unique factorization, for arbitrary sets of primes.
- Words with vanishing moments, of height one and of larger height; the logarithmic Hankel form; misalignment bands; the transfer from integers to primes at weight `1/p`.
- Near-diagonal energy against a Fejér clock, at every height; `k`-fold fibres of the product, with the bound `k!`.
- Rounded orbits as a calibration for what diagonal data sees.
- Two-point test of kernel decompositions, for one coordinate, for finitely many and for all primes.
- Outer factors of columns; allocation of the base.
- Fibres over finite-type and typical torus points, with the identity theorem and Hurwitz on domains.
- Sign-pattern count of the orbit.

**To build.**
- A transfer of the polylogarithmic saving to the top of the column.
- A bound for the oscillating energy past the diagonal range better than interpolation.
- An effective Bohr isometry for boxes at scale `exp(cy)`, not only half-spaces.
- Height-dependent coordinates that do not return, with a nontrivial decomposition.
- A formal statement that a zero of depth `d` at height `γ` forces entry into a half-space at length `(log γ)^{1/d}`.

## 8. Test systems

| System | Behaviour | Lean |
|---|---|---|
| Curves, Golden, commensurable steps | rank one: periodic orbit, exact returns of positive density at any size, weights irrelevant; products collide, so every integer argument is void; certificates are the Schur property | `defect_period`, `exists_exact_return`, `shiftedEnergy_period`, `tupleStep_eq_of_coeff_sum_eq`, `rank_one_law` |
| Finite rank | return time `Q^r`, independent of the number of steps | `exists_return_of_rank` |
| Integers | infinite rank, with integrality | `not_isRankOne_log`, `le_of_aligned` |
| Rounded primes | same weights, same orbit to time `cT`, same diagonal moments, exact return at `T`; loses unique factorization past the mixing range | `diagonal_data_cannot_exclude_return`, `exists_collision` |
| Continuous Beurling | no torus: the column dies, the orbit never returns. Non-alignment alone decides nothing | `tendsto_continuousColumn`, `exists_defect_ge` |
| Integer-norm systems | same steps, different weights: orbit statements are uniform in the weights, so such a system must be excluded through the amplitude | by design |
| Liouville twin | same absolute moments and energies, opposite sign at the start of the orbit | `norm_twist_neg_one`, `clockedColumn_neg_one` |

## 9. Open research topics

1. **The required saving.** At `y = (1+ε)L²/16` a one-sided bound at the level of the base needs a saving `≍ εL/ℓ` on the top of the column. At weights `p^{−½}` the proved saving is of order `L^{−8}ℓ^{−4}` at `y ≥ 48L²ℓ`, on all primes. A macroscopic theorem, `sup_{[T,2T]} P ≤ (1 − c)S` for some `K > 1`, is quasi-RH strength up to crystal shielding. What is the largest saving at length `L^{2K}`?
2. **The location of the saving.** The polylogarithmic saving may sit on small primes; on the top of the column the proved saving is a power of `T`. Does the top carry a saving larger than every power of `T`? How many primes up to `y` are misaligned at precision `L^{−C}`?
3. **The exponent on a set of primes.** Is the exponent `2(A − A' + 1)/(A' − 1)` the truth on sets of `L^{A'}` primes, or an artifact of counting? Counting smooth numbers alone cannot beat precision `T^{−1/(A−1)}`: a comb of density `y^{−k}/T` is consistent with every count. Below `A' = 1` the count `C(|G|, k) > T` fails and only Baker remains.
4. **The oscillating energy past the diagonal range.** The expected shape is diagonal + start + nothing else; its proof is non-alignment. Which part of `k₀ < k < k₀·2K/(2K−1)` is reachable? This is `y`-smooth numbers in intervals of length `N/T`.
5. **Mixing time.** `2^{π(y)}/θ(y)` from below on boxes; `exp(c_m y)` from above on half-spaces. What is the exact exponent for boxes?
6. **Certificates.** A decomposition with coordinates that see absolute height. `two_point_inequality` says exactly what they must achieve: they must differ from their values along returns by the size of what they pay. A system of returning coordinates only certifies through an archimedean coordinate that already carries `S` (`selfDecomposition`, `agler_wall_all_primes`).
7. **The hull.** Torsion points beyond Liouville (characters, finite-order twists); natural boundary over typical points; the exact zero-carrying set when RH fails.
8. **Arithmetic Bernstein between growth `½` and `1`.** The Euler collapse kills perturbations at `α ≤ 1`, the mechanism stops at `½`.
9. **Zero to entry.** A Turán-type statement of how an off-line zero forces a visit, and at which length.

## 10. Traps

| Trap | Truth |
|---|---|
| Diagonal moments exclude a return | A rounded orbit has identical diagonal moments and an exact return at `T` |
| Near-diagonal counts prove a saving | The start of the orbit alone gives `E_k ≥ S^{2k}/(8kΛH)`, whose `2k`-th root tends to `S`: the positive energy sees size |
| The mixing term is statistical | It is `t = 0`, the pole |
| Effective Kronecker needs Baker | Half-spaces need only the integer gap, with exponent linear in `y` |
| Bohr's isometry holds at finite time | Up to `y ≍ log T` for half-spaces; past that the orbit misses boxes |
| Kernel-valued conductances evade frustration | With returning coordinates they pay nothing beyond the archimedean coordinate (`agler_wall_all_primes`) |
| Agler's bidisc theorem contradicts the wall | A function of `(2^{−s}, 3^{−s})` is almost periodic and does not decay; the wall concerns functions that see `t` |
| `t`-dependent coefficients are a new tool | Pointwise they are tautological (`graph_lift`); slow ones cost size (`frozen_certificate_costs_size`) |
| Any saving against size moves the sign | The sign needs the saving to reach size minus base, `≍ εL/ℓ` just past the horizon; the proved saving is of order `L^{−8}ℓ^{−4}` |
| A saving on all primes is a saving at the top | Words use every small prime, so the saving may sit there; the size sits at the top, where the proved saving is a power of `T` |
| Below the size horizon a saving is needed | Size fits under the base there; there is nothing to save |
| Absolute moments separate the twin | `|P_{−1}| = |P|`: only a signed functional at the start can |
| Non-alignment decides the critical line | Continuous Beurling systems have no returns, so it decides nothing there |
| Zeros over a Haar-null set means no zeros | The orbit itself is Haar-null |
| A rank-one proof transfers | Products collide at rank one, so the integrality argument and the Kronecker time both change |
| The Euler product pays at `p^{−½}` | The pole pays at `1/p` only: `column_le_pole` |

## 11. Criteria

**A contribution to the field must:**
- carry a time coordinate, or state why a statement without one belongs here (for example a blindness of all finite-time data);
- behave differently at rank one, or reduce there to the Schur, Castelnuovo or periodic statement;
- not be invariant under torus translation, unless it is an explicit statement of that blindness;
- be uniform in the weights if it is an orbit statement, and name the input on the amplitude if it is not;
- be false on impure columns, Golden and heated kernels if it claims a sign;
- state its scale against the Kronecker scale, the diagonal range, the size horizon and the mixing time, and say where on the column it lives.

**The field has succeeded when** there is an all-height one-sided bound for prime polynomials of length `L^{2K}`, `K > 1`, beyond size by a factor tending to infinity; or a proof that no such bound follows from the orbit and integrality alone, with a named replacement input. The first milestone is a saving on the top of the column larger than every power of `T`.

## 12. Limits

- For a Dirichlet series the supremum over the orbit equals the supremum over the torus, so every gain comes from finite time or from the Gamma coupling.
- Non-alignment speaks about large heights. A single off-line zero at a fixed height is invisible to it.
- A macroscopic theorem on the critical line is quasi-RH strength. Below that, tests are curves and models.
- Baker is too weak: its constant grows at least exponentially in the number of primes.

## 13. Context

| Direction | Programmes |
|---|---|
| Uses | HTGeometry (log separation, window means, simultaneous Dirichlet, Hurwitz, Schwarz–Pick), RHTower (Abel summation, Liouville series, zero-free right half-plane, near-one bound, prime harmonic lower bound, zeta bounds on `Re s > 1`), ArithmeticCorrelationGeometry (gauge torus, almost-sure square root), SignedSuccessorArithmetic (prime cosine sum against `ζ`), ArithmeticInnerFunctionTheory (column shape) |

| Neighbour | Interface |
|---|---|
| ArithmeticInnerFunctionTheory | One-dimensional causal theory: torus sums, arithmetic Bernstein, locked = torus (`torusSum_nonneg_iff_locked`, `exists_height_aligned`). PTT says why the growth is `½`, and what locking means at finite time |
| ArithmeticAuxiliaryDynamics | First-return bound, Hurwitz limits in the gauge torus, the spike at the pole (`exists_gauge_point`, `not_bounded_near_pole`). PTT works at all levels and on all fibres |
| ArithmeticGaugeTheory, ArithmeticCorrelationGeometry | Gauge torus, Liouville antipode, almost-sure square root; no time coordinate. PTT supplies time and the fibres |
| SquareRootThreshold | Kronecker realization, exponential height escape, cut crystals (`exists_height_prime_phase_approx`). PTT replaces qualitative Kronecker by the resonator |
| RHTower sinc energy and Vinogradov modules | The sinc spectrum `evenMoment_window_kernel`; Vinogradov–Korobov, a proportional saving above length `exp(L^{2/3})`. PTT adds the positive clock, reads energy as returns, and has absolute savings far below that length |
| Curve and Schur theories (ArithmeticCastelnuovoSeveri, canonical chains) | The rank-one models: `rank_one_law` is the reduction |
| The whole research | The all-height one-sided bound past size is the question this field is built for; it would amplify every rung of the visibility ladder, and is effectively quasi-RH |

## 14. Big picture

The walls that remain concern many independent primes at finite height. PTT puts them in one language, and then separates what is forced from what is not.

Forced: the orbit is a group, so large values form an approximate group, doubling identifies the two corners, and rare heights descend. The integers separate, so effective Kronecker holds for half-spaces with no Baker input, and the orbit is uniform on low-degree characters up to the last diagonal scale. Unique factorization and Tarry–Escott words forbid exact alignment at every length past the Kronecker scale. So there *is* a saving against size at all large heights: on all primes it exceeds every power of `T`, and it is a power of `log T` past the size horizon; on any large set of primes, in particular at the top of the column, it is a power of `T`.

Not forced: nothing in the diagonal data, group closure or the orbit up to `cT` excludes a return at `T`, since a rounded orbit has all of these and does return. Near-diagonal counts contain the start of the orbit, so they see size and nothing less. Kernel-valued prime-by-prime certificates with returning coordinates pay only what the archimedean coordinate dominates, so the Euler factor of the scattering function cannot be paid in that form, even though a single coordinate pays every Schur function of itself. The pole prices the weights `1/p` and is silent at `p^{−½}`.

So the problem is located: the oscillating near-diagonal sum past the diagonal range, at the top of a column just past the size horizon, at a required saving of order `L/ℓ`, where `L^{−8}ℓ^{−4}` on all primes and a power of `T` at the top are proved. It cannot come from a positive count, from diagonal moments, from a frozen certificate, or from a coordinate that returns. The two mechanisms in hand are complementary. Words reach precision polynomial in `1/L`, but use every small prime. Pigeonhole lives anywhere on the column, at precision a power of `1/T`. Combining them, precision polynomial in `1/L` on a positive proportion of the top of the column, is the next theorem to aim at. It would still fall short of the required saving unless the precision becomes macroscopic, and that last step is the quasi-RH core.
