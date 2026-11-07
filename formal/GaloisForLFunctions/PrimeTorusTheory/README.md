# Prime Torus Theory (PTT)

Namespace `GaloisForLFunctions.PrimeTorusTheory`; umbrella `PrimeTorusTheory.lean`.

Throughout, `L = log T`, `ℓ = log L`, `θ_p = t log p/2π`, and a column is `P(t) = Σ_{p ≤ y} a_p cos(t log p)` with size `S = Σ a_p`.

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
| Alignment | `AlignedAt`, `phaseDist`, `rotDist`, `topPrimes` | distance of `θ_p` to `ℤ`, or to a rotation `φ + ℤ` |
| Near-diagonal energy | `energy`, `shiftedEnergy`, `clockedMoment`, `diagonalMass` | `Σ A_u A_v cos(T₀(λ_u − λ_v)) sinc²(H(λ_u − λ_v)/2)` over pairs of `k`-tuples |
| Resonators | `resonator`, `boxKernel`, `boxWeight`, `binomMean` | a Fejér product `Σ_{n∣D} c(n) n^{it}`; the concentrated product `Π_p ((1 + cos x_p)/2)^{e_p}` |
| Words | `IsWord`, `binomMoment`, `wordLog`, `logForm`, `FineWord`, `wordHeight` | Tarry–Escott words; the squared phase `y(u)` |
| Models | `modelPhase`, `apTerm`, `rankCoeff` | a prime phase model extended additively; the progression `1 + Q(x + h(a + b))`; its lattice coefficient |
| Fibres of the hull | `orbitPoint`, `gaugeFibre`, `liouvilleFibre` | `L_ω(s) = Σ ω(n) n^{−s}` |
| Order-two points | `coin`, `signMeasure`, `signHom` | fair coins on the phases `0`, `½`: random completely multiplicative `±1` functions |
| Logarithm of a fibre | `eulerVar`, `primeSum`, `hullRem` | `z_p = x_p p^{−s}`; `Σ_p z_p`; `Σ_p (−log(1 − z_p) − z_p)` |
| Lacunary families | `IsLacunary`, `corrOf`, `primeSumOf`, `pairChar` | unimodular orthonormal `x_p` whose pair products `x_p conj x_q` satisfy Bessel up to `2`; the correlation `∫_E x_p conj x_q`; `Σ_{p<N} x_p p^{−s}` |
| Prime zeta | `primeZeta` | `P(w) = Σ_p p^{−w}` |
| Reduced gap | `gapOf` | `Π_p p^{|e_p − κ_p|}`, the product of the two coprime integers of a frequency |
| Ξ-current and its lift | `xiCurrent`, `xiBase`, `lamColumn`, `xiLift` | `2 Re(ξ' conj ξ)`; the archimedean base; `Σ Λ(n) n^{−σ} Re ω(n)`; `2|ξ|²(B − column)` on `X` |
| Certificates | `AglerDecomposition`, `AglerDecompositionAll`, `TwoPositive`, `pickKernel`, `heightCoord` | kernel-valued conductances; coordinates that see the height |
| Sign patterns | `pattern`, `cosZeros` | the box of the torus the orbit is in |
| Theta amplitude | `thetaAmp`, `thetaSum` | `e^{x/2} Σ_{n≥1} e^{−πn²e^{2x}}` |

## 3. Language

- **Alignment, entry.** The orbit is near the corner `+1` on a set of primes; it enters the half-space `{P ≥ θS}`.
- **Return.** A height of small defect. **Start of the orbit.** `t = 0`, the corner `ω_0 = 1`, the pole.
- **Corners, rotations.** `+1` and `−1`; the Liouville twin is the orbit translated by `−1`. A rotation is a common phase `φ` of all primes: moments cannot tell it from `+1`.
- **Rank.** The number of generators of a progression holding the phases `θ_p`.
- **Kronecker scale.** `y ≍ log T`: up to it the orbit reaches every half-space.
- **Mixing time.** The time for the orbit to reach every box of radius `ρ` on the primes up to `y`: between `exp(π(y) log(π/4ρ))/θ(y)` and `exp(10 y √(log y log log y/δ))`, with `ρ ≍ √δ`.
- **Diagonal range.** `k ≤ log H / log y`: products of `k` primes separate at resolution `1/H`. **Past the diagonal.** They overflow the boxes.
- **Size horizon.** `y = L²/16`, where `Σ_{n ≤ y} Λ(n) n^{−½} ≈ 2√y` meets the base `½ L`. At `y = L^{2K}` this is the scale `K = 1`. The Rankin saddle of the `y`-smooth numbers up to `T` is at `1 − 1/(2K)`, which is `½` exactly at `K = 1`. Below the horizon size fits under the base and no sign is needed.
- **Saving against size.** A lower bound for `S − sup P`. **Required saving.** What a bound at the level of the base needs: size minus base, which is `≍ εL/ℓ` at `y = (1 + ε)L²/16` at weights `p^{−½}`.
- **Top of the column.** The primes near `y`, where the size sits.
- **Race.** The base against the time the orbit needs to align.
- **Frozen coefficient.** Constant on a window longer than the Kronecker time.
- **Lacunary.** The prime characters `x_p` on the torus, whose pair products are orthonormal: a set of positive measure correlates with few of them.
- **Natural boundary.** A line across which a fibre has no analytic continuation at any point.

## 4. Mechanisms

**The orbit is a group.**
1. `√D` is subadditive (`sqrt_defect_add_le`), the pretentious triangle inequality. So `D(nt) ≤ n²D(t)`, Bohr sets are approximate groups, `B(r) + B(s) ⊆ B(r + s)`, and returns transport values: `|P(t) − P(s)|² ≤ 2S·D(t − s)`.
2. Halász–Montgomery on the orbit (`sq_sum_column_le`): `(Σ_{t∈A} P(t))² ≤ S Σ_{t,u∈A} P(t − u)`. So `N` heights at level `θ` have differences of average level `θ²`, and a proportion `θ²/2` of the pairs has level `θ²/2`.
3. Descent (`exists_low_return_of_many_large_values`, `card_le_of_no_low_return`). Pigeonholing a large-value set into short intervals gives a large value at a low height. Rare heights are controlled by the first return.
4. Doubling (`defect_two_mul_le_antiDefect`, `three_four_one`). `ω ↦ ω²` sends both corners to `+1`: a visit near `−1` at `t` is a visit near `+1` at `2t`. This is `3 + 4cos + cos 2 ≥ 0` on the orbit.
5. Translation (`exists_many_translates`, `not_mem_largeValue_of_count`). Partition the torus into `G^r` cells. Among `G^r m` equally spaced times, `m` share a cell, and their differences are returns of defect `≤ 2π²S/G²`. So one height at level `θ` generates `m` heights at level `θ − 2π/G` in a window of length `G^r mΔ`. A count of separated large values in windows therefore excludes single heights, but only while `G^r` is below the window, that is below the Kronecker scale.

**Resonators are finite-time Bohr isometries.**
6. A Fejér product over a set `Y` of primes is `|R(t)|²`, with `R = Σ_{n∣D} c(n) n^{it}`, `D = Π_{p∈Y} p^m`, and unimodular coefficients. Its window integrals have an exact main term and an error bounded by the integrality `|log a − log b| ≥ 1/max(a, b)`, with no input from linear forms in logarithms. So every window of length `2(N+1)(m+1)^y 4^{my}/η` reaches level `m/(m+1)` on the primes up to `y` (`exists_column_ge_of_primesUpTo`).
7. Boxes need a concentrated kernel. `Π_p w(x_p)^{e_p}`, `w = (1 + cos)/2`, has binomial Fourier coefficients of total mass `1`, whatever the number of primes (`abs_integral_boxWeight_sub_le`). Outside the box of `q`, lowering the exponent of `q` from `2m` to `m` costs `(1 − δ)^m`, which replaces a union bound by `8 m r (1 − δ)^m ≤ 1`. So every window of length `exp((20/δ) y log y)` enters every box on the primes up to `y` (`exists_mem_box`, `eventually_exists_mem_box`).
8. Chernoff for boxes (`abs_integral_boxWeight_sub_le_gap`, `exists_mem_box_gap`). Most of the kernel's mass sits at small frequencies. The frequency of a multi-index `κ` is `log(a/b)` with `ab = Π_p p^{|e_p − κ_p|}`, and `min(L, 2ab) ≤ L^{1−λ}(2ab)^λ`. The binomial kernel is sub-Gaussian, `cosh(u/2)^{2e} ≤ e^{eu²/4}`, so the error is `2L^{1−λ} Π_p 2exp(e_p λ² log² p/4)`. With Chebyshev and the optimal `λ`, every window of length `exp(10 y √(log y · log log y/δ))` enters every box (`eventually_exists_mem_box_sharp`).
9. Dyadic codes for the lower side (`exists_box_missed_dyadic`). The signs of `cos(2^a x)`, `a ≤ J`, separate the dyadic arc centres `π(2k + 1)/2^{J+2}`, `k < 2^{J+1}` (`dyadic_code_injective`), and every point within `π/2^{J+3}` of a centre has its signs, since `2^a` times a centre is an odd multiple of `2^a π/2^{J+2}` away from the zeros of `cos` (`pos_cos_iff_of_near`). The orbit on `[0, T]` crosses at most `2 Σ_{p,a}(⌊T 2^a log p/π⌋ + 1) + 1` sign vectors of the steps `2^a log p`, so below `2^{(J+1)π(y)}` some box of radius `π/2^{J+3}` is missed (`exists_box_missed_dyadic_of_lt`).

**Integers forbid alignment, with a price.**
10. Unique factorization (`le_of_aligned`). Past the diagonal range two distinct products of `k` primes of a set `G` fall into one box of width `π/t`. Alignment to within `ε` puts `t log(a/b)` within `2kε` of `0`, while `|log(a/b)| ≥ y^{−k}`, so `t ≤ 2kεy^k`. Only the cardinality of `G` enters, so the saving survives deleting primes (`saving_on_any_set_of_primes`, `saving_at_the_top_of_the_column`). The price is a power of `T`.
11. Tarry–Escott words (`exists_not_aligned`, `exists_not_aligned_of_large`). A word `c` with vanishing moments makes `Σ c_a log(x + a)` tiny and slowly varying, so at a suitable `x` the phase `t Σ c_a log(x+a)/2π` is at distance `≥ ¼` from the integers. Alignment of every integer in `[x, x + M]` would put it near an integer. This uses that every integer in a short interval is a product of the generators.
12. Squared words and the logarithmic Hankel form (`logForm`, `exists_band`, `le_sum_primes_phaseDist`, `le_sum_primes_critical`). The phase of `Σ c_a c_b log(x + a + b)` is positive, decreasing and log-convex in `x`, with no cancellation to control. So its crossing of `½` is slow, a band of real arguments. Since the word has mass zero the phase depends only on `x/h`, so the band gives misaligned integers of positive density, on every progression. Their mean distance is carried by the primes at weight `1/p`.
13. Height against length (`exp_neg_le_sum_primes_critical`). Words of height `H` trade `ℓ¹` mass for length: order `L` at length `L^A` costs `H^{O(1)}` with `log H ≍ L^{2−A} ℓ`.
14. **Escape from progressions** (`exists_prime_escape`, `exists_prime_escape_rank`). The squared phase `y(u)` moves slowly along every lattice `(β + n)/h`, by log-convexity (`exists_grid_point`). If the `θ_p` lie near a model `ψ_p`, then `y(x/h)` lies near the values of the model on the progression. When the model has rank `d` and width `E`, those values form a set of size `≤ (2WE + 1)^d`, `W = (M + 1)²Λ`, and a cell of `[¼, ½]` is free of them (`exists_free_cell`). The phase lands in that cell, which is a contradiction. So generators cost their number, not their size.
15. **Where the words stop** (`primorial_dvd_of_free`, `squared_word_pattern`). A progression of `K ≥ z` terms free of the primes up to `z` has every such prime in its step, so `θ(z) ≤ log q`: the mean-distance theorem runs over full progressions and deletes only the primes up to `≍ log y`. A squared word with moments vanishing to order `k` has a pattern `x + h(a + b)` of at least `2k + 3` distinct sums, and if these avoid a prime `p ∤ h` its support occupies at most `p/2` classes modulo `p` (Cauchy–Davenport). So a word living on integers with only large prime factors is an admissible almost-prime pattern of size a power of its height.

**The energy is the moment.**
16. `clockedMoment_eq`: the Fejér-clocked moment of the orbit is exactly the near-diagonal sum, oscillating at height `T₀`. Through the diagonal range the energy is diagonal (`energy_le`). At every `k` a fibre of the product has at most `k!` tuples and the kernel over the integers near `m` has mass `≲ m/H`, whichever integers occur (`energy_le_past_diagonal`). Every large value contributes (`card_mul_le_clockedMoment`), and the start of the orbit contributes `S^{2k}/(8kΛH)` (`energy_ge_start`): the mixing term forced by Cauchy–Schwarz is the pole. The oscillating energy is bounded by the modulus on the window (`shiftedEnergy_le_of_norm_le`).

**Rank.**
17. At rank one (`IsRankOne`) the orbit is periodic whatever the size, exact returns have positive density, and products collide (`tupleStep_eq_of_coeff_sum_eq`). At finite rank `r` the return time is `Q^r` whatever the size (`exists_return_of_rank`). A continuous system has no torus (`tendsto_continuousColumn`).

**The two-point test.**
18. Test a decomposition on `(1, −1)` at `s` and at `s + iτ`, with `τ` a return. Prime coordinates barely move and contribute a nonnegative amount; the Gamma coordinate is tiny at `s + iτ`. What remains is `|S(s)| ≤ |G(s)|` (`two_point_inequality`, `norm_le_of_returns`). With all primes the return errors are dominated by `Σ_p p^{−2σ}`, which converges on `Re s > ½` (`two_point_inequality_all`).
19. At rank one the same test is Schwarz–Pick (`exists_certificate_iff`): the determinant of the quotient kernel is the pseudo-hyperbolic comparison.
20. Products decompose (`hasSum_of_product`): `S = Π z_n` has kernels `Π_{m<n} z_m(x) conj z_m(y)` of rank one. So each prime can pay its Euler factor out of a share of the Gamma factor, through coordinates `(s + 3)^{−α_p} E_p(s)` that do not return (`euler_test_has_height_certificate`).

**The hull is lacunary.**
21. Unique factorization makes the pair characters `x_p conj x_q`, `p ≠ q`, orthonormal (`integral_pairChar_mul_conj`), so the characters of the gauge torus form a lacunary family (`isLacunary_twist`). By Bessel a set `E` of positive measure correlates with few of them, and beyond some `P` the off-diagonal is at most half the diagonal: `(|E|/2) Σ_{P≤p} |a_p|² ≤ ∫_E |Σ_{P≤p} a_p x_p|²` (`le_setIntegral_normSq`). Since `Σ 1/p = ∞`, the prime sums `Σ_p p^{−s_j} x_p`, `Re s_j ↓ ½`, perturbed by anything bounded in `L²`, stay bounded only on a null set, for every lacunary family (`IsLacunary.measure_bounded_primeSumOf_eq_zero`, Zygmund's argument). The logarithm of a fibre is the prime sum plus the remainder `Σ_p (−log(1 − z_p) − z_p)`, whose quadratic part runs over the squares of primes and is bounded in `L²` up to the line. A continuation across a point of the line is nonzero at a nearby rational height, where the logarithm stays bounded along a ray. Unbounded rays forbid continuation (`no_continuation_of_rays`), so the line is a natural boundary (`ae_natural_boundary`).
22. The same logarithm works over any point unimodular on the primes (`exp_tsum_eq_tsum`, `analyticOnNhd_hullRem`): continuation to `Re s > ½` is a question about the prime sum alone. With fair coins on the primes, the prime sum is a centred series of independent terms with variance `Σ_p p^{−2σ}`, and Kolmogorov makes it converge almost surely past `½` (`measure_coordSeriesConverges_sign`). So almost every order-two point extends zero-free (`ae_signFibre_extends_zeroFree`). The coins are lacunary too: over pairs `p < q` the products `X_p X_q` are orthonormal, since `p q' = q p'` forces `(p, q) = (p', q')` (`integral_pair_sign`, `isLacunary_sign`). The quadratic part of the logarithm is now deterministic, `½ P(2s)`, but `P = log ζ − h` with `h` analytic on `Re w > ½`, so `P' = ζ'/ζ − h'` is bounded near `1 + 2iq` for `q ≠ 0` and `P(2s)` stays bounded along the rays (`exists_bound_primeZeta`). So the line is a natural boundary there as well (`ae_sign_natural_boundary`).

## 5. The questions, and their answers

| Question | Answer | Lean |
|---|---|---|
| How long does the orbit need to enter a half-space at `y = L^{2K}`, `K > ½`? Any saving against size? | Every window of length `exp(c_m y₀)` enters level `(m/(m+1)) S(y₀)`, and every window of length `exp(10 y₀ √(log y₀ log log y₀/δ))` enters every `δ`-box on the primes up to `y₀`. Past the Kronecker scale the column never reaches size, nor does its modulus against any rotation. On all primes the saving exceeds `T^{−δ}` for every `δ` at every `K > ½`, is at least `exp(−L^β)`, `β > 2 − 2K`, up to `K = 1`, and of order `L^{−8}ℓ^{−4}` at `y ≥ 48 L²ℓ`. The modulus saves `L^{−19}ℓ^{−14}` at `y ≥ 10⁹ L⁶ℓ⁴`. With every prime up to `L^{A'}` deleted, `1 < A' < 2K`, the saving is still `T^{−2(2K−A'+1)/(A'−1)−δ}`. Separated visits at level `θ` number at most `H^{1/(2K)+o(1)}` at `H ≍ T`. | `question_one`, `question_one_boxes_and_rotations`, `eventually_exists_mem_box_sharp`, `card_largeValue_le` |
| Near-diagonal energy past `k = L/log y`? | It is the clocked moment. At every `k` it is at most `k!(Σ r^{−2σ})^k + 24 k!(Σ r^{1−2σ})^k/H + 32 S^{2k}/H²`, and at least the diagonal and `S^{2k}/(8kΛH)`. At `σ = ½` the two sides differ by `k!(log y/4)^k`, which is the unknown density of smooth numbers in short intervals. The positive count never sees a saving. The oscillating energy does: at height `T` it is at most `(S − c L^{−19}ℓ^{−14})^{2k}`. Diagonal data cannot exclude a return. | `question_two`, `question_two_past_the_diagonal`, `shiftedEnergy_critical_le`, `diagonal_data_cannot_exclude_return` |
| Why is the Gamma coupling at the critical growth `κ = ½`? | The theta amplitude counts integers (Poisson): `f(x)e^{x/2} → ½`. The diagonal cost of the Bernstein test divides by the count of the test integers. So against integers the cost balances exactly, against primes it loses one logarithm, and below `½` it vanishes. Both `½`s are the pole of `ζ`: the centre of the functional equation is half the pole, and `Σ n^{−2σ}` diverges there. | `question_three` |
| Which functions on `X` restrict to the Ξ-current and have a sum-of-squares form with `t`-dependent coefficients? | For `σ > 1` the current `2 Re(ξ' conj ξ)` is the restriction of `𝒥_σ(t, ω) = 2|ξ|²(B(σ + it) − Σ_n Λ(n) n^{−σ} Re ω(n))`; its worst point on every fibre is the pole `ω = 1`, so `𝒥_σ` is nonnegative on the fibre exactly when the base pays `−ζ'/ζ(σ)`. Pointwise in `t`: all nonnegative ones, tautologically. Frozen on a window past the Kronecker time: only those paying size. Above the size curve: explicit, column by column, with an outer factor. Kernel-valued with returning prime coordinates and a Gamma coordinate: only those dominated by the Gamma coordinate, for finitely many primes and for all primes on `Re s > σ₀ ≥ ½`, so a Schur function carrying the Euler factor `ζ(2s−1)/ζ(2s)` has none. With coordinates that see the height it does have one. At one coordinate: exactly the Schur functions. | `question_four`, `question_four_xi_current`, `question_four_height_coordinates`, `no_decomposition_euler`, `exists_certificate_iff`, `rank_one_law` |
| Over which torus points does the hull extend into the strip, and which carry zeros? | Finite modifications of orbit points: meromorphically, with exactly the translated zeros of `ζ`. Dirichlet characters: entirely, with the zeros of `L(s, χ)`, and zero-free on `Re s ≥ 1`. The Liouville point, also of order two: `ζ(2s)/ζ(s)`, holomorphic on `Re s > ½` iff RH. Haar-almost every point: holomorphic on `Re s > ½`, zero-free, and the line `Re s = ½` is a natural boundary. Almost every order-two point: holomorphic and zero-free on `Re s > ½`, with the line as natural boundary; the Liouville point extends holomorphically to `Re s > ½` iff RH. RH is the zero-freeness of every nonzero limit of vertical translates. | `question_five`, `fibre_extends_of_character`, `ae_natural_boundary`, `ae_sign_natural_boundary` |
| Does a large-value set have additive structure, forcing returns the pole must pay for? | Yes. Differences have level `θ²` on average, and at the corner the set is an approximate group. At weights `1/p` the pole prices each level: `θ S ≤ log(8 log u + 39) + C`, so a height at level `θ` lies above `exp(c(log z)^θ)`, and the number of large values in a window is bounded through the first level the pole permits. At weights `p^{−½}` the pole pays nothing. | `question_six`, `pair_level_le`, `card_le_of_pole` |

## 6. Pillar theorems

All are unconditional. The hull theorems are equivalences with RH and are stated as such.

| Theorem | Lean |
|---|---|
| Group closure, transport, corners | `sqrt_defect_add_le`, `column_sub_sq_le`, `defect_two_mul_le_antiDefect` |
| Large-value structure and descent | `sq_sum_column_le`, `card_pairs_ge`, `exists_low_return_of_many_large_values` |
| Finite-time Bohr isometry on half-spaces and on boxes; Chernoff for boxes; the mixing bracket | `exists_column_ge`, `exists_mem_box`, `exists_mem_box_gap`, `eventually_exists_mem_box_sharp`, `exists_box_missed`, `exists_box_missed_dyadic_of_lt` |
| Transfer by translation | `exists_many_translates`, `not_mem_largeValue_of_count` |
| Pigeonhole non-alignment; power saving on any set of primes and at the top of the column | `le_of_aligned`, `saving_against_size`, `saving_on_any_set_of_primes`, `saving_at_the_top_of_the_column` |
| Non-alignment at every large height, away from every torsion point | `exists_not_aligned_of_large`, `exists_prime_not_near_torsion`, `exists_not_aligned_of_large_of_word` |
| Escape from progressions of low rank; every rotation; many misaligned primes | `exists_prime_escape_rank`, `exists_prime_not_near_rotation`, `exists_prime_not_mem_of_large` |
| Where the words stop: full progressions, patterns of squared words | `primorial_dvd_of_free`, `sum_log_le_log_of_free`, `squared_word_pattern` |
| The modulus stays below size | `norm_sum_primes_le`, `norm_sum_le_of_large`, `norm_sum_ap_le_of_large`, `norm_zeta_le_of_large` |
| Saving at every length; past the size horizon; away from small primes | `rpow_neg_le_sum_primes_critical`, `exp_neg_le_sum_primes_critical`, `le_sum_primes_critical`, `le_sum_primes_liouville`, `le_sum_primes_critical_coprime_of_large` |
| Moment = energy; start of the orbit; energy at every order; oscillating energy | `clockedMoment_eq`, `energy_ge_start`, `energy_le`, `energy_le_past_diagonal`, `card_largeValue_le_past_diagonal`, `shiftedEnergy_critical_le` |
| Rounded orbit: diagonal data cannot exclude a return | `diagonal_data_cannot_exclude_return`, `exists_collision` |
| Agler wall; first and second test; sharpness | `two_point_inequality`, `agler_wall`, `two_primes_first_test`, `agler_wall_all_primes`, `euler_test`, `selfDecomposition` |
| The lift of the Ξ-current; its fibre minimum at the pole | `xiCurrent_eq_xiLift`, `lamColumn_le_pole`, `xiLift_nonneg_iff`, `xiCurrent_nonneg_of_size_le` |
| Rank one; coordinates that see the height | `exists_certificate_iff`, `rank_one_law`, `hasSum_of_product`, `euler_test_has_height_certificate`, `hasSum_of_exp` |
| Corners and parity | `clockedColumn_eq`, `clockedColumn_neg_one`, `clockedMomentAt_le_energy` |
| Hull | `riemannHypothesis_iff_liouvilleFibre_extends`, `ae_fibre_extends_zeroFree`, `fibre_zero_iff`, `riemannHypothesis_iff_limits_zeroFree`, `fibre_extends_of_character` |
| Lacunary families; Zygmund; natural boundary | `isLacunary_twist`, `IsLacunary.le_setIntegral_normSq`, `IsLacunary.measure_bounded_primeSumOf_eq_zero`, `no_continuation_of_rays`, `ae_natural_boundary` |
| Logarithm of a fibre; typical order-two points | `exp_tsum_eq_tsum`, `analyticOnNhd_hullRem`, `measure_coordSeriesConverges_sign`, `ae_signFibre_extends_zeroFree`, `isLacunary_sign`, `exists_bound_primeZeta`, `ae_sign_natural_boundary` |
| A zero forces an entry | `isolated_zero_forces_entry` |
| Pole price | `column_le_pole`, `not_mem_largeValue_of_lt`, `card_le_of_pole`, `eventually_not_mem_largeValue` |
| Critical coupling | `tendsto_thetaAmp_left`, `tendsto_thetaAmp_integers`, `tendsto_thetaAmp_div_primeCounting` |

## 7. Tools

Each tool is stated with what it reaches and where it stops.

| Tool | Reaches | Stops at |
|---|---|---|
| Non-alignment below the mixing time | Words: precision `L^{−C}` at `y ≍ L²ℓ`, and rotation-proof at `y ≍ L⁶ℓ⁴`. Pigeonhole: on any `L^{A'}` primes at precision a power of `T` | Words use every small prime, so they cannot see only the top of the column. Both Q-progressions and rank generators stop at the primes up to `≍ log y`: a full progression free of the primes up to `z` has step `≥ e^{θ(z)}`, and a squared word on large primes is an admissible almost-prime pattern of `≥ 2k + 3` sums |
| Near-diagonal energy past `k = log T/log y` | Upper and lower bounds within `k!(log y/4)^k` at every `k`; the oscillating energy below size | The factor is the density of `y`-smooth numbers in intervals of length `N/T` |
| Discrepancy against Haar at `y > log T` | Characters of height `≪ L`; boxes of radius `ρ` missed below `exp(π(y) log(π/4ρ))/θ(y)` by dyadic sign patterns, `δ`-boxes entered from above at `exp(10 y √(log y log log y/δ))` | A gap `(log y)^{3/2} √(log log y)` in the exponent of the mixing time at fixed `δ`, from the union bound over the primes |
| Transfer from typical to rare heights | Group closure, Halász–Montgomery, descent to the first return, translation of one large value into `m` (`exists_many_translates`), large-value counts at every scale, the isolated-zero bridge | Translation needs a return before the window ends, so its window `G^{π(y)} mΔ` is the Kronecker scale; typical bounds do not reach single heights past it |
| Certificates with prime conductances | Rank-one Pick criterion; the wall on returning coordinates, sharp; product certificates with coordinates that see the height | A constant share of the base pays only down to size at `t = 0`, and unconstrained coordinates carry no information (`hasSum_of_exp`) |

The mechanisms give reusable general statements: the metric calculus of any phase system; the integer-gap integral for arbitrary multi-indices; the model and the free cell for arbitrary finite value sets; the fibre and kernel bounds for arbitrary sets of primes; product and two-point tests for arbitrary coordinates.

## 8. Test systems

| System | Behaviour | Lean |
|---|---|---|
| Curves, Golden, commensurable steps | rank one: periodic orbit, exact returns of positive density at any size, weights irrelevant; products collide, so every integer argument is void; certificates are the Schur property | `defect_period`, `exists_exact_return`, `shiftedEnergy_period`, `tupleStep_eq_of_coeff_sum_eq`, `rank_one_law` |
| Finite rank | return time `Q^r`, independent of the number of steps | `exists_return_of_rank` |
| Integers | infinite rank, with integrality and additive structure | `not_isRankOne_log`, `le_of_aligned`, `exists_prime_escape_rank` |
| Rounded primes | same weights, same orbit to time `cT`, same diagonal moments, exact return at `T`; loses unique factorization past the mixing range | `diagonal_data_cannot_exclude_return`, `exists_collision` |
| Continuous Beurling | no torus: the column dies, the orbit never returns. Non-alignment alone decides nothing | `tendsto_continuousColumn`, `exists_defect_ge` |
| Integer-norm systems | same steps, different weights: the box and half-space theorems are weight-free or hold for every weight, so an orbit statement cannot separate `ζ` from such a system; it must be excluded through the amplitude | `exists_mem_box`, `sum_one_sub_cos_le_of_box`, `exists_column_ge_of_primesUpTo` |
| Liouville twin | same absolute moments and energies, opposite sign at the start of the orbit | `norm_twist_neg_one`, `clockedColumn_neg_one` |

## 9. Open research topics

1. **The required saving.** At `y = (1+ε)L²/16` a one-sided bound at the level of the base needs a saving `≍ εL/ℓ` on the top of the column. A macroscopic theorem, `sup_{[T,2T]} P ≤ (1 − c)S` for some `K > 1`, is quasi-RH strength up to crystal shielding. What is the largest saving at length `L^{2K}`?
2. **The location of the saving.** Polylogarithmic precision reaches the primes above `≍ log y` and no further: a progression prime to `Q` has length `≥ Q`, and a generator costs a factor `L⁴`. On the top of the column the proved saving is a power of `T`. Does the top carry a saving larger than every power of `T`?
3. **Precision on a set of primes.** Is the exponent `2(A − A' + 1)/(A' − 1)` the truth on sets of `L^{A'}` primes? Counting smooth numbers alone cannot beat precision `T^{−1/(A−1)}`: a comb of density `y^{−k}/T` is consistent with every count. Below `A' = 1` the count `C(|G|, k) > T` fails and only Baker remains.
4. **Smooth numbers in short intervals.** The energy past the diagonal is `diagonal + start` up to `k!(log y/4)^k`. Any saving on this factor is a count of `y`-smooth numbers in intervals of length `N/T` with `y` polylogarithmic in `N`.
5. **The rank of the orbit.** More than `d` primes up to `L^{9d+6}` are misaligned at precision `L^{−9d−10}`. Is the number of misaligned primes at fixed precision `L^{−C}` a power of `y`?
6. **Mixing time.** `½ π(y) log(1/δ) ≲ log T_mix ≲ 10 y √(log y log log y/δ)`. The union bound costs `log y/δ` in the degree of the kernel. Does a sieve-type minorant of the box remove it, and is `exp(cy)` the truth?
7. **Certificates.** Which class of coordinates, tied to `p^{−s}`, gives a certificate below size at `t = 0`?
8. **The hull.** The exact zero-carrying set when RH fails; which order-two points extend, a set of full coin measure that contains the Liouville point iff RH; the torus points whose fibre continues across the line, a Haar-null set containing the orbit and the characters: which others does it contain?
9. **Arithmetic Bernstein between growth `½` and `1`.** The Euler collapse kills perturbations at `α ≤ 1`, the mechanism stops at `½`.

## 10. Traps

| Trap | Truth |
|---|---|
| Diagonal moments exclude a return | A rounded orbit has identical diagonal moments and an exact return at `T` |
| Near-diagonal counts prove a saving | The start of the orbit alone gives `E_k ≥ S^{2k}/(8kΛH)`, whose `2k`-th root tends to `S`: the positive energy sees size |
| A saving at the corner is a saving for moments | Moments see `|P|`, and a common rotation has full modulus. Only a rotation-proof saving passes to the moments (`norm_sum_primes_le`) |
| The mixing term is statistical | It is `t = 0`, the pole |
| Effective Kronecker needs Baker | Half-spaces and boxes need only the integer gap |
| A box costs what a half-space costs | A half-space controls the average coordinate; a box controls all of them, and the concentrated kernel pays a factor `log y` in the exponent |
| Bohr's isometry holds at finite time | Up to `y ≍ log T` for half-spaces; past that the orbit misses boxes |
| Kernel-valued conductances evade frustration | With returning coordinates they pay nothing beyond the archimedean coordinate (`agler_wall_all_primes`) |
| Coordinates that do not return are a breakthrough | Every zero-free Schur function is the product of its own roots (`hasSum_of_exp`). The content is in how a coordinate depends on `p^{−s}` |
| Agler's bidisc theorem contradicts the wall | A function of `(2^{−s}, 3^{−s})` is almost periodic and does not decay; the wall concerns functions that see `t` |
| `t`-dependent coefficients are a new tool | Pointwise they are tautological (`graph_lift`); slow ones cost size (`frozen_certificate_costs_size`) |
| Any saving against size moves the sign | The sign needs the saving to reach size minus base, `≍ εL/ℓ` just past the horizon; the proved saving is of order `L^{−8}ℓ^{−4}` |
| A saving on all primes is a saving at the top | Words use every small prime; the size sits at the top, where the proved saving is a power of `T` |
| Below the size horizon a saving is needed | Size fits under the base there; there is nothing to save |
| Torsion points behave alike | Characters extend unconditionally; the Liouville point extends iff RH; both have finite order (`fibre_extends_of_character`) |
| Absolute moments separate the twin | `|P_{−1}| = |P|`: only a signed functional at the start can |
| Non-alignment decides the critical line | Continuous Beurling systems have no returns, so it decides nothing there |
| Zeros over a Haar-null set means no zeros | The orbit itself is Haar-null |
| A typical fibre continues past the line like `ζ` | The line is a natural boundary almost surely, over the torus and over the order-two points (`ae_natural_boundary`, `ae_sign_natural_boundary`); continuation is a property of a null set containing the orbit and the characters |
| The box time is set by the largest integer of the kernel | Most of the kernel's mass sits at small frequencies; the Chernoff form saves `√(log y/log log y)` in the exponent |
| A typical-height count reaches every height by translation | Translation needs a return inside the window; past the Kronecker scale there may be none |
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
| Uses | HTGeometry (log separation, window means, simultaneous Dirichlet, Hurwitz, Schwarz–Pick), RHTower (Abel summation, Liouville series, zero-free right half-plane, near-one bound, prime harmonic lower bound, zeta bounds on `Re s > 1`), ArithmeticCorrelationGeometry (gauge torus, almost-sure square root), SignedSuccessorArithmetic (prime cosine sum against `ζ`), ArithmeticInnerFunctionTheory (column shape), ArithmeticPositivityTheory (single-height visibility) |

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

Forced: the orbit is a group, so large values form an approximate group, doubling identifies the two corners, and rare heights descend. The integers separate, so effective Kronecker holds for half-spaces and boxes with no Baker input, and the orbit is uniform on low-degree characters up to the last diagonal scale. The prime characters are lacunary, so over a Haar-typical point the hull ends exactly at the critical line. Unique factorization and Tarry–Escott words forbid alignment at every length past the Kronecker scale. The prime phases do not lie near any rotation or any progression of low rank, so the saving against size holds for the modulus, the quantity moments see. It is a power of `log T` past the size horizon, it grows with the length away from small primes, and at the top of the column it is a power of `T`.

Not forced: nothing in the diagonal data, group closure or the orbit up to `cT` excludes a return at `T`, since a rounded orbit has all of these and does return. Near-diagonal counts contain the start of the orbit, so they see size and nothing less. Kernel-valued prime-by-prime certificates with returning coordinates pay only what the archimedean coordinate dominates, so the Euler factor of the scattering function cannot be paid in that form. Coordinates that see the height do pay it, down to size at `t = 0`. The pole prices the weights `1/p` and is silent at `p^{−½}`.

So the problem is located: the oscillating near-diagonal sum past the diagonal range, at the top of a column just past the size horizon, at a required saving of order `L/ℓ`. What is proved there is `L^{−8}ℓ^{−4}` on all primes, a growth `√(log y)` away from the primes up to `log y`, and a power of `T` at the top. It cannot come from a positive count, from diagonal moments, from a frozen certificate, or from a coordinate that returns. The two mechanisms in hand are complementary. Words reach precision polynomial in `1/L`, but stop at the primes up to `log y`. Pigeonhole lives anywhere on the column, at precision a power of `1/T`. Combining them, precision polynomial in `1/L` on a positive proportion of the top of the column, is the next theorem to aim at. It would still fall short of the required saving unless the precision becomes macroscopic, and that last step is the quasi-RH core.
