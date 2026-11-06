# Multiscale Analysis of the Mollified Zeta Field (MZF)

Namespace `GaloisForLFunctions.MultiscaleMollifiedZetaField`; umbrella `MultiscaleMollifiedZetaField.lean`.
Every theorem below is unconditional. A statement about RH is an equivalence with RH, and no theorem has RH as a premise.

## 1. Motivation

Route WD reads the zeros of `ζ` through the mollified field `F = ζM`, `M` a Dirichlet polynomial. Its results all come from
one method, second moment plus Jensen, and that method has three proved limits: polynomial length has a moment floor
`1 + 1/(8+6θ)` (APR); moments do not determine the log-mean (Π19); occupied-window bounds lose a factor `log V` against
the target `D_win` (CDG).

Two branches remain, and they fail for different reasons.

- **The density branch** (`D_win`, clustering) is sub-RH. A unit window holds about `log V` zeros, so counting them one at a
  time loses `log V`.
- **The RH branch** asks for a bound on `∫_1^T|ζM_{T^θ}(½+it)|²dt` with `T`-exponent independent of `θ`. Its exact θ-slope
  is `2·zetaZeroWidth`, so closing the slope to `0` is RH (card `WD-LONG-MOEBIUS-SLOPE-LAW`). This is the **residual**.

Probabilistic number theory has a known way past union bounds: `log|ζ(½+it)|` behaves as a log-correlated field with primes
in dyadic scales as branching steps, and barrier arguments control maxima of such fields (Fyodorov–Hiary–Keating,
Arguin–Bourgade–Radziwiłł, Harper). MZF builds that language for the mollified field in this corpus, and proves exactly
what it reaches and what it cannot reach on each branch.

## 2. Objects

| Object | Meaning |
|---|---|
| Mollified error | `E_M = ζM − 1`, `M = Σ_{n≤N} b_n n^{−s}`; `E_X = ζM_X − 1` for the long Möbius polynomial `M_X` |
| Prefix cancellation | the coefficients of `ζM` vanish on `2 ≤ n ≤ y` |
| Line Poisson weight | `P_ρ(u) = δ/(π(δ² + (u−γ)²))`, the harmonic measure of `Re z > ½` seen from `ρ = ½+δ+iγ` |
| Low set | `lowSet X κ = {u : |E_X(½+iu)| ≤ X^κ}` |
| Prime field | `F(t) = Σ_{p∈P} w(p) cos(t log p)`; with `w = p^{−1/2}`, the real part of the prime sum on the line |
| Steinhaus model | `S = Σ_p w(p) Re X_p`, independent uniform phases `X_p` |
| Mass | `W = Σ_p w(p)²`; with `w = p^{−1/2}` the reciprocal sum `Σ_{p≤Y} 1/p` (variance `W/2`) |
| Prime walk | `S_j(t) = Σ_{p≤y_j} p^{−1/2} cos(t log p)` at the cuts `y_j = ⌈exp(exp j)⌉`; each block carries mass `1 + O(e^{−j})` |
| Barrier | the envelope `√(K_j W_j)`, `K_j = ⌈4 log(j+2)⌉` |
| Integrated polynomial | `P_x(s) = Σ_n Λ(n) W_x(n) n^{−s}/log n`, whose `σ`-derivative is `−D_x`, Selberg's smoothed von Mangoldt polynomial |
| Off-line point | `½ + R + it`, `R = κ/log T`; `κ` is the depth |
| Length regimes | below the window `X ≤ T^{1−ε}`: primes behave independently; above the window `X ≥ T^{1+ε}`: the Selberg-integral regime; compact window `X → ∞` at fixed height |
| Euler piece | `Π_{p∈B}(1 − p^{−s})`, coefficients `eulerCoeff B`; the gcd form `G_s(a) = Σ a_h a_k gcd(h,k)^s/(hk)` |
| Occupied heights | `τ` whose unit window `[τ, τ+1]` holds a zero of depth `≥ D` |
| Near-line receivers | `D_win`, `D_zero`, clustering, the shifted-defect detector (CDG) |
| Short weight | `W = Σ_{m≤z} w_m m^{−s}`, `w_1 = 1`, `|w_m| ≤ 1`: the proxy `|W|²` of a barrier event |
| Camera test | `K(u) = δ⁻¹ v((u − y)/δ)`, `v ≥ 0` a `C²` profile on `[−1,1]`; centre `y`, width `δ` |
| Zero field | `Z_{y,δ}(t) = Σ_ρ m_ρ K̂(γ_ρ − t − i b_ρ)`, `b_ρ = β_ρ − ½` |
| Camera polynomial | `C(t) = Σ_n Λ(n) K(log n) n^{−½−it}` |

## 3. Language

- **Floor, cap.** A floor is a lower bound for a functional of `E` forced by a zero; a cap is an upper bound forced by a zero-free
  region.
- **`L⁰` statement.** A statement about the size of `E` on most points of a window, with no moment. It is the weakest form
  of a size statement and survives restriction to any event.
- **Slope.** The rate `lim log(functional)/log X` in the length.
- **Hole.** A point where `|E| ≥ 1`. Every zero of `F` lies in a hole; a hole need not contain a zero.
- **Last scale.** The primes just above the mollifier, near `T^{Θ(1)}`, where products exceed `T` and mean values stop.
- **Bohr lift.** The Dirichlet polynomial read as a function on the torus of primes; independence means Haar measure on it.
- **Purity-blind.** A functional of the partial prime sums that takes the same value on a pure field and on a field with off-line zeros.
- **Occupancy threshold.** The depth above which the proportion of occupied unit windows tends to zero.
- **Dominant, isolated, clustered.** Three grades of a zero against its camera window: the field is at least half its term;
  the companions have small weighted mass; at most `N` zeros in the sector and small mass outside.
- **Sector.** The window `|γ − t| δ ≤ 1/10`, on which camera weights have positive real part.

## 4. Mechanisms

**A. Half-plane Jensen at a zero.** On `Re z ≥ ½`, an entire function of polynomial growth satisfies
`log|F(ρ)| ≤ ∫P_ρ log|F(½+iu)|du`. Apply it to `y^{z−½}(z−1)E_M(z)`: the coefficients of `E_M` start after `y`, so the factor
`y^{z−½}` costs nothing as `Re z → ∞`, and it gains `δ log y` at `ρ`. At a zero `E_M(ρ) = −1`. So a zero forces a floor on the
logarithmic mean of `|E_M|`, not only on its mean square.

**B. Floor against cap.** A zero-free region caps `log|E_X|` pointwise by `(width+ε) log X`. At a zero of nearly maximal depth the
Poisson mean reaches that cap, and a function under a cap whose mean reaches the cap is close to the cap in `P_ρ`-measure. The
Poisson mass of the low set is at most `(w−δ)/(w−κ)`, so restriction to any event of definite `P_ρ`-mass keeps the slope.

**C. Bohr transfer.** Below the window, moments of `F` are the moments of `S` up to `2(AY)^j/T`: the monomials of `F^j` have
frequencies `log(m/n)` with `|log(m/n)| ≥ 1/max(m,n)`, the window mean of a nonzero frequency is small, and the zero-frequency part is the
Steinhaus expectation.

**D. Taylor at order `2K`.** `|e^{iy} − Σ_{k<n}(iy)^k/k!| ≤ |y|^n/n!` compares the height average of `e^{ivF}` with the model through
`2K` moments. The even moment `E S^{2K}` is bounded from the moment generating function.

**E. The sharp phase.** `E e^{b Re X_p} = I₀(b) ≤ e^{b²/4}` through the recursion `∫cos^{k+2} = ((k+1)/(k+2))∫cos^k`. This gives
the true proxy `½`, hence `P(S ≥ λ) ≤ e^{−λ²/W}`, the exact Gaussian exponent, and through the transfer the same exponent on heights.

**F. Poisson mass per zero.** `Re ξ'/ξ` is a sum of signed Poisson kernels `(u−β)/((u−β)²+(t−γ)²)` over the zeros. Each has mass at most `π`
in `t` at every abscissa, so by Tonelli a zero costs `πR` across a segment of length `R`, with no logarithmic loss even when the zero lies
on the segment. The real part is what makes this work: the modulus `1/|s−ρ|` would lose `log(1/R)`.

**G. Integrating Selberg's formula.** The explicit formula holds on `½ ≤ Re s ≤ 3/2`, so integrate it from `Re s = 3/2`, where
both `log|ζ|` and `P_x` are bounded. Off the exclusion windows `|γ−t| ≤ 12Rx^{3(β−½)}` each kernel along the segment is an exponential in
`σ` times a Lorentzian in `t`, and the integrated majorant has mean `≪ e^{−κ/60000}`.

**H. Blocks do not interact.** On coprime integers `gcd(hk, h'k') = gcd(h,h') gcd(k,k')`, so the gcd form factors, with local factor
`1 − 2/p + p^{s−2}`. Each block removes its reciprocal mass from the factor `log U` of the second moment.

**I. Every prime above the mollifier has coefficient one.** For `p > y`, `c_p = b_1 = 1`, whatever `Ψ` is. The primes of
`(V^θ, V^{θ+1/a}]` have mass `≍ 1/a` and are damped by `≍ e^{−2θa}` on `Re s = ½ + a/L`. This defect is a property of the
last scale, and a barrier on smaller primes does not touch those coefficients.

**J. Mimicking a barrier.** One impure factor at `p₀ ≈ V^{1/A}` with coefficient `c = p₀^{½+A/log V}` moves each prime sum by at most `8p₀^{−1/2}`-order
quantities and puts a zero on `Re s = ½ + A/log V` in every unit window. Barrier events on prime sums cannot see that factor.

**K. Abel and Hardy.** `M(n) = √n A(n) − Σ_{k<n}(√(k+1) − √k) A(k)` for `A(n) = M_n(½)`, and a discrete Hardy inequality bounds the Mertens
pronic energy by four times the log energy of `A`.

**L. The block copies the profile.** `(ζΨ − 1)W = ζ(ΨW) − W`. For a prime `p` above the length of `ΨW`, `c_{pm} = c_m`: the block primes copy
the whole low-frequency profile of `ΨW` to `pm`, where `W` has no coefficient to cancel it. The energy gains the factor `1 + Σ_p p^{−2σ}`, and
everything below the block cancels against `W` as the perfect square `Σ_{m≤z}|c_m − w_m|² m^{−2σ} ≥ 0`.

**M. The camera.** The explicit formula of the twist `e^{−itu}K` reads `Z_{y,δ}(t) + C(t) = O(1 + log t/δ)`. A Dirichlet polynomial on
`log n ∈ [y − δ, y + δ]` photographs the zeros near height `t` at resolution `1/δ`. A zero of depth `b ≥ 0` has amplitude `≥ ½(∫v) e^{b(y−δ)}` on
its window. The mean value theorem bounds `∫|C|²` by `≪ T(log N/δ)²`, which is `T/c²` at `δ = cL`, for every depth.

**N. The uncertainty scale of a depth.** The weight `e^{bu}` concentrates in the last `L/α` of the range of `u`, so the natural resolution at
depth `α/L` is `α/L`. Tuning `δ = L/(4+α)` loses only a constant in the amplification.

**O. The camera is a power sum in its centre.** At `y = νh`, `Z_{νh}(t) = Σ_ρ B_ρ z_ρ^ν` with `z_ρ = e^{(b_ρ+i(γ_ρ−t))h}`. In the sector the weights
`B_ρ` lie in a half plane whatever the depth, so the top groups of Turán's second main theorem cannot cancel, and no separation is needed.

**P. Each zero costs `π/δ`.** By Fubini the Lorentzian mass `Σ_ρ m_ρ/(1 + δ²(γ_ρ − t)²)` has first moment `≪ T/c`, whereas a near-line zero has camera
weight `≤ e^A` times its Lorentzian. So near-line mass of size `Λ` is confined to measure `≪ e^A T/(cΛ)`.

## 5. Pillar theorems

| Theorem | Statement | Module |
|---|---|---|
| `integrable_and_poisson_log_floor` | prefix cancellation up to `y` forces `∫P_ρ log|E_M| ≥ δ log(y+1) − log(|ρ|/|1−ρ|)` | `TheZeroForcesALogarithmicFloor` |
| `eventually_poissonMass_lowSet_le` | `∫_{lowSet X κ} P_ρ ≤ (w−δ)/(w−κ) + η`: exponent rigidity in Poisson measure | `TheExponentOfTheMollifiedErrorIsRigid` |
| `zetaZeroWidth_le_iff_positive_proportion` | `zetaZeroWidth ≤ β` iff a uniform positive proportion of each window has `|E_X| ≤ X^{β+ε}` for sparse `X` | same |
| `eventually_restricted_secondMoment_ge` | barrier immunity: no event of definite Poisson mass lowers the second-moment slope | same |
| `riemannHypothesis_iff_unit_window` | RH iff `∀ε ∃B ∀X≥1, ∫_0^1|ζM_X(½+iu)|²du ≤ B X^{2ε}`: the height parameter is eliminated | `TheWidthIsReadInOneWindow` |
| `riemannHypothesis_iff_pointwise` | RH iff `E_X` has subpower growth at one point of the line | same |
| `barrier_data_does_not_decide_occupancy` | a mimic field with a zero in every unit window satisfies the same barrier as a pure field with none | `BarriersAreBlindToPurity` |
| `abs_mean_primeField_pow_sub_model_le` | moments of the prime field on `[T,2T]` equal the Steinhaus moments up to `2(AY)^j/T` | `PrimeSumsAreSteinhausBelowTheWindow` |
| `tendsto_primeFieldLaw_gaussian` | the prime field is asymptotically Gaussian when `W → ∞` and `(AY)^K = o(T)` for every `K` | `ThePrimeFieldIsGaussian` |
| `exists_volume_log_norm_zeta_shift_ge_le` | `λ ≤ |log|ζ(½+R+it)| − log|ζ(½+it)||` holds on measure `≤ C R T log T/λ` | `TheLineIsAShiftOfTheField` |
| `exists_volume_log_norm_zeta_sub_logPoly_gt_le` | `|log|ζ(½+R+it)| − Re P_x(½+R+it)| ≤ C₀` off measure `≪ T e^{−κ/60000} + T^{1/2}` | `TheOffLineLogarithmIsThePrimeField` |
| `tendsto_log_norm_zeta_law_gaussian` | **Selberg's central limit theorem** for `log|ζ(½+it)|/√(½ log log T)` on `(T, 2T]` | `SelbergsCentralLimitTheorem` |
| `measureReal_modelField_ge_le` | `P(S ≥ λ) ≤ e^{−λ²/W}` | `ThePrimeWalkObeysItsBarrier` |
| `volume_primeField_ge_le` | `|S| ≥ λ` on `[T,2T]` has measure `≤ T 2e²K²e^{−K} + 2Y^{4K}` for `KW ≤ λ²` | same |
| `volume_barrier_crossing_le` | crossing the barrier at a scale `j₀ ≤ j ≤ J` has proportion `≤ 256/j₀` up to the transfer error | same |
| `exists_abs_walkMass_succ_sub_le` | the dyadic decomposition: each block has mass `1 + O(e^{−j})` | same |
| `gcdForm_blockConv`, `gcdForm_eulerCoeff` | the gcd form factors over coprime blocks; its Euler value is `Π_p(1 − 2/p + p^{s−2})` | `TheTwistedMomentFactorsOverBlocks` |
| `exists_twisted_second_moment_le` | bounded real mollifiers of length `≤ U^{21/50}`: second moment `≤ F(U)((1+ε)(v−a)+εa)` on the upper blocks | same |
| `exists_euler_piece_second_moment_le` | Euler pieces: `F(U) ≈ (e^{2R}/2R) log U Π_{p∈B}(1 − 2/p + p^{2R/log U}/p)` | same |
| `exists_eventually_shiftedDefect_ge` | every normalized mollifier of length `≤ V^θ`, `θ<½`, has shifted defect `≥ (e^{−2}/12)(e^{−2θa}/a) V` | `TheLastScaleSetsTheDefect` |
| `eventually_shiftedDefect_gt_below_threshold` | below `a = (1−ε) log log V/(2θ)` the defect exceeds `C V/log V` for every `C` | same |
| `exists_volume_occupied_windows_le_proportion` | occupied heights at depth `(51/50)a/L` have proportion `≪ (L/a) e^{−22a/25}` | `TheOccupiedWindowsLoseOneLogarithm` |
| `exists_volume_occupied_windows_le_threshold` | at `a = (25/22)(1+ε) log L` the proportion is `≪ L^{−ε}` | same |
| `not_forall_moebiusPoly_energy_le` | `limsup (log T)⁻¹ Σ_{n≤T}|M_n(½)|²/n ≥ ¼ Σ_ρ |ρζ′(ρ)|^{−2}` over any finite set of simple critical zeros | `TheLongMollifierPaysForNegativeMoments` |
| `exists_eventually_weighted_shiftedDefect_ge` | every short weight: `∫|ζΨ−1|²|W|² ≥ (e^{−2}/12)(e^{−2θa}/a) V Σ_{m≤z}|c_m|²m^{−2σ}`, `c = 1⋆b⋆w`, the sum being `≥ 1` | `TheLastScaleSurvivesEveryShortWeight` |
| `exists_eventually_weighted_shiftedDefect_ge_of_prefix` | a mollifier cancelling the prefix up to `z`: the sum is the mean square of `W`, so the average of the defect against `|W|²/∫|W|²` stays above the floor | same |
| `exists_norm_zeroField_add_cameraPoly_le` | the camera equation: `|Z_{y,δ}(t) + C(t)| ≪ 1 + log t/δ` for `e^{y+δ} ≤ t` | `ThePrimeCameraSeesDominantZeros` |
| `exists_volume_zeroField_ge_le_uniform` | `|Z| ≥ λ` on measure `≤ (C₀/c²)T/λ²`, uniformly in `c`, in the centre, and in `λ` | same |
| `exists_card_dominant_zeros_le_rate_two` | at `δ = L/(4+α)`, separated dominant zeros of depth `≥ α/L` number `≪ T L (4+α) e^{−2α}` | same |
| `exists_card_dominant_zeros_le_threshold` | separated dominant zeros of depth `≥ (½+ε) log log T/log T` number `≪ T (log T)^{−ε}` | same |
| `dominatesWindow_of_isolated`, `exists_card_isolated_zeros_le` | isolation, a condition on the zeros alone, implies dominance and the same count | same |
| `exists_nu_norm_zeroField_ge` | a cluster of at most `N` zeros in the sector cannot hide from all `N` centres: loss `κ(N, M)` | `TheTuranCameraSeesBoundedClusters` |
| `exists_card_clustered_zeros_le` | separated zeros in clusters of at most `N`, with small outside mass, number `≪_{c,N} T L e^{−2(1−4c)α}` | same |
| `exists_volume_near_mass_ge_le` | Lorentzian mass `≥ Λ/E` on measure `≪ E T/(cΛ)` | `TheNearLineZerosCannotBlockTheCamera` |
| `exists_card_zeros_without_deep_companions_le` | separated zeros whose competitors are at most `N` in the sector and a small mass deeper than `A/L`: `≪_{c,N} T L e^{A−(1−4c)α}` | same |

## 6. Tools

**Developed here.** Half-plane Jensen with prefix amplification; the exponent-rigidity calculus (Poisson mass of low sets); Steinhaus
moment transfer; the Taylor comparison of characteristic functions on heights; Slutsky on a window (`tendsto_windowLaw_of_close`); the
window law `windowLaw`; the sharp phase moment generating function; the Gaussian tail on heights; the doubly exponential scale grid; the
explicit formula up to `Re s = 3/2` (`exists_selberg_explicit_formula_wide`); `log_norm`-increments along horizontal segments; the
Tonelli cost of one zero (`integrable_and_integral_kernel_le`); the polynomial-difference energy (`sum_polyDiffCoeff_sq_le`); the gcd
form and block convolution; the scaling trick that frees the high-block bound from bounded main terms; the last-scale block; the Gaussian floor at
any positive energy (`gaussFloor_of_pos`, `gaussFloor_of_norm_le`); the twisted first moment against a polynomial
(`norm_integral_zeta_poly_conj_sub_le`); the mean value theorem from below (`integral_normSq_edPoly_ge`); the prime camera at all widths and
centres; the sector of the window (`re_paperFT_profile_ge`); the first moment of the Lorentzian mass (`integral_windowMass_le`).

**Used from the corpus.** Boundary Jensen on the disc (`circleIntegrable_and_sum_log_add_le_circleAverage`), Littlewood's Mertens bound
(`mobiusMertens_subpower_of_zeroFree`), the Möbius field, the Steinhaus model, the symmetrised partial fraction of `ξ'/ξ`
(`two_logDeriv_xi_eq_pair_tsum`), the weighted zero density (`exists_tsum_weighted_density_le`), Selberg's explicit formula
(`norm_logDeriv_zeta_add_selberg_le`), the exclusion windows (`exists_sum_selbergRightWindow_le`), the mean value theorem
(`integral_normSq_edPoly_displaced_le`), the sharp Mertens theorem, the Gaussian floor (`gaussFloor_general_at_scale`), the high-block
bound (`exists_highBlock_bound_of_mainTerm_upper`), the near-line density (`exists_selberg_criticalGate_nearLine_zeroDensity`), the
Mertens energy law (`not_forall_mertens_pronicEnergy_le_log`), the explicit formula of `ζ` (`Zeta23.WeilEF.EF_lit_zetaZeroConfig`), the weighted Turán
theorem (`HTGeometry.exists_norm_weightedPowerSum_ge_scaled`), the Lorentzian zero mass (`lorentzMass_le_log`), the zero count (`exists_N_window_le`).

## 7. Answers and open questions

**The central question.** Does a barrier on partial prime sums give `P(unit window of [V,2V] holds a zero of depth ≥ A/log V) ≤ ε(A)`
with `ε(A) → 0` independent of `V`?

*As an implication from barrier data alone: no.* `barrier_data_does_not_decide_occupancy` gives two fields with the same barrier, one with a zero in
every unit window and one with none. A proof must use something that distinguishes `ζ` from the mimic.

*Through polynomial detectors: not at fixed depth.* `eventually_shiftedDefect_gt_below_threshold` shows that every normalized mollifier of
length `V^θ`, `θ < ½`, misses the detector size `C V/log V` at every depth up to `(1−ε) log log V/(2θ)`.

*What is proved.* Selberg's near-line density gives occupancy proportion `≪ (L/a) e^{−22a/25}`, which tends to zero at depth `≍ log log V`. The prime
camera lowers the threshold constant to `½` for dominant zeros, and bounded clusters and zeros without deep companions obey the corresponding counts.
The question for fixed `A` stays open.

**The residual of the slope law.** Closing the slope is RH, so it is not closed here. Its weakest equivalent forms are in Lean: one window for
all lengths (`riemannHypothesis_iff_unit_window`), one point (`riemannHypothesis_iff_pointwise`), and a uniform positive proportion or any
moment `p > 0` at sparse lengths (`zetaZeroWidth_le_iff_positive_proportion`, `zetaZeroWidth_le_of_frequently_window_moment`). The height
parameter and the prefix integral are not needed for the Möbius mollifier. The compact-window regime is where it lives, and primes are not
independent there.

**Barrier to detector.** No conversion exists at the level of size. Barrier data is purity-blind; restricting to an event lowers no slope
(`eventually_restricted_secondMoment_ge`); and the detector floor comes from primes that the barrier does not touch. At fixed depth this is a theorem for the
standard proxies of barrier events: no short weight lowers the defect (`exists_eventually_weighted_shiftedDefect_ge`).

**The last scale.** The defect of any polynomial mollifier is set by the primes just above it, at rate exactly `2θ` with mass `1/a`. This is
what stops mean values from reaching fixed depth.

**Negative moments.** A long-Möbius energy with logarithmic slope `S` at the central point bounds `Σ_ρ|ρζ′(ρ)|^{−2}` over the simple critical
zeros by `4S`. The residue law at `s = 0` is the corpus theorem of ArithmeticCorrespondencePositivity.

**Clusters.** The camera sorts deep zeros by what competes with them in their window.

| Competitors of a zero at depth `α/L` | Count of separated zeros | Status |
|---|---|---|
| none | `T L α e^{−2α}` | proved (`exists_card_dominant_zeros_le_rate_two`) |
| at most `N` in the sector, small mass outside | `T L e^{−2(1−4c)α}` | proved (`exists_card_clustered_zeros_le`) |
| at most `N` in the sector, small mass deeper than `A/L`, any near-line zeros | `T L e^{A−(1−4c)α}` | proved (`exists_card_zeros_without_deep_companions_le`) |
| comparably deep companions, without limit | `T L e^{−22α/25}` | proved (`exists_selberg_criticalGate_nearLine_zeroDensity`, by the mollifier) |

The conditions in the first column select which zeros are counted; they are not premises about `ζ`. So in any separated family of zeros at depth `α/L`, all but
`≪ T L e^{A−(1−4c)α}` have, at some height of their window, more than `N` zeros in the sector or large mass of zeros deeper than `A/L`.

**Open.**
1. Occupancy at fixed depth: is `ε(A)` independent of `V` true unconditionally? It needs a detector that is not a size statement.
2. Second-moment rate: replace `22/25` by the sharp rate, and with it the threshold constant in `log log V`.
3. A barrier statement for the last scale itself, past the length where `K`-th moments stop (`2Kθ ≤ 1`).
4. The second moment of the Lorentzian mass. A bound `≪ T/c²` at scale `1/δ`, a pair correlation bound, carries the near-line theorem from rate one to rate two. The camera at
   centre `0` bounds a positive kernel, but camera weights of deep zeros there have no sign.
5. Comparably deep pairs: a lower bound for the outside mass at sector distance, or a camera with fast tails, to shrink the condition `ClusterAt`.
6. Condensation: do the zeros of `M_X` condense on `Re s = Θ` (Jentzsch–Szegő)? Only the Hurwitz half is easy.
7. Sharper negative moments: the constant `¼` and the passage from finite sets of simple zeros to multiplicities.

## 8. Traps

| Trap | Truth |
|---|---|
| A barrier gives `D_win` because it gives maxima | That success is an analogy; a zero is not a large value of the field, and the mimic field proves the implication false |
| Size detection reaches `V/log V` | The Fejér–Dirichlet polynomial occupies `≥ V/12` windows with every `L^p` and `log⁺` defect of that size (CDG) |
| Restriction to a good event lowers the slope | It does not: `eventually_restricted_secondMoment_ge` holds for every event of definite Poisson mass |
| Primes are independent at every length | Only below the window; at bounded height a prime block is nearly one rotating phase |
| A longer mollifier removes the defect | Every prime above it has coefficient one; the defect rate is `2θ`, so `θ < ½` is what bounds it |
| The rate of the defect is `2` | That is the rate of primes near `V`. The rate is `2θ`, with factor `1/a`, from the primes just above the mollifier |
| The Cauchy kernel of a zero costs a logarithm across a segment | Only in modulus. Its real part is a Poisson kernel of mass `π` in the height |
| Selberg's CLT needs a mollifier | Not at this strength: the explicit formula and `L¹` shift suffice, since the errors need only be `o(√log log T)` in probability |
| Selberg's formula stops at `Re s = 1` | It holds to `Re s = 3/2`, and starting there avoids any statement about `ζ(1+it)` |
| The Gaussian rate follows from `cosh b ≤ e^{b²/2}` | That loses a factor `2` in the exponent; the true proxy needs `I₀(b) ≤ e^{b²/4}` |
| Proportion results reach `D_win` | The root model has proportion one and every exponential depth rate and fails `D_win` |
| Fixed-window rigidity is unconditional | The Poisson weight depends on `ρ`; fixed-window vanishing of low sets needs a zero attaining the width |
| Formalizing the slope law closes the residual | Closing the slope is RH |
| A short polynomial weight can select heights where the defect is small | It cannot: the block primes copy its whole low-frequency profile to integers where it has no coefficient |
| Density bounds for dominant zeros are density bounds | They count only zeros that dominate; the definition is the content, and clusters are what remains |
| Isolation with `e^{|b'|y}` | A reflected partner would then always block. The weight is signed: `e^{b'y + |b'|δ}`, at most one on the left of the line |
| Turán needs separated nodes | Not with weights in a half plane. Top groups cannot cancel; the loss depends only on the number of nodes and the start |
| Near-line zeros block a deep zero because they are many | The Lorentzian mass has mean `≍ 1/c`, so only rare windows carry mass `≍ e^α` |
| Rate one for near-line blocking is the truth | It is the limit of the first moment; a second moment would give rate two |

## 9. Context

| Programme | Interface |
|---|---|
| CDG (`ConjugateDiagonalGeometry/NearLineLogMean`) | receivers `D_win`, `D_zero`; detector sharpness and the Fejér–Dirichlet obstruction; the Gaussian floor; MZF sharpens the floor from rate `2` to rate `2θ` |
| APR (`ArithmeticProduction`) | necessary-length laws, zero floors, slope law; MZF reduces the slope residual to one window |
| RHTower | Steinhaus model, Selberg near-line density, explicit formula, mean values |
| ArithmeticCorrespondencePositivity | the Mertens energy law, which MZF transfers to the long Möbius polynomial |
| ADO (`ArithmeticDiscreteness`) | small values of `ζ′`, repulsion; the link is `not_forall_moebiusPoly_energy_le` |
| ZCG, FFP | sign-free readers of the same zeros, in heat and Jensen-polynomial coordinates |
| SquareRootThreshold, ZetaUniformTwinRadius | twin radius and cluster detectors from Weil positivity; MZF obtains the unconditional count without positivity |
| HTGeometry | Turán's second main theorem with weights, the input of the cluster camera |

MZF serves WD's density branch as a programme and its RH branch by exact limits. The sign routes (CHT, SWC, FADF) do not enter. Sparse off-line
zeros survive every density statement here, so no theorem in this folder reaches RH.

## 10. Big picture

The field has three zones.

- **Small primes, below the window.** Independent phases. Here probability works in full: Selberg's central limit theorem, the Gaussian tail
  with its sharp exponent, the barrier, the factorization of the gcd form over blocks.
- **The last scale, just above the mollifier.** Coefficients are forced to one, length constraints stop higher moments, and mean values
  control only an `L²` budget with `V/log V` units per cell. Occupancy is decided here, at depth `≍ log log V`.
- **The compact window, `X → ∞` at fixed height.** No independence. The slope law and RH live here, and they are reduced to their weakest
  forms but not decided.

A barrier is a statement about the first zone. The central question and the residual live in the other two. That separation is the main
structural result: the multiscale method is complete where independence holds, and the proofs show exactly why it stops where it stops.

Between the zones sits a prime-only instrument, the camera. It needs neither a mollifier nor independence. It reaches the Density Hypothesis rate for zeros that dominate
their window or sit in bounded clusters with small outside mass, and rate one for all zeros without deep companions. It reorganizes the density branch: the mollified second
moment pays for all zeros at rate `22/25`, and the camera pays at a higher rate for all but the deep clusters. What remains between them is one concrete object, comparably
deep zeros at scale `1/(cL)`.

## 11. Success and contribution criteria

**The programme succeeds if** it answers the central question, in either direction, in Lean, or proves `D_win`, or names by theorem the class of
inputs that cannot reach it. It has so far named two such classes (barrier data, polynomial size detectors below `log log V`); the fixed-depth
question itself is open.

**A contribution must:**
1. be unconditional, with every analytic input proved; an implication from a named law must state that law and whether it is an
   equivalence with RH;
2. state the outcome on the mimic battery: impure factor, root model, Fejér–Dirichlet detector, Liouville twin;
3. name its length regime and compare it with the necessary-length laws;
4. for a limit theorem, name the model at which the tool stops and extract the sharp positive statement;
5. improve a pillar, answer a question of section 7, or add a tool used by another module.
