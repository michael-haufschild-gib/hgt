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
| Pseudo-hyperbolic ratio | `ϱ(ρ, ρ') = |ρ − ρ'|/|ρ + ρ̄' − 1|`, the modulus at `ρ` of the Blaschke factor of `ρ'` in `Re s > ½` |
| Gram form | `G(C) = Σ C_k C̄_l/(λ_k + λ̄_l)`, the energy of `Σ C_k e^{λ_k y}` on `(−∞, 0]`; `λ_ρ = ρ − ½ − it` |
| Lorentzian mass | `Σ_ρ m_ρ/(1 + δ²(γ_ρ − t)²)`, the zeros of `ζ` seen from height `t` at resolution `1/δ` |
| Normalised derivative | `N(ρ) = 2b (|ρ−1|/|ρ|) |ζ′(ρ)| exp(−∫P_ρ log|ζ(½+iu)|du)`; normal size `1` |

## 3. Language

- **Floor, cap.** A floor is a lower bound for a functional of `E` forced by a zero; a cap is an upper bound forced by a zero-free
  region.
- **`L⁰` statement.** A statement about the size of `E` on most points of a window, with no moment. It is the weakest form
  of a size statement and survives restriction to any event.
- **Slope.** The rate `lim log(functional)/log X` in the length.
- **Hole.** A point where `|E| ≥ 1`. Every zero of `F` lies in a hole; a hole need not contain a zero. Holes reach every disc on `Re s = Θ`, for arbitrarily large `X`.
- **Last scale.** The primes just above the mollifier, near `T^{Θ(1)}`, where products exceed `T` and mean values stop.
- **Bohr lift.** The Dirichlet polynomial read as a function on the torus of primes; independence means Haar measure on it.
- **Purity-blind.** A functional of the partial prime sums that takes the same value on a pure field and on a field with off-line zeros.
- **Occupancy threshold.** The depth above which the proportion of occupied unit windows tends to zero.
- **Dominant, isolated, clustered.** Three grades of a zero against its camera window: the field is at least half its term;
  the companions have small weighted mass; at most `N` zeros in the sector and small mass outside.
- **Sector.** The window `|γ − t| δ ≤ 1/10`, on which camera weights have positive real part.
- **Hyperbolically isolated.** `Π_{ρ'} ϱ(ρ, ρ') ≥ B₀` over the zeros deeper than half the depth of `ρ`. Far zeros, much deeper zeros and much shallower zeros have ratio close to `1`.

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

**Q. The Blaschke factor is the exact price of cancellation.** `G(β_j C) = G(C) − 2 Re λ_j |Σ C_k/(λ_k + λ̄_j)|²`, from `(a−μ)(c̄−μ̄) − (a+μ̄)(c̄+μ) = −(a+c̄)(μ+μ̄)`. Removing the other nodes one at a time,
the energy of `Σ C_k e^{λ_k y}` on `[y₀, Y]` is at least `|C_i|² e^{2 Re λ_i Y} Π_{j≠i}|β_j(λ_i)|²/(2 Re λ_i)` minus the energy before `y₀`. No sector, no separation and no count of nodes enter. Height cancels: `|β_j(λ_i)| = ϱ(ρ_i, ρ_j)`.

**R. The energy of the camera over its centres.** Fubini and the mean value theorem give `∫_{y₀}^{Y}∫_T^{2T}|C_y(t)|² dt dy ≪ L T/c²`. The Blaschke bound reads this energy zero by zero: a window of a zero with factor `≥ B₀` costs `e^{2x} B₀²/(α+1)` of it.

**S. Exponential tail of the mass.** Summing the local count on dyadic scales `2^j κ/L`, with the rate of the local count at each, gives `Σ m/(1 + δ²(γ−t)²) > Kκ` only on measure `≪ T e^{−κ/120000} + (L+1) T^{1/2}`. So near-line noise never reaches `e^{(1−ε)x}` except on measure `≪ T e^{−2x}`.

**T. The very deep zeros are rare.** At the low centre `y = 2δ` a zero of depth `b` has weight `e^{3cbL}` times its Lorentzian, and first moment `π/δ`. The weighted window count has `Σ m e^{3cbL}` over the zeros deeper than `v₀` of size `≪ (T/v₀) e^{−v₀L/4800}`. So the low-centre mass of the zeros deeper than `A/(3cL)` is small off a small set, and needs no hypothesis.

**U. Dividing by the Blaschke product.** `F = E/Π β_a` is entire of the growth of `E` with `|F| = |E|` on the line, since `|z + ā − 1| = |z − a|` there. Its value at a simple zero `ρ` of `E` is `2b E′(ρ)/Π_{a≠ρ}β_a(ρ)`. Half-plane Jensen at `ρ` for `F` gives `N(ρ) ≤ Π_a ϱ(ρ, a)`: a normal derivative is hyperbolic isolation.

**V. A mollifier is outer.** `|M(ρ)| ≤ exp ∫P_ρ log|M|`, so a mollifier leaves the ratio of `N` unchanged or lowers it. It enters only when `∫P_ρ log|ζ|` is estimated by a second moment: `|M(ρ)| exp ∫P_ρ log|ζ| ≤ (∫P_ρ|ζM|²)^{1/2}`.

**W. Jentzsch for the Möbius polynomials.** If `M_X` has no zero on a disc crossing `Re s = Θ`, for all large `X`, it has a logarithm `g_X` there. Borel–Carathéodory bounds `g_X` by `≪ log X` from `|M_X| ≤ X` and by `≪ 1` on a small circle right of `Θ`, where `M_X → 1/ζ`. Three circles interpolate to `(log X)^θ`, `θ < 1`, at a point left of `Θ`. So `M_X` is subpower there, and Abel summation gives a zero-free half plane left of `Θ`: a contradiction.

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
| `gramForm_blaschke`, `energy_ge_blaschke` | the contraction identity of the Gram form; the energy on `[y₀, Y]` is bounded below by the Blaschke product of the other nodes | `TheBlaschkeFactorBoundsTheCauchyForm` |
| `exists_card_hyperbolic_zeros_le` | the hyperbolic camera, with noise and exceptional set explicit: `≪ (α+1) T L e^{−2(1−3c)α}/B₀²` | `TheHyperbolicCameraSeesIsolatedZeros` |
| `exists_volume_lorentz_mass_gt_le` | the Lorentzian mass exceeds `Kκ` on measure `≪ T e^{−κ/120000} + (L+1)T^{1/2}` | `TheLorentzianMassHasAnExponentialTail` |
| `exists_card_zeros_compete_only_with_deep` | near-line and far zeros need no hypothesis: only zeros deeper than `A/L` compete | `OnlyComparablyDeepZerosCompete` |
| `exists_volume_very_deep_mass_gt_le` | the low-centre mass of the zeros deeper than `v₀` exceeds `X` on measure `≪ (1/cL)(Σ m e^{3cbL})/X` | `TheVeryDeepZerosAreRare` |
| `exists_card_hyperbolically_isolated_zeros_unconditional_le` | **the hyperbolic density theorem**: separated zeros at depth `[α,α+1]/L`, `x = (1−3c)α`, with `Π ϱ ≥ B₀ ≥ e^{−x/8}` over the zeros deeper than `x/(2L)`, number `≪_c (α+1) T L e^{−2(1−3c)α}/B₀² + L³T^{1/2}` | `TheHyperbolicDensityTheorem` |
| `blaschke_poisson_le` | Poisson–Jensen with a finite Blaschke product, for entire functions of quadratic growth on `Re z ≥ ½` | `TheDerivativeReadsTheBlaschkeFactor` |
| `normalDerivative_le_prod` | `N(ρ) ≤ Π_{a∈D} ϱ(ρ, a)` for every finite set `D` of other zeros in `Re s > ½` | same |
| `exists_card_zeros_with_normal_derivative_le` | zeros with `N(ρ) ≥ B₀ ≥ e^{−x/8}` obey the same count | same |
| `exists_card_zeros_of_negative_moment_le` | a separated family with `Σ N(ρ)^{−2} ≤ J #S` has `#S ≪_c J (α+1) T L e^{−2(1−3c)α} + L³T^{1/2}` | same |
| `exists_card_hyperbolic_zeros_unseparated_le`, `exists_card_zeros_with_normal_derivative_unseparated_le` | the same counts without separation, for `α ≥ 2(1 + 1/c)`: `≪_c (α+1)² T L e^{−2x}/B₀² + (α+1) L³T^{1/2}` | `TheCountNeedsNoSeparation` |
| `exists_zero_moebiusPoly_near` | **Jentzsch half**: every disc around a point of `Re s = ½ + zetaZeroWidth` holds a zero of `M_X` for arbitrarily large `X` | `TheZerosOfTheMollifierCondense` |
| `eventually_moebiusPoly_ne_zero` | **Hurwitz half**: a compact set in `Re s > ½ + zetaZeroWidth` avoiding `s = 1` holds no zero of `M_X` for large `X` | same |
| `exists_mollified_error_eq_neg_one_near` | every disc on the abscissa has `ζM_X − 1 = −1` at some point, for arbitrarily large `X` | same |
| `zetaZeroWidth_le_iff_moebiusPoly_zero_free`, `riemannHypothesis_iff_moebiusPoly_zero_free` | the zeros of `M_X` read the width; RH iff they do not accumulate in `Re s > ½` away from `s = 1` | same |
| `exists_card_zeros_with_normal_mollified_derivative_le` | the same count for `2b(|ρ−1|/|ρ|)|ζ′(ρ)M(ρ)| ≥ B₀(∫P_ρ|ζM|²)^{1/2}`, `M` the Möbius polynomial of any length | same |

## 6. Tools

**Developed here.** Half-plane Jensen with prefix amplification; the exponent-rigidity calculus (Poisson mass of low sets); Steinhaus
moment transfer; the Taylor comparison of characteristic functions on heights; Slutsky on a window (`tendsto_windowLaw_of_close`); the
window law `windowLaw`; the sharp phase moment generating function; the Gaussian tail on heights; the doubly exponential scale grid; the
explicit formula up to `Re s = 3/2` (`exists_selberg_explicit_formula_wide`); `log_norm`-increments along horizontal segments; the
Tonelli cost of one zero (`integrable_and_integral_kernel_le`); the polynomial-difference energy (`sum_polyDiffCoeff_sq_le`); the gcd
form and block convolution; the scaling trick that frees the high-block bound from bounded main terms; the last-scale block; the Gaussian floor at
any positive energy (`gaussFloor_of_pos`, `gaussFloor_of_norm_le`); the twisted first moment against a polynomial
(`norm_integral_zeta_poly_conj_sub_le`); the mean value theorem from below (`integral_normSq_edPoly_ge`); the prime camera at all widths and
centres; the sector of the window (`re_paperFT_profile_ge`); the first moment of the Lorentzian mass (`integral_windowMass_le`); the Blaschke contraction of the Gram form
and the energy bound it gives (`gramForm_blaschke`, `energy_ge_blaschke`); the exponential tail of the Lorentzian mass; the exponential moment of the depth over three windows
(`exists_sum_very_deep_le`); division by a finite Blaschke product with Poisson–Jensen (`exists_blaschke_quotient`, `blaschke_poisson_le`).

**Used from the corpus.** Boundary Jensen on the disc (`circleIntegrable_and_sum_log_add_le_circleAverage`), Littlewood's Mertens bound
(`mobiusMertens_subpower_of_zeroFree`), the Möbius field, the Steinhaus model, the symmetrised partial fraction of `ξ'/ξ`
(`two_logDeriv_xi_eq_pair_tsum`), the weighted zero density (`exists_tsum_weighted_density_le`), Selberg's explicit formula
(`norm_logDeriv_zeta_add_selberg_le`), the exclusion windows (`exists_sum_selbergRightWindow_le`), the mean value theorem
(`integral_normSq_edPoly_displaced_le`), the sharp Mertens theorem, the Gaussian floor (`gaussFloor_general_at_scale`), the high-block
bound (`exists_highBlock_bound_of_mainTerm_upper`), the near-line density (`exists_selberg_criticalGate_nearLine_zeroDensity`), the
Mertens energy law (`not_forall_mertens_pronicEnergy_le_log`), the explicit formula of `ζ` (`Zeta23.WeilEF.EF_lit_zetaZeroConfig`), the weighted Turán
theorem (`HTGeometry.exists_norm_weightedPowerSum_ge_scaled`), the Lorentzian zero mass (`lorentzMass_le_log`), the zero count (`exists_N_window_le`), the typical local count
(`RHTower.ZetaTypicalLocalZeroCount`), the weighted window count (`exists_windowZeros_weighted_le`).

## 7. Answers and open questions

**The central question.** Does a barrier on partial prime sums give `P(unit window of [V,2V] holds a zero of depth ≥ A/log V) ≤ ε(A)`
with `ε(A) → 0` independent of `V`?

*As an implication from barrier data alone: no.* `barrier_data_does_not_decide_occupancy` gives two fields with the same barrier, one with a zero in
every unit window and one with none. A proof must use something that distinguishes `ζ` from the mimic.

*Through polynomial detectors: not at fixed depth.* `eventually_shiftedDefect_gt_below_threshold` shows that every normalized mollifier of
length `V^θ`, `θ < ½`, misses the detector size `C V/log V` at every depth up to `(1−ε) log log V/(2θ)`.

*What is proved.* Selberg's near-line density gives occupancy proportion `≪ (L/a) e^{−22a/25}`, which tends to zero at depth `≍ log log V`. The prime
camera lowers the threshold constant to `½` for hyperbolically isolated zeros, and the hyperbolic density theorem gives the count `≪ (α+1) T L e^{−2(1−3c)α}/B₀²`.
At fixed `A` a count `≪ T L e^{−rA}` still allows every unit window to be occupied, so density alone cannot decide `ε(A)`: a positive answer needs the deep zeros to sit in few windows, or a saving of the factor `L`. The question for fixed `A` stays open.

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
zeros by `4S`. The residue law at `s = 0` is the corpus theorem of ArithmeticCorrespondencePositivity. Off the line the negative second moment of the normalised derivative is what the Density Hypothesis rate costs:
a family of separated zeros at depth `α/L` with mean `N^{−2}` at most `J` has size `≪ J (α+1) T L e^{−2(1−3c)α}`, and the mollified field reads the same quantity (`exists_card_zeros_of_negative_moment_le`, `exists_card_zeros_with_normal_mollified_derivative_le`).

**Clusters.** The camera sorts deep zeros by what competes with them in their window.

| Competitors of a zero at depth `α/L` | Count of separated zeros | Status |
|---|---|---|
| none | `T L α e^{−2α}` | proved (`exists_card_dominant_zeros_le_rate_two`) |
| at most `N` in the sector, small mass outside | `T L e^{−2(1−4c)α}` | proved (`exists_card_clustered_zeros_le`) |
| at most `N` in the sector, small mass deeper than `A/L`, any near-line zeros | `T L e^{A−(1−4c)α}` | proved (`exists_card_zeros_without_deep_companions_le`) |
| zeros deeper than `x/(2L)` with `Π ϱ ≥ B₀ ≥ e^{−x/8}`, `x = (1−3c)α` | `(α+1) T L e^{−2x}/B₀²` | proved (`exists_card_hyperbolically_isolated_zeros_unconditional_le`) |
| any, at a zero with `N(ρ) ≥ B₀ ≥ e^{−x/8}` | `(α+1) T L e^{−2x}/B₀²` | proved (`exists_card_zeros_with_normal_derivative_le`) |
| comparably deep companions, without limit | `T L e^{−22α/25}` | proved (`exists_selberg_criticalGate_nearLine_zeroDensity`, by the mollifier) |

The conditions in the first column select which zeros are counted; they are not premises about `ζ`. So in any separated family of zeros at depth `α/L`, all but
`≪ (α+1) T L e^{−(7/4)x}` have Blaschke product below `e^{−x/8}` over the zeros at least half as deep: a zero at the Density Hypothesis rate is only blocked by comparably deep zeros of total Green potential `Σ log 1/ϱ ≥ x/8`, equivalently only at an abnormally small normalised derivative.

**Condensation.** The zeros of `M_X` condense on `Re s = Θ`, `Θ = ½ + zetaZeroWidth`: they accumulate at every point of that line along a sequence of lengths depending on the point, and nowhere in `Re s > Θ` except at `s = 1`. So the mollifier fails on the abscissa: every disc there has `ζM_X − 1 = −1` at some point, for arbitrarily large `X`, whether `ζ` vanishes in the disc or not. This is one more RH equivalent, and it is not a door: it decides nothing about `Θ`.

**Open.**
1. Occupancy at fixed depth: is `ε(A)` independent of `V` true unconditionally? It needs a detector that is not a size statement.
2. Second-moment rate: replace `22/25` by the sharp rate, and with it the threshold constant in `log log V`.
3. A barrier statement for the last scale itself, past the length where `K`-th moments stop (`2Kθ ≤ 1`).
4. Negative moments off the line: a bound for `Σ N(ρ)^{−2}` over the zeros at depth `α/L`, even in the range `J ≤ e^{x/4}`. Second moment and Jensen control the numerator of `N`; the derivative in the denominator is the input missing.
5. Comparably deep clusters: the Green potential of zeros at hyperbolic distance `O(1)`. Inside the camera sector positive weights should merge nearly coincident zeros (mechanism O), which could replace the factor `ϱ` of very close pairs.
6. Equidistribution: is the height distribution of the zeros of `M_X` near `Re s = Θ` regular (Szegő, Erdős–Turán)? Does the accumulation hold along all lengths rather than a sequence depending on the point?
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
| Rate one for near-line blocking is the truth | It is the limit of the Markov bound on the first moment; the exponential tail of the mass gives rate two |
| Cauchy forms need separated nodes | The Blaschke product is the exact price of cancellation; it needs no separation and is close to `1` for far, much deeper and much shallower zeros |
| A longer mollifier raises the Blaschke bound | A mollifier is outer: it leaves `N(ρ)` alone and enters only through the second moment that estimates `∫P_ρ log|ζ|` |
| A zero of `M_X` is a zero of `ζM_X` that the mollifier controls | At a zero of `M_X` the error equals `−1`; these zeros condense on the abscissa, so mollification fails there for arbitrarily large `X` |
| `T L e^{−2A}` at fixed `A` answers occupancy | It exceeds `T`, so it allows every unit window to be occupied; density alone cannot decide `ε(A)` |

## 9. Context

| Programme | Interface |
|---|---|
| CDG (`ConjugateDiagonalGeometry/NearLineLogMean`) | receivers `D_win`, `D_zero`; detector sharpness and the Fejér–Dirichlet obstruction; the Gaussian floor; MZF sharpens the floor from rate `2` to rate `2θ` |
| APR (`ArithmeticProduction`) | necessary-length laws, zero floors, slope law; MZF reduces the slope residual to one window |
| RHTower | Steinhaus model, Selberg near-line density, explicit formula, mean values |
| ArithmeticCorrespondencePositivity | the Mertens energy law, which MZF transfers to the long Möbius polynomial |
| ADO (`ArithmeticDiscreteness`) | small values of `ζ′`, repulsion; the links are `not_forall_moebiusPoly_energy_le` and `normalDerivative_le_prod`: `|ζ′(ρ)|` small is where a Blaschke product can be small |
| ZCG, FFP | sign-free readers of the same zeros, in heat and Jensen-polynomial coordinates |
| SquareRootThreshold, ZetaUniformTwinRadius | twin radius and cluster detectors from Weil positivity; MZF obtains the unconditional count without positivity |
| HTGeometry | Turán's second main theorem with weights, the input of the cluster camera; the half-plane Poisson kernel |
| RHTower near-line density and zero counts | the local count behind the exponential tail, and the weighted window count behind the very deep zeros |

MZF serves WD's density branch as a programme and its RH branch by exact limits. The sign routes (CHT, SWC, FADF) do not enter. Sparse off-line
zeros survive every density statement here, so no theorem in this folder reaches RH.

## 10. Big picture

The field has three zones.

- **Small primes, below the window.** Independent phases. Here probability works in full: Selberg's central limit theorem, the Gaussian tail
  with its sharp exponent, the barrier, the factorization of the gcd form over blocks.
- **The last scale, just above the mollifier.** Coefficients are forced to one, length constraints stop higher moments, and mean values
  control only an `L²` budget with `V/log V` units per cell. Occupancy is decided here, at depth `≍ log log V`.
- **The compact window, `X → ∞` at fixed height.** No independence. The slope law and RH live here, and they are reduced to their weakest
  forms but not decided. The zeros of `M_X` mark the abscissa here: they condense on `Re s = Θ`.

A barrier is a statement about the first zone. The central question and the residual live in the other two. That separation is the main
structural result: the multiscale method is complete where independence holds, and the proofs show exactly why it stops where it stops.

Between the zones sits a prime-only instrument, the camera. It needs neither a mollifier nor independence. Read through the Hardy geometry of `Re s > ½` it reaches the Density
Hypothesis rate for every hyperbolically isolated zero: near-line, far and much deeper zeros are not competitors at all. Its reading of a zero is the Blaschke factor, and that
factor is bounded below by the normalised derivative `N(ρ)`. It reorganizes the density branch: the mollified second moment pays for all zeros at rate `22/25`, and the camera pays
at rate `2(1−3c)` for all but the zeros with a large Green potential from comparably deep zeros, equivalently with an abnormally small `N(ρ)`. What remains between them is one concrete
object, and it is the same one on both sides: the negative moments of `ζ′` at the zeros.

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
