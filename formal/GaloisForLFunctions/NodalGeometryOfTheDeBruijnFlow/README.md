# Nodal Geometry of the de Bruijn Flow (NGF)

Namespace `GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow`; umbrella
`NodalGeometryOfTheDeBruijnFlow.lean`. Labels: **[L]** proved in Lean, without added hypotheses or axioms; **[D]** derived on paper,
not a theorem here; **[O]** open.

## 1. Motivation

Let `H_t(z) = ∫ Φ(x) e^{tx²} e^{izx} dx` (`RHTower.DeBruijn.riemannHeat`). It solves `∂_t H = −∂_z² H`, so `u(x, t) = H_t(x)` is a caloric function and
*decreasing* `t` is forward parabolic time. RH says that the nodal curves `{u = 0}` in the half-plane `t > 0` have no turning points. A collision is a point where `u` vanishes to parabolic
order two or more, with local model `x² − 2(t − t₀)`.

Every bound on the half-Gaussian source of route ZCG is a size bound, and size stops at the saddle `½/log X`: lowering the coefficient by size needs Lindelöf-strength input, and below a fixed coefficient it forces a
zero-free strip. NGF supplies the tools below the saddle that do not rest on size. They read the flow as a parabolic object: monotone quantities, zero numbers, blow-up profiles and zero dynamics.

NGF is a programme of route ZCG, not a new field, and it does not exclude a collision by itself. Its identities hold for every caloric function. Arithmetic enters only through data: the proved region above the horizon, the count of zeros, and the zero-free boxes at typical heights.

## 2. Objects

| Object | Meaning |
|---|---|
| Nodal set | `{(x, t) : t > 0, H_t(x) = 0}`; below the horizon it is a forest opening upward in `t` |
| Collision | a real multiple zero of `H_{t₀}` |
| Caloric transform | `caloric g t z = ∫ g(y) e^{ty²} e^{izy} dy`, `g` of super-Gaussian decay; `g = Φ` gives `H_t` at every real `t` |
| Fock energy | `F(σ) = Σ_n (2σ)ⁿ/n! ‖∂ⁿu(z₀, t₀)‖²`, equal to the Gaussian line energy of `u` at time `t₀ + σ` |
| Frequency | `N(σ) = σ D(σ)/F(σ)`, half the mean Taylor degree of the Fock measure |
| Zero number | real zeros with multiplicity in a buffered window; collision mass `2⌊k/2⌋` at order `k` |
| Velocity | `V = H″/H′` at a simple zero |
| Gap, mesh, spread | `g = x' − x` of a pair; the least gap of a packet; `P = Σ_{i<j}(x_j − x_i)²` of a cluster |
| Compression | `S = Σ_b m_b/((x' − b)(x − b))`, the force of the other zeros on a pair |
| Depth energies | `E₁, E₂ = Σ w(Re z − X)(Im z)^{2p}`, the localized moments of the depth |
| Nonreal time | the measure of heats at which `H_s` has a nonreal zero in a window |
| Zero potential, energy | `R₁(z) = Σ m_a/|z − a|`, `R₂(z) = Σ m_a/|z − a|²` over a packet |
| Amplitude | `P = |ξ(½ + 2tα + iX)| e^{−tα²}`, `α = ½ log(X/2π)`: the size of the flow where it is one exponential |

## 3. Language

- **Saddle, horizon**: `½/log X`, where the Gaussian mass of `H_t` leaves the strip; `(6600/9991 + ε)/log(X/2π)`, above which `H_t` is proved real and simple near `X`.
- **Buffered window**: a window whose moving boundary curves carry no zero of `H_t` for the times considered.
- **Parabolic cylinder**: a window of heights `[A, B]` times an interval of heat times; its parabolic boundary is the initial time and the lateral layers.
- **Crystal, mesh time**: a lattice of spacing `g`; the time scale `t ≍ g²`, that is `τ = t log²X` for spacing `≍ 1/log X`.
- **Crowd**: too many zeros close to a point, measured by `R₂` or `R₁`.
- **Blind law**: an identity or monotonicity that also holds for `H_{t−τ}`.

## 4. Mechanisms

1. **The Gaussian energy is a Fock norm.** Fubini and the Gaussian transform give the expansion of `F(σ)` in Taylor data, at every complex `z₀`. Frequency monotonicity (Almgren–Poon) then is the fact that tilting an exponential family raises its mean.
   The order `k` of a zero is at most `2N(σ)`. Convexity gives `F(rσ) ≥ r^{2N(σ)} F(σ)`.
2. **Zero number.** As `t` decreases, the zero number of a buffered window falls only at collisions, by `2⌊k/2⌋`. At a zero of order `k` there are `k` real zeros just above `t₀` and `k mod 2` just below, so the nodal set is a forest without caps.
3. **Blow-up.** `H_{t₀ ± q²}(x₀ + qσ)/q^k` tends to the heat polynomial of degree `k`. The gaps of the profile satisfy `μ² ≤ 24/(k + 1)`.
4. **The gap law.** `g(V(x') − V(x)) = 4 − 2g²S + 2g(Q(x') − Q(x))`. A zero outside the Jensen disc of the pair compresses it, so `g²` opens no faster than `8t`.
5. **The mesh pair.** At a mesh pair the other zeros are at least lattice-spaced, so `g²S ≤ 2 − 1/(R + 1) − 1/(L + 1)`, with equality on a lattice. So the squared gap opens at rate at least `16/n`, up to `O(g² log X)`. Only the `n` zeros within `ρ` of the pair count; the others enter through their energy `E`.
6. **The first touch.** The first pair to reach a barrier is a mesh pair of the packet around it. This gives a maximum principle for gaps in real cylinders, with a rate `≍ 1/log X` in general and `8/n` away from crowds.
7. **The cluster law.** The singular forces inside a cluster cancel in pairs: `dP/dt = 2n²(n − 1) + O(log X/ρ² · P)`, without any separation inside the cluster.
8. **The two quadratures.** Above the horizon, and at typical heights above any positive coefficient, `H_t = 2 Re Q`, `H_t′ = −2 Im Q′`, `Q′ ≈ aQ`. So `H_t` and `H_t′/α` are the two quadratures of the amplitude. At a zero the whole amplitude is in the derivative, and Cauchy's estimate on discs of radius `1/α` spaces the zeros.
9. **The frequency at the horizon.** Read at the time of the horizon, the frequency is `≈ σα²`. A wave cannot hide its energy in the derivative: too large a frequency contradicts the exact growth `e^{(r−1)2σα²}` of the amplitude, by convexity.
10. **The reverse saddle.** The representation of `H_{t₀}` by `H_{t₀+t}` around a saddle sees the zeros only through the field `V` and the energy `R₂`. So persistence is decided by the crowd.
11. **Depth moments.** The zeros attract vertically, so the depth energies dissipate, and cutoffs cost only `O(log X) E_p`, with no inverse gap. A conjugate pair loses a fixed amount of `E₁`, so `(E₁, E₂)` bounds the heat time spent nonreal.
12. **The crystal.** The linearized Dyson flow on a lattice has the exact symbol `ξ(2π − ξ)/g²`: mesh time for the pair mode, the Poisson semigroup at height `t log X` at long wavelength.
13. **The Hermite pinch.** The roots of `He_k` are stationary for the Dyson flow in self-similar variables (the Stieltjes relation), so the mesh-pair rate pins their least gap: `16/k ≤ μ² ≤ 24/(k + 1)` for the profile, with equality at `k = 2`.
14. **The Poisson sum.** `2 Re ξ′/ξ(½ + r + iY) = Σ_ρ P(r, a, u)`, `P = 2r v/(v² + e²)`, `v = r² − a² + u²`, `e = 2|au|`. If the zeros of depth above `R₀` keep away from `Y`, `|u| > 4|a|`, then for `r ≥ 2R₀` one has `P ≥ 0` and `P/r` decreasing: the slope at one scale bounds all larger scales, and `|ξ|` at depth `r` dominates the whole strip below it, zeros included. No size bound for `ζ` enters and no power of `log T` is lost.
15. **The critical scale.** The transform at the saddle `u` is decided by the slope on `[u/3, 5u/4]`, with errors `B√τ` and `e^{−uβ/40}`. Selberg's typical bound at dyadic scales `R_j`, with `B_j R_j = q (5/4)^j`, has summable exceptional measures and `B_j²τ ≪ 1/q²` at `τ ≍ R_j/log T`.
16. **The rotation.** At a fixed saddle, `Q_{x+s}(0) = ρ e^{ias} + r(s)` with `‖r‖` small against `|ρ| e^{−πs/4}`. At a zero `Re ρ ≈ 0`, so `H_t(x + s)` has the sign of `∓ sin αs`, and the next zero sits at `αs ≈ π`.
17. **Finite speed.** Iterating the `E₁` law over nested blocks is a discrete parabolic estimate: energy and nonreal time at time `b` are a Poisson average, with parameter `w = Λ log X (b − a)`, of the energies at time `a`, up to `w^{J+1}/(J + 1)!`.

## 5. Pillar theorems

Corpus inputs: `exists_volume_not_zetaLogDerivScaleData_le_uniform_level` (Selberg's typical slope at the critical scale), `exists_volume_zetaZeroShadowScaled_le` (zeros of all depths at once), `two_mul_re_logDeriv_xi_eq_tsum_pair` (pair sum), `riemannHeat_zeros_real_simple_subWeyl` (horizon), `exists_uniform_riemannHeat_exterior_force` (packet and exterior field), `exists_riemannHeat_shrinking_window_bounds` (zero-free discs), `norm_halfGauss_sub_main_le_of_typical` (typical heights), `spread_roots_heatFlow`, `meshGe_heatStep` (polynomials), `ffConv_root_im_le` (Walsh).

| Theorem | Lean | Module |
|---|---|---|
| Fock identity | `hasSum_fock` | `TheGaussianEnergyIsAFockNorm` |
| Frequency monotone; order ≤ 2N; limit at scale 0; doubling | `frequency_le_frequency`, `order_le_two_mul_frequency`, `tendsto_frequency`, `pow_mul_lineEnergy_le` | `TheFrequencyIsAChaosLevel` |
| Sturm drop law in moving buffered windows; no caps | `BufferedWindow.realZeroCount_eq_add_sum_windowCollisionMass`, `no_real_zero_near_backward_of_even` | `TheZeroNumberDropsOnlyAtCollisions` |
| Hermite blow-up at actual collisions; gap law at order 2; Hermite gap bound | `blowup_forward`, `blowup_backward`, `order_two_gap_law`, `exists_close_zeros_forward` | `CollisionsBlowUpToHermiteProfiles` |
| Velocity law; exact local gap law; integrated law from a collision | `hasDerivAt_zero_path`, `gap_rate_eq`, `exists_gap_sq_le_of_collision` | `TheGapLawOfAdjacentZeros` |
| Mesh growth under the Dyson flow | `sum_inv_mul_le_of_sep`, `mesh_sq_growth` | `TheDysonFlowKeepsTheMesh` |
| Rate at the mesh pair of a packet; with a local count | `mesh_pair_rate_ge`, `exists_mesh_pair_opens`, `local_pair_rate_ge` | `TheMeshPairOfAPacketOpens` |
| Localized averaged law | `cluster_rate_le`, `exists_cluster_spread_law`, `exists_cluster_spread_of_collision` | `TheClusterSpreadsAtTheExactRate` |
| First touch; maximum principle for gaps; away from crowds | `gap_barrier_of_rate`, `exists_gap_maximum_principle`, `exists_gap_maximum_principle_of_count` | `TheGapsObeyAMaximumPrinciple` |
| Uniform mesh above a real time; above `Λ` | `exists_uniform_mesh`, `exists_uniform_mesh_above_newman` | `AboveTheRealTimeTheMeshIsUniform` |
| Central inequality ⇒ no collision, RH, bounded multiplicity | `deriv_ne_zero_of_centralInequality`, `riemannHypothesis_of_centralInequality`, `mult_add_one_le_of_centralInequality` | `TheCentralInequalityIsStrongerThanRH` |
| Central inequality above the horizon | `exists_gap_ge_above_horizon`, `exists_central_inequality_above_horizon` | `AboveTheHorizonTheZerosAreSpaced` |
| Central inequality on density-one heights, down to every `κ > 0` | `eventually_gap_ge_of_typicalWindow`, `exists_densityOne_central_inequality` | `TheCentralInequalityOnAlmostAllHeights` |
| Half-Gauss estimates, amplitude comparisons | `exists_halfGauss_estimates`, `exists_quadrature_bounds`, `horizonAmp_height_le`, `horizonAmp_time_le` | `TheHalfGaussAboveTheHorizon` |
| Order bound from the horizon | `exists_order_le_at_horizon`, `exists_order_le_of_time`, `exists_mult_le_log` | `TheOrderOfACollisionAtTheHorizon` |
| Depth law of polynomials, sharp | `im_sq_lt_of_forward_real`, `exists_root_depth_eq` | `TheDepthLawOfPolynomials` |
| Depth law with its crowd | `exists_zero_near_of_no_crowd`, `exists_zero_near_of_potential`, `exists_zero_near_of_normal_density` | `TheDepthLawSeesOnlyTheCrowd` |
| Dissipation of `E₂` through collisions | `exists_uniform_heatLocalizedQuarticEnergy_evolution` | `TheDepthMomentsAreDissipated` |
| Nonreal time on windows; Selberg's fourth moment of the depths; rarity | `exists_sum_nonrealTime_le`, `exists_sum_mult_im_pow_four_le`, `exists_card_nonrealTime_gt_le` | `NonrealTimeOnWindows`, `TheFourthMomentOfTheDepths`, `NonrealTimeIsRareOnAlmostAllWindows` |
| Symbol of the crystal | `hasSum_one_sub_cos_div_sq`, `lattice_eigen` | `TheCrystalRelaxesAtTheMeshTime` |
| The shifted fake | `shiftKernel_superGaussian`, `caloric_shiftKernel`, `order_le_two_mul_frequency_shift`, `exists_deep_zero_shift` | `TheLocalToolsAreBlindToTheInitialTime` |
| Hermite mesh pinched; local law at a collision | `dysonVelocity_hermite`, `sq_sub_ge_profileRoots`, `exists_gap_ge_near_collision` | `TheHermiteMeshIsPinched` |
| Isolated pair at rate 8; a pair can close off the mesh | `sum_inv_mul_le_of_mesh`, `isolated_pair_rate_ge`, `isolated_pair_rate_le`, `exists_pair_closes` | `TheDysonFlowKeepsTheMesh`, `TheCompressionAwayFromTheMesh` |
| Energy at finite speed; lateral control of nonreal zeros | `nest_poisson_le`, `exists_energy_propagates_at_finite_speed`, `exists_nonreal_entry_le` | `NonrealZerosEnterAtFiniteSpeed` |
| Central inequality and `Λ_X` with an explicit rate, unit windows | `typical_envelopes_small`, `exists_central_inequality_at_power_of_log`, `exists_volume_localNewman_gt_power_of_log_le` | `TheEnvelopesAtAPowerOfTheLogarithm`, `TheCentralInequalityAtAPowerOfTheLogarithm` |
| Poisson comparison; growth; lower strip | `re_logDeriv_mul_le`, `norm_xiLine_le_growth`, `norm_xiLine_le_of_keeping` | `TheSlopeOfXiIsAPoissonSum` |
| Half-Gauss transform from its source | `top_exponent_le`, `source_core`, `halfGauss_estimates_of_source` | `TheHalfGaussAtTheCriticalScale` |
| Gap from quadrature data; central inequality at the critical scale | `gap_ge_of_quadrature_data`, `exists_volume_not_criticalGood_le`, `exists_central_inequality_at_critical_scale` | `TheCentralInequalityOnAlmostAllHeights`, `TheCentralInequalityAtTheCriticalScale` |
| Reality at the critical scale | `riemannHeat_ne_zero_of_critical`, `exists_zeros_real_at_critical_scale` | `TheZerosAreRealAtTheCriticalScale` |
| The crystal law | `quadrature_model`, `exists_next_zero_of_data`, `exists_crystal_law` | `TheCrystalIsFormedAtTheCriticalScale` |

## 6. Questions and their status

**The central question.** Is there `c > 0` with `g_t² ≥ c min(t, log⁻²X)` for all adjacent real zeros near `X` and all `t > 0`?
- It implies no positive-time collision, hence RH, and also `c(m + 1) ≤ 24` for every zero of order `m` of `H₀`. So it is strictly stronger than RH. [L]
- It holds with an absolute `c` in the zone `6600/9991 + ε ≤ t log(x/2π)`, `t log x ≤ 1`. [L]
- It holds with an absolute `c` on one set of heights of density one, for `κ ≤ t log(x/2π) ≤ 1`, for every `κ > 0`. [L]
- On unit windows it holds with an explicit rate: for `17η_T ≤ t log(x/2π) ≤ 1`, `η_T = (1 + log 4T)^{−1/5}`, outside a set of `X ∈ [T, 2T]` of measure `≪ T η_T¹⁴`. [L]
- It holds with an absolute `c` down to the critical scale, in short windows: for every `δ > 0` there is `κ` such that outside measure `δT`, for `|x − X| ≤ κ/(2 log T)` and `7κ/log T ≤ t log(x/2π) ≤ 1/8`. That is `τ = t log²X ≳ κ`. [L]
- For `τ ≲ κ(δ)` it is open, on density-one heights and for each height. [O] Uniformly in `X` it is stronger than RH, and under GUE statistics clusters of growing size are expected, so the uniform form is expected to fail. [D]

**(b1) The local repulsion law.** In a real cylinder `g²` follows the barrier `m₀ + r(s − a)`, `r ≍ 1/log B`, up to `≍ log⁻²B` (maximum principle) [L]. Above a real time `a`, `g_t² ≥ min(c a (t − a), c a², g₁)`, for `t ≤ 5a/4`, with `g₁` from a bounded range of heights [L]. So near the real time the law is `g² ≳ (t − a)/log X`, with the factor `1/log X` that a cluster of `≍ log X` zeros would saturate. An isolated pair has `g² = 8(t − t₀)` up to the factor `e^{±λ(t−t₀)}`, the case `n = 2` of the cluster law [L]. Away from crowds the factor disappears: if at most `n` zeros lie within `ρ` of each zero of the cylinder and the others have energy at most `E`, the barrier rises at rate `8/n` up to the level `1/(n(2E + C log B))` [L]. At normal density `E ≍ log²X/n` [D], and this is `g² ≳ min((t − a)/n, log⁻²X)`, the form of the central inequality with a local constant. So inside a real cylinder the central inequality can fail only through a crowd or through the parabolic boundary. At a real zero of order `k`, all pairs near it satisfy `g² ≥ (16/k − ε)(t − t₀)` just above `t₀`, and some pair has `g² ≤ (24/(k + 1) + ε)(t − t₀)` [L]. On almost all heights the crystal law holds at `τ ≳ κ` [L]. Below that scale, whether the count and the energy stay normal in the cylinder is open. [O]

**(b2) The depth law.** A zero `z` of `H_{t₀}` keeps a zero of `H_{t₀+t}` within distance `d`, as soon as `t|V| ≤ cd`, `t R₂(z) ≤ c`, `t log X ≤ cd` [L]. It suffices that `t(R₁(z) + log X) ≤ cd` [L]. At normal density, `N(r) ≤ A r log X` for `r ≥ d`, this reads `t A log X log(72/d) ≤ cd` [L]: linear in the depth, up to the logarithm. The worst case `R₁ ≪ log X/d` recovers `t log X ≤ c d²`. For clusters the quadratic law is the truth: if `e^{−tD²}q` is real-rooted, a polynomial `q` of degree `n` has `(Im z)² < 8nt`, with sharp constant at the Hermite cluster [L]. So the crowd decides between the two laws. The upper side of the linear law holds at typical heights: for every `δ > 0` there is `κ` such that outside measure `δT`, every zero of `H_t` with `|Re z − X| ≤ κ/(2 log T)` is real once `t log(Re z/2π) ≥ 7κ/log T`, that is `t ≲ d/log X` with `d = κ/log T` the largest depth near `X` [L]. Whether a crowd can stand at a deep zero of `ζ` at the time it would be needed is open. [O]

**(b3) Compression on clusters.** At the mesh pair `g²S ≤ 2 − 1/(R + 1) − 1/(L + 1)`, sharp on lattices [L]. For an isolated cluster as a whole, `dP/dt` equals the exact Hermite rate `2n²(n − 1)` up to `O(log X/ρ² · P)` [L]. If the near zeros are `μ`-separated from the pair and from each other, then `g²S ≤ 4(g/μ)²` whatever their number, so the rate lies in `[8 − 16(g/μ)² − 4(2E + K)g², 8 + 4Kg²]` [L]. Without the separation no sign holds: a pair next to a clump of `13` points closes under the Dyson flow [L]. So the mesh pair and the isolated pair are the cases where a sign is forced; a clump near a non-mesh pair is the exact obstruction, and whether it occurs for the actual source is open. [O]

**Orders.** A real zero of order `k` of `H_{t₀}` at height `X` has `k ≤ (1 + δ)(6600/9991 + ε − τ) ½log(X/2π) + K`, with `τ = t₀ log(X/2π)`. At `t₀ = 0` this is `k ≤ (3300/9991 + ε) log X`, about `0.33 log X`. [L]

**B73.** `Λ_X log X → 0` on one set of density one is proved in ZCG (`exists_densityOne_localNewman_scaled_tendsto_zero`) [L]. The depth moments give the complementary time-measure form with a rate: at most `C_ε U/log U` of the windows of `[U, 2U]` spend heat time more than `ε/log U` nonreal [L]. The density-one central inequality gives a mechanism that sees the gaps [L]. With a rate: `Λ_X log X ≤ 32 η_T` outside measure `≪ T η_T¹⁴` [L].

**Relaxation.** The symbol of the crystal fixes the scales [L]. On almost all heights the relaxation is complete at the critical scale: for all `δ, ε > 0` there is `κ` such that outside measure `δT`, the zero after a zero `x` with `|x − X| ≤ κ/(2 log T)` and `7κ/log T ≤ t log(x/2π) ≤ 1/8` satisfies `|(x′ − x) ½ log(x/2π) − π| ≤ ε` [L]. So the spacing is the mean spacing `2π/log(x/2π)`, with relative error tending to zero as `τ → ∞`. The passage from the local statistics at `τ ≲ 1` to the crystal at `τ ≍ κ` is open. [O]

## 7. Tools

Parabolic frequency, doubling and convexity; Sturm drop law with moving buffers; blow-up to heat polynomials; local Dyson law with an `O(log X)` exterior field; first-touch comparison over packets; the cluster spread law; half-Gauss quadratures at the horizon and at typical heights; the reverse saddle with exact zero energy; depth moments; the Walsh depth bound for polynomials; the crystal symbol; Poisson comparison and the lower strip for `ξ`; the half-Gauss transform from its source; the rotation at a fixed saddle; the Poisson bound for nested energies.

## 8. Traps

- **Blindness.** The Fock identity, the frequency and the order law hold for `H_{t−τ}`, whose kernel `Φ e^{−τx²}` has the same decay; yet that flow has nonreal zeros of unbounded depth for `t < τ`. A sign needs data that distinguishes `Φ` among the `Φ e^{−τx²}`.
- **Degeneration at `t = 0`.** Any repulsion inequality must degenerate exactly there: the zeros of `H_{−τ}` are not real.
- **The central inequality is too strong as stated.** It bounds multiplicities, so it cannot follow from RH alone.
- **The pair and cluster models.** The pair model `(z² + δ²) cos(Lz/2)` has the linear law, the cluster model has the quadratic one, and each obeys the functional equation and the size bounds (`pairModelHeat_orderTwo_collision`, `AClusterHidesAnOffLineZeroFromHeat`). No method blind to the local count can decide between them.
- **Dimension count.** Collisions are generic in the `(X, t)` plane, so Diophantine repulsion alone cannot exclude them. [D]
- **Unbuffered windows.** Zeros cross fixed lines, and nonreal counts in fixed windows can rise.
- **Frequency is three circles.** `F` is also a Bargmann–Fock area norm of `u(·, t₀)`, so the frequency adds no information about `H_{t₀}` beyond its Taylor data; its value is that it can be read on the real line at the later time. [D]
- **Lateral entry.** Vertical dissipation controls depth, not the horizontal path of a nonreal zero. This is the gap between nonreal time and `Λ_X`. The energy propagates at finite speed, so a window real on a neighbourhood of width `4J` has energy and nonreal time `≪ w^{J+1}/(J + 1)!` on its core; a pair of tiny height is not excluded by this.
- **Times in the maximum principle.** A barrier moves forward in heat time. The horizon gives information at later times; backward, the gap law only reaches `≍ log⁻²X` below a snapshot.
- **Short windows.** The critical-scale theorems hold in windows of width `≍ κ/log T`. Their exceptional measure comes from a mean square, and it does not survive a union over the `≍ log T/κ` windows of a unit interval; the unit-window theorems stop at `η_T`.

## 9. Open research topics

The central inequality and reality below the critical scale, `τ ≲ κ(δ)`, on density-one heights; the passage from the local statistics to the crystal; control of the local count and of the energy `E` in a cylinder below that scale; compression near a clump for the actual source; the local count at time `t` around a zero of depth `d`; the critical-scale theorems on unit windows; exact exclusion of tiny nonreal pairs in a lateral entry.

## 10. Position in the corpus

NGF is the parabolic side of ZCG. ZCG's camera fixes the configuration at `t = 0`, ZCG's horizon fixes it at `t ≍ 1/log X`, and NGF studies the region between them, with the horizon as a boundary condition. RHTower supplies the source estimates, the collision law and the reverse Gaussian; ZCG the half-Gauss transform, the sub-Weyl horizon, the typical-height estimates and the polynomial mesh; FFP the Walsh theorem and the finite-free view of the same flow; ArithmeticLocalDivisorGeometry the Hermite edge. SquareRootThreshold and the Selberg near-line density supply the off-line moments, and RHTower's typical box the slope of `ζ` at the critical scale. By ZCG's rule, no Weil positivity or spectral sign enters here.

## 11. Success criteria and contributions

The programme succeeds when its tools exist for the actual source, its questions are answered or reduced to one precise open input, and the reach and failure of each law are shown on the fakes. A theorem that reaches `τ ≍ 1` on density-one heights, with a constant depending on the density, would be a decisive contribution.

A contribution must be unconditional in Lean; state a blind law for a class containing both `H_t` and a fake; and say which datum of `ζ` it uses when it is not blind. A new identity counts only if it yields a bound the previous tools could not state.
