# Zero Configuration Geometry (ZCG)

Namespace `GaloisForLFunctions.ZeroConfigurationGeometry`; umbrella `ZeroConfigurationGeometry.lean`;
49 modules.

## 1. Motivation

The explicit formula is usually read as a sum rule. Either one asks for the sign of the result
(Weil positivity), or one asks how many zeros it certifies on the line (proportion theorems). This
programme excludes both as the decisive step: no positivity of a form, no spectral realization, no
count of zeros, no Hodge index.

ZCG reads the explicit formula as a **camera** instead. A window `f` supported in `[−r, r]` produces
an exact image of the zero configuration: the Weil form, or the Gram matrix of a grid of modulated
windows. The primes below `e^{2r}` compute that image. RH says where the imaged points lie. The
field asks four questions of the image, none of them about a sign:

- **identification**: when does the image determine the configuration?
- **mimicry**: which configurations share an image, and what shape do they have?
- **certification**: which properties of images force every point onto the real curve?
- **deformation**: how can a point leave the real curve along a family?

The answers form one picture. Identification is cheap and sign-free: finite pieces are seen at
every aperture and pinned by the primes. Hiding has a price in density: a cancelling cluster at
aperture `a` has density at least `2a/π`, and inside a separated union it needs a near-collision
in height. Certification is the hard part. In the function field it happens at the
identification threshold, by positions. The zeros of `ζ` have unbounded density, so no finite
camera identifies or certifies them. The route to RH (§10) therefore rests on the one ζ-specific
geometric mechanism available, the archimedean contraction of the functional equation, and uses
the camera to carry it down to `ζ`. It meets the same missing input as every route: the geometry of
primes below the mean spacing.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Camera of aperture `r` | `ApertureWindow r` | `C²` windows supported in `[−r, r]` |
| Zero coordinate, depth | `Zeta23.gammaOf`, `gammaOf_re`, `gammaOf_im` | `γ_ρ = (ρ − ½)/i = γ − iδ`, `δ = β − ½` |
| Tilt | `tilt δ f` | `f·e^{δu}`; a point of depth `δ` is a real point of the tilted camera |
| Pair, squared gap | `paperFT_add_add_sub` | FE pair `c ± w`, `w²` real: real pair `w² > 0`, collision `w = 0`, tilted pair `w = iδ` |
| Pair signal, depth signal | `pairSignal`, `depthSignal` | pair minus doubled centre; `depthSignal f x δ = pairSignal f x (iδ)` |
| Second-moment image | `secondMoment` | `(u² f)^(c)` |
| Point image | `pointImage` | `f̂(γ_z) conj ĝ(conj γ_z)`, the contribution of one point to `W(f, g)` |
| Signed multiplicity, cluster, site | `multDiff`, `siteOf` | `m_Z − m_{Z'}`; its support; the FE representative with `β ≥ ½` |
| Differential, division window | `annihilate z g`, `divWindow` | `g' + izg`, multiplying the transform by `−i(w − z)`; its inverse at a transform zero |
| Blind, isolating window | `exists_window_blind_to_perturbed_lattice`, `exists_isolating_window` | transform vanishing on a configuration; on all of it but one point |
| Count bound, lower density | `exists_injective_near_int`, `HasLowerDensityAtLeast` | at most `D(b − a) + C` points over `[a, b]`; at least `2Dρ − K` in large balls |
| Perturbation factor | `pertFactor` | `((z − ν_k)/(z − μ_k))((i − μ_k)/(i − ν_k))`, moving a lattice point |
| Arithmetic image | `arithmeticImage λ f` | full Weil functional of `f ⋆ f̃` for arithmetic data `λ` |
| Prime channel, discrepancy | `primeChannel`, `primeDiscrepancy` | `Σ_n λ(n) n^{−1/2}(k(log n) + k(−log n))`; `Σ_{n ≤ e^{2r}} |λ − λ'|/√n` |
| Frobenius configuration, curve camera | `CurveDatum`, `spectrum`, `curveImage`, `traceConfig` | `2g` normalized eigenvalues; their power sums `S_1, …, S_k` |
| Column, Euler column | `offLineLatticeConfig`, `eulerColumnCoeff` | vertical lattice of spacing `2π/L`; zeros of `1 + Ap^{−s} + p^{1−2s}` |
| Fakes | `pureDatum`, `goldenRootDatum`, `flipData`, `twinData` | function-field and arithmetic data that partially mimic `ζ` |
| Collision | `IsCollision`, `IsFrobeniusCollision` | a real double root; a double trace root or a trace root at `±2` |
| Heat flow, heat step, spread | `heatFlow`, `heatStep`, `spread` | `e^{−tD²}`; `1 − cD`; `Σ_{j<k}(x_j − x_k)²` |
| Euler stage | `eulerStage`, `stageLine_eq_mul_exp` | the truncation `Λ_X` and its phase on the critical line |
| Cosine camera | `cosineWindowTransform` | transform of `cos(2θs)` on `[−½, ½]` at complex frequency |

## 3. Language

- A camera **identifies** a class when equal images force equal configurations. Two
  configurations are **mimics** at aperture `a` when every window of aperture `a` gives the same
  image; their signed difference is a **cancelling cluster**.
- **Depth is tilt**: the image sees depth only through `cosh(δu)` and `sinh²(δu/2)` in the window.
- A window is **blind** to a configuration when its transform vanishes there. It **isolates** a
  point when it is blind to the rest and sees that point.
- The **density aperture** of a configuration of density `D` is `πD`, the least aperture of a blind
  window. The **Ingham scale** at aperture `a` is `π/(2a)`, the least separation a camera of
  aperture `a` resolves.
- The **identification threshold** of a class is the least aperture that identifies it. The **sign
  threshold** is the least aperture at which Weil positivity decides reality. The gap between them
  is the **certification gap**.
- A point is **pinned** by arithmetic data when no finite modification keeps the arithmetic image.

## 4. Mechanisms

**The camera.**
1. *Depth is tilt.* `f̂(x − iδ) = (f e^{δu})^(x)`. Every zero is a real point of the camera tilted
   by its depth. In the matrix explicit formula its Gram summand is the rank-one block of the
   tilted taper at its real ordinate.
2. *Pairs are analytic in the squared gap.* `f̂(c + w) + f̂(c − w) = (2cos(wu) f)^(c)`, even in `w`.
   An FE pair is its real centre seen through `2cosh(δu)`. Minus the doubled centre it is the
   centre seen through `4 sinh²(δu/2)`, of size at most `4 sinh²(δr/2) ∫|f|`, and every smaller value
   is attained.
3. *The squared gap is read at second order.* For `|w| r ≤ 1`,
   `|pairSignal + w² M₂| ≤ (5/48)|w|⁴ r⁴ ∫|f|`, with `M₂ = −f̂''`. Reality of a near-collision is the
   sign of the coefficient of the image's curvature in the height variable. Through the explicit
   formula this curvature is the `(log n)²`-weighted prime sum below `e^{2r}`. This is the
   coalescent channel, stated as an identity.

**Identification.**
4. *Finite modifications are seen at every aperture.* The image difference of a finite modification
   is `Σ c_z f̂(γ_z) conj ĝ(conj γ_z)`. Polarization, the fundamental lemma and the identity theorem
   turn its vanishing into that of the exponential polynomial `Σ c_z e^{iγ_z u}`, so every
   coefficient vanishes. Cancelling clusters are infinite.
5. *Differential windows invert the camera.* Composing `g ↦ g' + izg` over the other points gives
   a window, of any aperture, that reads one coefficient:
   `W_Z(f, g) − W_{Z'}(f, g) = c(z₀) ∏_{z ≠ z₀}(−i(γ_{z₀} − γ_z))`. The inverse is conditioned by
   the gap product and has explicit mass. Modulation moves it to any height, and with integer
   multiplicities it gives quantitative identification.
6. *The primes pin every finite piece of `ζ`.* The arithmetic image at aperture `r` depends on
   `λ(n)` only for `log n < 2r`. A prime discrepancy `D_r` moves it by at most `2D_r sup|k|`. So data
   agreeing with `Λ` below `e^{2r}` fix every finite piece of the zeros of `ζ`, and data that first
   differ from `Λ` at `n₀` are seen exactly above aperture `½ log n₀`.
7. *Function-field identification.* The curve camera of order `k` sees exactly the top `k`
   coefficients of the trace polynomial (Dickson sums against power sums, then Newton). Order `g`,
   i.e. lag `g log q`, identifies; below it pure and tilted mimics exist.

**Hiding.**
8. *Hiding needs near-collisions.* On the line, Ingham's inequality resolves every separation
   `g > π/(2a)` at aperture `a`. With tilts the kernel `∫ cos(at) e^{(σ+ix)t}` is explicit, and
   Ingham survives with the factor `cosh(2sT)`. An FE pair is one site with a `2×2` block. In the
   profile basis `cosh(δv)`, `sinh(δv)/(δV)` the block is uniform in depth. For shallow
   configurations a pair splits into its centre `p + q` and a remainder of size `e^{2sV} − 1`.
   Localizing at the site of maximal weighted multiplicity makes the centre real, and Ingham at the
   sharp threshold beats the remainder. So shallow mimics need near-collisions below every
   `g > π/(2a)`, and the on-line lattice pair attains `π/(2a)`.
9. *Hiding costs density.* A pair of windows `(f, g)` isolates a point `w₀` when, at every other
   point `w`, `f̂(γ_w) = 0` or `ĝ(conj γ_w) = 0`, and such a point carries no cancellation. Match
   the heights of a cluster into `D⁻¹ℤ` by Hall's theorem, and split by the parity of the lattice
   index. Then `f` must be blind to one half and `g` to the other. Each half is a complex
   perturbation of `2D⁻¹ℤ` of depth `≤ ½`, blinded at every aperture `> πD/2`. So a cancelling
   cluster at aperture `a`, counted point by point, has density `≥ 2a/π`, at any depth. A separated
   union has at most two cluster points per height. Hence mimics need near-collisions below every
   `g > π/a`, whatever the depths.
   *Locally.* Only the cluster near the height `X` of a point `z₀` has to be counted. Translate it
   to height `0`, blind its two halves with windows whose floor at `z₀` and decay on the strip do
   not depend on the cluster, and modulate back by `e^{−iXu}`. The far cluster then enters with
   weight `(1 + |X|)²/(1 + R)^{2k−2}` for every decay order `k`. So an isolated cancelling point at
   height `X` forces density `≥ 2a/π` within distance `R ≍ (1 + |X|)^{1/(k−1)}` of `X`.

**Kernel design.**
10. *Multipliers.* Shifts multiply the transform by exponential polynomials, at the cost of their
    width. Sine multipliers blind lattices and finite unions of total density `D` above `πD`.
    Convolution with a density `φ` on `[−W, W]` blinds the zero set of `φ̂` above `W`. Linear factors
    cost nothing: `annihilate` multiplies by `−i(w − κ)`, and at a zero `κ` `divWindow` divides by it,
    keeping the support.
11. *Perturbed lattices.* Dividing at the lattice points `μ_k` and multiplying by `ν_k`, one factor
    at a time, gives stage windows of fixed aperture with transform `sin · b̂ · Π_k r_k`. On the real
    line the sine absorbs the nearest factor and harmonic sums bound the rest, so
    `|sin · Π r_k| ≤ K(1 + |x|)^p` uniformly. The stages converge uniformly, and the limit is blind
    to every `ν_k`. This works for complex `ν_k` of depth `≤ ½`, since `|i − ν| ≥ |i − Re ν|/2`.
    On the strip `|Im z| ≤ ½` the same bound holds with `|sin|` periodic in `Re z`. At a point
    `η`-far from every `ν_k` and `h/4`-far from the lattice the product has an explicit floor
    `c₀ e^{−κC}(1 + |Re z|)^{−q}`, uniformly in the index set. Every factor is `≥ η/((η + L)(1 + L))`,
    and the factors near `1` are `≥ e^{−2|r_k − 1|}`.
12. *Blind windows are entire functions.* An entire function of type `A` that decays on horizontal
    lines is the transform of a smooth window in `[−A, A]`; the proof is a contour shift, Fourier
    inversion and the identity theorem. So blind windows above `τ` exist exactly when entire
    functions of every type above `τ` vanish on the configuration. For configurations of finite
    upper uniform density, Hall matching into a lattice reduces the question to item 11.
13. *Blindness costs the density aperture.* Jensen's formula, with the angular mean `(2/π)R` of
    `|Im z|`, gives `A ≥ πD` for a nonzero blind window of aperture `A` and lower density `D`. With
    item 12 the aperture `πD` is exact for configurations of uniform density, and no window is
    blind to a configuration of unbounded density.
14. *Real kernel zeros.* At its zeros the cosine camera's transform satisfies
    `z sin z = (θ tan θ) cos z`. For `z = u + iv` and `0 < θ < π/2` this forces `v = 0`, so additive
    rigidity of kernel zeros holds over `ℂ`.

**Arithmetic fakes.**
15. *Ramanujan is reality.* A zero of `1 + Ap^{−s} + p^{1−2s}` has `Re s = ½` exactly when `A² ≤ 4p`.
    For curves, `|β| = 1` exactly when `β + β⁻¹ ∈ [−2, 2]`.
16. *Euler columns are lattices.* With `A_δ = −2√p cosh(δ log p)` the zero set is the column
    `{½ ± δ + 2πik/log p}`, which mimics the doubled on-line lattice exactly at every aperture
    `≤ ½ log p`. The data of the twin are separated from `Λ` at the same aperture, so data and
    configuration give the same threshold.

**Deformation and repulsion.**
17. *Reality leaves only through collision.* Simple real roots persist and real-rootedness is
    closed, so along a family the first exit from reality is a real double root. In the function
    field purity is closed and is lost only at a Frobenius collision.
18. *Heat time spreads the configuration.* `e^{−tD²}` raises `Σ_{j<k}(x_j − x_k)²` by exactly
    `2n²(n − 1)t`. Each step `1 − cD` keeps a real configuration real and simple and never shrinks
    its mesh: at two new roots the logarithmic derivative is compared with a telescoping sum.
    Laguerre steps never deepen, and shift averages contract the squared depth by `λ²`, the discrete
    de Bruijn law.
19. *Repulsion in model families.* Above its horizon the Euler stage `Λ_X` moves by a phase of speed
    `½ log(t/2π)`, up to the prime weight `W/2`. Its zeros there are on the line, simple, and exactly
    the preimage of `πℤ`. The mechanism needs only a symmetric half, zero-free on `Re z > ½` with
    dominated logarithmic derivative. So it holds for every finite real Dirichlet carrier
    `Γ_ℝ(z) exp(Σ_{n ≤ X} a(n) n^{−z})` above the horizon `log(t/2π) > W_a + 6/t`. Read backwards,
    a tilted zero at height `t` costs prime weight `W_a ≥ log(t/2π) − 6/t`. The twins are tilted at
    every height and pay this price as soon as the weight grows like `log` of the height, as the
    weight of `ζ` does. In the function field `∏ h'(α) = Res(h, h') ∈ ℤ` forces distinct trace
    points apart. The image of `ζ` has neither a dominating phase speed below the horizon nor
    integrality.

**Certification.**
20. *Function-field certificates.* The exact image up to the genus certifies purity by the
    positions of the trace points. A size bound at all orders does too: by simultaneous return, the
    image grows like the deepest eigenvalue, so purity is boundedness of the image. This is the
    function-field Landau principle.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| **Camera** | | |
| Depth is tilt; Gram block of a zero | `paperFT_gammaOf`, `Gsummand_eq_tilted` | unconditional |
| Pairs analytic in the squared gap | `paperFT_add_add_sub`, `paperFT_gammaOf_add_reflect`, `paperFT_realPair_eq_cos` | unconditional |
| Depth signal, sharp | `depthSignal_eq`, `norm_depthSignal_le`, `exists_depthSignal_ge` | unconditional |
| Second-order law; curvature form | `norm_pairSignal_add_sq_mul_secondMoment_le`, `norm_realPair_sub_tiltedPair_le`, `deriv_deriv_paperFT_eq_neg_secondMoment`, `norm_pairSignal_sub_sq_mul_curvature_le` | unconditional |
| Coalescent channel = height curvature of the prime channel | `weilTest_modulate`, `primeChannel_modulate`, `deriv_deriv_primeChannel_modulate` | unconditional |
| **Identification** | | |
| Finite modifications seen at every aperture | `eq_of_weil_eq_on_aperture_of_finite`, `infinite_modification_of_mimic` | unconditional |
| Explicit inverse by differential windows | `paperFT_annihilate`, `exists_window_sum_eq_coeff_mul_gaps`, `exists_windows_W_sub_W_eq` | unconditional |
| Quantitative identification, uniform in height | `exists_annihilating_window_bound`, `norm_multDiff_mul_gaps_le`, `multDiff_eq_zero_of_precision`, `norm_multDiff_mul_gaps_le_at_height` | unconditional |
| Primes pin finite pieces of `ζ`, stably | `arithmeticImage_congr_of_eq_below`, `eq_zeta_of_arithmeticImage_of_finite`, `norm_weilFullFunctional_sub_le`, `multDiff_eq_zero_of_arithmetic_precision` | unconditional |
| Every fake is separated exactly at its first prime | `FirstDisagreement`, `exists_window_arithmeticImage_ne`, `arithmeticImage_eq_iff`, `eq_of_arithmeticImage_eq`, `exists_window_W_ne_zeta`, `flipData_mimic_iff` | unconditional |
| Function-field identification at `g log q` | `spectrum_eq_of_powerSum_eq`, `spectrum_eq_of_weil_eq_on_aperture`, `curveConfig_weil_eq_iff_trace_eq`, `identification_threshold_sharp` | unconditional |
| The curve camera sees exactly the top coefficients | `curveImage_eq_iff_coeff_eq`, `eq_of_curveImage_eq`, `exists_pure_mimics`, `exists_tilted_mimic` | unconditional |
| **Hiding** | | |
| Hiding needs near-collisions (on-line) | `exists_near_pair_of_onLine_mimic` | unconditional |
| Ingham's inequality with tilts; block inequality for pairs | `tiltedKernel_eq`, `tilted_ingham_inequality`, `pairGap_pos`, `block_ingham_inequality`, `eq_zero_of_pairSum_eq_zero` | unconditional |
| Tilted resolution; aligned pairs and the dark sector | `eq_of_weil_eq_of_pairSeparated`, `exists_near_pair_or_shallow_pair_of_mimic`, `pairWeight_modScaledBump_eq_sq`, `exists_near_pair_or_dim_shallow_pair_of_mimic` | unconditional |
| Resolution is uniform in depth | `uniform_block_inequality`, `norm_integral_cos_mul_mul_cexp_le`, `eq_of_weil_eq_of_heightSeparated`, `exists_near_pair_of_mimic`, `exists_near_pair_of_mimic_of_le` | unconditional |
| Shallow configurations are resolved at the Ingham scale; `π` is optimal | `pair_eq_centre_add_rem`, `remainder_upper`, `ingham_lower`, `inghamConst_mul_normSq_le`, `eq_of_weil_eq_of_shallow`, `exists_depth_resolving_at_ingham_scale`, `exists_near_pair_or_deep_of_mimic_at_ingham_scale`, `not_exists_depth_resolving_at_ingham_threshold` | unconditional |
| Isolation identifies the cluster; thin backgrounds hide no tilted point | `W_sub_W_eq_tsum`, `W_eq_of_mimic`, `multDiff_eq_zero_of_isolated`, `eq_of_mimic_of_isolable`, `eq_of_mimic_of_simple_zeros`, `eq_of_mimic_of_onLine_lattice`, `eq_of_mimic_of_perturbed_lattices`, `eq_of_mimic_of_perturbed_lattices_and_finset` | unconditional |
| Sparse clusters never cancel: density `< 2a/π`, any depth, sharp | `multDiff_eq_zero_of_pointImage_isolated`, `eq_of_mimic_of_onLine_count_le`, `exists_onLine_mimic_at_density`, `eq_of_mimic_of_count_le` | unconditional |
| Resolution at `π/a` at every depth | `eq_of_weil_eq_of_heightSeparated_of_lt`, `exists_near_pair_of_mimic_of_lt` | unconditional |
| Square-root threshold for columns of RvM density | `rvmLattice_mimic_iff` | unconditional |
| **Kernel design** | | |
| Windows blind to a lattice; the threshold `π/h` is sharp | `exists_window_blind_to_lattice`, `eq_zero_of_blind_to_lattice`, `exists_window_blind_to_lattice_iff` | unconditional |
| Exponential polynomials, finite unions of lattices, transforms of densities | `exists_window_blind_to_expPoly_zeros`, `exists_window_blind_to_lattices`, `exists_window_blind_to_densityTransform_zeros` | unconditional |
| Division at transform zeros; isolating windows | `exists_window_div`, `exists_isolating_window`, `exists_window_isolating_lattice_point` | unconditional |
| Products over a perturbed lattice, real and complex | `summable_norm_pertFactor_sub_one`, `tprod_pertFactor_ne_zero`, `norm_I_sub_re_le`, `norm_sin_mul_prod_pertFactor_le` | unconditional |
| Products on the strip; the floor at an isolated point | `norm_sin_mul_prod_pertFactor_le_strip`, `isoConst_le_norm_pertFactor`, `norm_prod_pertFactor_ge_strip`, `norm_tprod_pertFactor_ge_strip`, `norm_sin_mul_tprod_pertFactor_le_strip` | unconditional |
| Blind windows for perturbed lattices, real and complex | `exists_stage_window`, `exists_blind_limit_window`, `exists_window_blind_to_perturbed_lattice`, `exists_window_blind_to_complex_perturbed_lattice`, `exists_window_blind_to_perturbed_lattices` | unconditional |
| Converse Paley–Wiener; blind windows are entire functions | `exists_smooth_source_of_entire`, `exists_window_of_entire`, `blind_windows_iff_entire` | unconditional |
| Blind windows at the uniform density | `card_le_card_biUnion_intNbhd`, `exists_injective_near_int`, `exists_window_blind_of_count_le`, `exists_window_blind_of_count_le_complex`, `exists_window_blind_of_separated` | unconditional |
| Blindness costs the density aperture; `πD` is exact | `pi_mul_le_aperture_of_blind`, `eq_zero_of_blind_of_unbounded_density`, `eq_zero_of_blind_to_real_zeros_of_xi`, `blind_aperture_threshold` | unconditional |
| Uniform isolating windows: blind to a matched cluster, explicit floor at the target, strip decay independent of the cluster | `exists_bump_one_le_norm_paperFT_I_mul`, `windowFloor`, `windowGrowth`, `isolating_window_of_bump`, `exists_uniform_isolating_window` | unconditional |
| **Local camera** | | |
| Far zeros are faint in the local camera | `localWindow`, `paperFT_localWindow`, `norm_paperFT_localWindow_mul_le`, `norm_pointImage_mul_le`, `decay_le_tempered`, `tsum_far_le`, `norm_tsum_far_le`, `tsum_far_multDiff_le`, `tsum_far_zeta_le` | unconditional |
| Isolated points are seen by the local camera, with explicit constant | `apertureWindow_localWindow`, `localCameraConst`, `one_add_pow_le_of_isolated_cancellation_of_bump`, `one_add_pow_le_of_isolated_cancellation` | unconditional |
| The zeros of `ζ` have the sharp local density | `mu_le`, `card_le_ncount`, `ncount_le_of_goodHeight`, `exists_card_le_sharp`, `exists_card_le_sharp_centred`, `exists_card_le_sharp_centred_abs` | unconditional |
| Cosine camera: real zeros, complex additive rigidity | `im_eq_zero_of_cosineWindowTransform_eq_zero`, `no_complex_additive_zero_triple` | unconditional, `0 < θ < π/2` |
| **Arithmetic fakes** | | |
| Ramanujan is reality | `localFactor_zero_depth`, `localFactor_zero_re_eq_half_iff`, `curveDatum_pure_iff_tracePoints` | unconditional |
| Euler columns hide exactly below their prime | `eulerColumn_mimics_onLineLattice`, `no_bounded_aperture_excludes_eulerColumns`, `offLineLattice_mimic_iff`, `eulerColumn_mimic_iff` | unconditional |
| The twins are seen exactly at their prime (data) | `twinData_firstDisagreement`, `twinData_mimic_iff` | unconditional |
| **Deformation and repulsion** | | |
| Collision exit; function-field purity exit | `eventually_splits_of_simple`, `isClosed_splits`, `exists_first_collision`, `isPure_iff_circle`, `exists_first_frobenius_collision` | unconditional |
| Heat-time spread law; bounded backward exit | `coeff_heatFlow_sub_two`, `spread_roots_heatFlow`, `exists_nonreal_root_heatFlow` | unconditional |
| Heat steps never shrink the mesh | `meshGe_add_smul_derivative`, `nodup_roots_add_smul_derivative`, `iterate_heatStep` | unconditional |
| Laguerre steps never deepen; shift averages contract | `rootsInStrip_heatStep`, `heatStep_keeps_triple_edge_root`, `im_eq_zero_or_sq_add_sq_le_of_shiftAverage`, `roots_shiftAvgList_im_sq_le` | unconditional |
| Euler stages repel above the horizon; counted by their phase | `stageLine_eq_mul_exp`, `eulerStage_deriv_ne_zero_above_horizon`, `eulerStage_ne_zero_of_lt_gap`, `exists_eulerStage_zero_within`, `eulerStage_eq_zero_iff_phase`, `ncard_eulerStage_zeros` | unconditional |
| Integral configurations collide or repel | `prod_derivative_roots_eq_resultant`, `collide_or_repel` | unconditional |
| Symmetric halves are phase lattices | `SymmetricHalf`, `sym_linePt`, `line_eq_mul_exp`, `sym_eq_zero_iff_phase`, `sym_deriv_ne_zero`, `sym_ne_zero_of_phase_lt`, `exists_sym_zero_of_phase_ge`, `ncard_sym_zeros`, `norm_lt_of_speed_pos`, `sym_ne_zero_near_line` | unconditional |
| Finite carriers are real above their horizon; the Euler-depth descent | `carrierHalf`, `carrierWeight`, `re_carrierLogDeriv_ge`, `carrier_ne_zero_near_line`, `carrier_deriv_ne_zero`, `carrier_eq_zero_iff_phase`, `ncard_carrier_zeros`, `eulerDepthCoeff`, `carrierWeight_eulerDepth`, `eulerDepth_ne_zero_near_line`, `eulerDepth_deriv_ne_zero` | unconditional |
| Tilts cost prime weight: the twin calibration of O3 | `log_le_carrierWeight_of_tilted_zero`, `log_le_eulerDepth_weight_of_tilted_zero`, `localFactor_twin_tilted_zero`, `twin_tilt_costs_weight`, `exists_twin_tilt_beyond_every_weight` | unconditional |
| **Certification** | | |
| Function-field certification at the identification threshold | `pure_iff_of_powerSum_eq`, `pure_iff_of_weil_eq_on_aperture`, `isPure_of_curveImage_eq` | unconditional |
| Bounded images certify purity; growth reads the deepest eigenvalue | `exists_simultaneous_return`, `curveImage_growth`, `isPure_iff_bounded_curveImage` | unconditional |

## 6. Questions and what the programme answers

**Q0 Certification.** *Which geometric property of the imaged configuration, computable from
arithmetic images, forces every point onto the real curve?*
- Function field: the image up to the genus, read as the positions of the trace points in
  `[−2, 2]` (`pure_iff_of_weil_eq_on_aperture`, `isPure_of_curveImage_eq`). Also boundedness of the
  image at all orders (`isPure_iff_bounded_curveImage`). A size bound at finitely many orders
  certifies nothing.
- *Open:* a sign-free certificate for `ζ`. Its zeros have unbounded density, so no finite aperture isolates a
  tilt (`eq_zero_of_blind_to_real_zeros_of_xi`); see §10 and §11.

**Q1 Identifiability.** *When, and how stably, does the image determine the configuration?*
- Finite modifications are identified at every aperture, constructively and stably
  (`exists_windows_W_sub_W_eq`, `multDiff_eq_zero_of_precision`), uniformly in height. With
  approximate prime data the precision is the prime discrepancy below `e^{2r}`
  (`multDiff_eq_zero_of_arithmetic_precision`): only near-collisions absorb prime-side error.
- Data that first differ from `Λ` at `n₀` are seen exactly above aperture `½ log n₀`
  (`arithmeticImage_eq_iff`).
- Infinite configurations: suppose the union is separated, apart from FE partners, at a fraction
  `c` of the mean spacing `2π/L`. Then aperture `L/(2c)` identifies at every depth
  (`eq_of_weil_eq_of_heightSeparated_of_lt`), and aperture `L/(4c)` identifies shallow
  configurations (`exists_depth_resolving_at_ingham_scale`). Against columns of Riemann–von Mangoldt
  density, the matrix camera identifies exactly above exponent `λ = ½` (`rvmLattice_mimic_iff`).
- Function field: order `m` of the camera fixes the coefficient of degree `g − m`, so the genus is
  the exact threshold (`curveImage_eq_iff_coeff_eq`, `exists_pure_mimics`).
- *Open:* configurations with near-collisions below a fixed fraction of the mean spacing. For them
  identification is the coalescent question Q3.

**Q2 Cancelling clusters.** *Which clusters cancel, and why can arithmetic not produce them?*
- Finite clusters never cancel (`infinite_modification_of_mimic`).
- A cancelling cluster at aperture `a`, counted point by point, has upper uniform density at least
  `2a/π`, at any depth (`eq_of_mimic_of_count_le`). The on-line lattice pair cancels at exactly
  that density (`exists_onLine_mimic_at_density`).
- Inside a separated union a cancelling cluster contains two points of different FE orbits closer
  than any `g > π/a` (`exists_near_pair_of_mimic_of_lt`). For shallow configurations they are closer
  than any `g > π/(2a)` (`exists_near_pair_or_deep_of_mimic_at_ingham_scale`), and the constant `π`
  is optimal (`not_exists_depth_resolving_at_ingham_threshold`).
- Isolable clusters never cancel (`eq_of_mimic_of_isolable`). This covers perturbed lattices plus
  finitely many arbitrary points above `πD` (`eq_of_mimic_of_perturbed_lattices_and_finset`). Euler
  columns cancel against on-line lattices exactly below their dual frequency
  (`eulerColumn_mimic_iff`).
- Locally: let `z₀` be a cluster point at height `X`, `η`-isolated within `R`, with the cluster
  near `X` of count `(D, C₀)` and `πD < 2a`. Then `(1 + R)^{2k−2} ≤ B (1 + |X|)² Σ |c|/(1 + |γ|²)`,
  with `B = B(a, D, C₀, η, k)` (`one_add_pow_le_of_isolated_cancellation`). An isolated cancelling
  point therefore needs density `2a/π` within a power `(1 + |X|)^{1/(k−1)}` of its height.
- *Open:* whether deep configurations hide at union separations between `π/(2a)` and `π/a`.

**Q3 Sub-spacing geometry.** *What does the image say below the mean spacing?*
- Near a collision the camera reads the squared gap linearly, as the coefficient of the height
  curvature of the image (`norm_pairSignal_sub_sq_mul_curvature_le`). The height curvature of the
  prime channel is exactly the `(log n)²`-weighted prime sum (`deriv_deriv_primeChannel_modulate`).
- *Open:* the arithmetic input itself, control of this weighted prime sum at every height.

**Q4 Deformation.** *How can reality be lost along a family, and what repels?*
- Reality is lost only at a real double root (`exists_first_collision`). In the function field it
  is lost only at a Frobenius collision (`exists_first_frobenius_collision`).
- Heat time repels on average, at the exact rate `2n²(n − 1)` (`spread_roots_heatFlow`). It also
  repels pointwise: heat steps keep real configurations real and simple and never shrink the mesh
  (`iterate_heatStep`), and shift averages contract the depth (`roots_shiftAvgList_im_sq_le`).
  Backward heat time is bounded: a real configuration of total squared gap `S` is not real before
  time `−S/(2n²(n − 1))` (`exists_nonreal_root_heatFlow`).
- Model repulsion laws: above its horizon the Euler stage `Λ_X` is a simple on-line phase lattice
  (`eulerStage_deriv_ne_zero_above_horizon`, `ncard_eulerStage_zeros`). Integral configurations
  collide or repel (`collide_or_repel`).
- Every finite real carrier `Γ_ℝ(z) exp(Σ_{n ≤ X} a(n) n^{−z})`, symmetrized, is a symmetric half.
  Above `log(t/2π) > W_a + 6/t` it has no zero with `0 < |Re z − ½| ≤ u₀`, and its zeros on the
  line are simple and counted exactly by the phase (`carrier_ne_zero_near_line`,
  `ncard_carrier_zeros`). Along the Euler depth `a = sΛ/log n` the weight is `|s| W_Λ`
  (`carrierWeight_eulerDepth`). The deformation from the archimedean carrier (`s = 0`) to the
  Euler stage (`s = 1`) is collision-free at height `t` for `s < (log(t/2π) − 6/t)/W_Λ`
  (`eulerDepth_ne_zero_near_line`). This is the Euler-depth analogue of route steps 1–3.
- *Open:* a repulsion law that reaches tilt `0`, i.e. reality of `ζ` itself, along backward heat
  time or Euler depth.

**Q5 Window design.** *Which windows make tilted points inconsistent with their real neighbours?*
- Blind windows are exactly entire functions of exponential type vanishing on the configuration
  (`blind_windows_iff_entire`).
- Take configurations of depth `≤ ½`. Upper uniform density `D` gives blind windows at every
  aperture `> πD` (`exists_window_blind_of_count_le_complex`). Lower density `D` forces every
  nonzero blind window to have aperture `≥ πD` (`pi_mul_le_aperture_of_blind`). So for uniform
  density the threshold is exact (`blind_aperture_threshold`), and above it, for every chosen point,
  some window isolates it.
- The cosine camera has only real kernel zeros, so additive rigidity holds over `ℂ`
  (`no_complex_additive_zero_triple`).
- *Open:* the exact aperture for configurations whose upper and lower densities differ, i.e. the
  Beurling–Malliavin radius.

**Q6 Selectivity.** *Does every answer separate `ζ` from its fakes?*
- Euler columns hide exactly below `½ log p` and are excluded only by the Ramanujan bound
  (`eulerColumn_mimic_iff`, `localFactor_zero_re_eq_half_iff`). The twin's data are seen at the same
  aperture (`twinData_mimic_iff`). Bounded apertures exclude no infinite family of twins
  (`no_bounded_aperture_excludes_eulerColumns`).
- Prime flips, however sparse, are seen exactly above `½ log p₀` (`flipData_mimic_iff`). The golden
  root datum mimics the pure datum exactly up to lag `g log q` (`identification_threshold_sharp`).
- Mimicry of arithmetic data lives only at the level of configurations: at the level of data every
  fake is separated at its first prime.
- Domination is not selective. It holds for every finite real carrier above its horizon, including
  flips, twin truncations and Davenport–Heilbronn data. A tilted carrier zero at height `t` costs
  weight `W_a ≥ log(t/2π) − 6/t` (`log_le_carrierWeight_of_tilted_zero`). The twin is tilted at every
  height (`localFactor_twin_tilted_zero`), and for every weight bound some tilted twin zero is out
  of reach (`exists_twin_tilt_beyond_every_weight`). Since `W_Λ(X)` also grows like `log` of the
  height, the size of the weight cannot separate `ζ` from the twins. The selective input must be how
  the prime sum of `ζ` cancels below the horizon.

## 7. Tools

**Developed.**
- Tilt calculus, the pair formula for complex gaps, exact depth and pair signals, and a
  second-order Taylor law with explicit constant.
- Differential and division windows with prescribed transform zeros, mass bounds, modulation to any
  height, and the prime-discrepancy bound for arithmetic data.
- Polarization for finite and infinite signed modifications, exponential independence on an
  interval, and smooth windows with prescribed transform value.
- Ingham's inequality with tilts and the block inequality for FE pairs. The profile basis
  `cosh(δv)`, `sinh(δv)/δ` with uniform Gram bounds, Schur bounds for symmetric kernels, double
  integration by parts. The centre–remainder split of a pair, and localization at the site of
  maximal weighted multiplicity.
- Kernel design: exponential and sine multipliers, convolution with densities, Poisson
  periodization. Products over perturbed lattices with their uniform bound on the real line, and
  uniform limits of windows. The converse Paley–Wiener theorem, Hall matching of configurations of
  bounded local count into lattices, two-window isolation, and Jensen's bound for blind windows.
- The local camera: product bounds and floors on the strip, uniform isolating windows, modulation
  to height `X`, the far-tail bound for tempered clusters, and the sharp local zero count of `ζ`
  (density `(1/2π) log((X + R)/2π)`, error `O(log X)`).
- Symmetric halves: phase lattices of holomorphic functions with dominated logarithmic derivative,
  and the prime weight of finite real carriers.
- Newton and Dickson reciprocity for Frobenius spectra, simultaneous return of unimodular numbers,
  and resultants of trace polynomials.
- Sign-change persistence and closedness of real-rootedness. The heat operator with its coefficient
  law, logarithmic-derivative arguments for heat steps, pair-factor arguments for shift averages,
  and the phase law of Euler stages.

**To build.**
- Explicit constants for the local camera: `B(a, D, C₀, η, k)` as an explicit function, from a bump
  with explicit transform decay (a smooth bump convolved with a box power `sinc^m`).
- Resolution of deep configurations between `π/(2a)` and `π/a`.
- The Beurling–Malliavin radius of a configuration, through the equivalence with entire functions.
- Signed prime geometry below the mean spacing, as input to the coalescent channel.

## 8. Traps

| Trap | Truth |
|---|---|
| Visibility means a negative Weil form | Identification is sign-free; finite modifications are seen at every aperture, while negativity is guaranteed only beyond a logarithmic aperture (`finiteOffLine_visible`) |
| A cluster can hide in a bounded region | Finite modifications never hide; hiding needs infinitely many points |
| Cancelling clusters can be sparse or perturbed | Every cluster of upper uniform density `< 2a/π`, counted point by point and at any depth, is trivial; the lattice pair cancels at density `2a/π` |
| The density criterion needs a global count, so it says nothing for `ζ` | Only the count near the height matters: an isolated cancelling point at height `X` forces density `2a/π` within `R` with `(1 + R)^{2k−2} ≤ B (1 + |X|)² S` |
| The resolution scale of off-line pairs is worse than Ingham's | Shallow configurations are resolved at every `g > π/(2a)`, and every depth at `g > π/a` |
| An image matching the on-line shadow certifies the line | Lattices, Euler columns and band-limited modulations hide below their dual frequency |
| Bounded bandwidth excludes arithmetic fakes | For every aperture some prime carries Euler columns of every depth that hide |
| Depth is read at first order | The depth and gap signals are quadratic near a collision |
| Certifying reality needs a sign | In the function field, identification at lag `g log q` certifies purity by positions; Weil positivity is proved to decide only with `2g` lags (`curveConfig_weil_nonneg_iff_unitary_of_card_le`) |
| Identification certifies reality for `ζ` too | No finite aperture identifies the zeros of `ζ`: lattice columns of RvM density hide up to `λ = ½` |
| Reality can leave the line smoothly | Only through a collision, a real double root |
| Collisions signal non-purity | Pure configurations collide freely (a trace root at `±2`, a double trace root); a collision criterion characterizes exits, not states |
| Each heat step contracts the depth | Laguerre steps only keep the strip, since a multiple edge root survives a step; shift averages contract strictly |
| Repulsion needs a positivity or a sign | In the function field it follows from integrality (`Res(h, h')` is a nonzero integer), for Euler stages from the archimedean phase speed; neither is available for `ζ` below the horizon |
| Euler products separate `ζ` from twins at finite resolution | Only the Ramanujan bound at each prime does |
| Domination is a property of `ζ` | Domination holds for every finite real Dirichlet carrier above the horizon set by its coefficient size; it is `ζ`-specific only through how the Euler product controls the prime sum below that horizon |
| A strong enough domination bound excludes the twins | Domination excludes tilts of a finite carrier only below its weight; the twins' tilts sit at every height and are reached as soon as the weight grows like `log` height, as the weight of `ζ` does |

## 9. Context

| Direction | Programmes (module imports) |
|---|---|
| Uses | RHTower 14, SquareRootThreshold 9, HTGeometry 9, Zeta23 4, ArithmeticCastelnuovoSeveri 4, SelbergClass 1, IncommensurableGaborPinching 1 |

| Neighbour | Interface |
|---|---|
| Zeta23 | `ZeroConfig`, `paperFT`, `gammaOf`, Weil form, Gram summands of the matrix explicit formula; the zero-counting contour (Backlund, good heights, the Γ side) behind the sharp local count |
| SquareRootThreshold | `multDiff`, `TemperedConfig`, the lag structure of two-bump tests, separated Ingham; the sign-based visibility apertures that ZCG contrasts with identification |
| RHTower | vertical lattices and their Nyquist blindness; the unconditional explicit formula; the scaled bump and its decay; de Bruijn–Newman and the collision criterion; de Bruijn's strip contraction; Euler stages |
| ArithmeticCastelnuovoSeveri | curve data and their lag formula; the inverse transform `invFT` and its sup bound |
| HTGeometry | Newton identities, multiset determination, closedness of real-rootedness; the contour shift and compact inverse behind converse Paley–Wiener; Jensen counting; separated point counts |
| SelbergClass | reciprocal Euler factors of the positive twins |
| IncommensurableGaborPinching | the cosine kernel and its real additive rigidity |
| ArithmeticOrientationGeometry | growth-rate and index laws; the unbounded-aperture certificates of §11 |

## 10. The route to RH

The camera theory of §4–§6 holds for every tempered configuration. A route to RH needs a mechanism
that only `ζ` has. ZCG takes it from the functional equation and the Euler product: **archimedean
contraction**.

**The ζ-specific mechanism.** Off the line the functional-equation factor contracts:
`log|χ(σ + it)| ≤ −(σ − ½)(log(t/2π) − 4/t² − π/t)` (`norm_zetaChi_le_right_line_exp`). The rate,
`log(t/2π)` per unit depth, is `2π` times the zero density at height `t`. Whatever the functional
equation reflects loses this much off the line. Two families are proved to be dominated by it.
- *Euler carriers.* Let `E_N` be the exponential of the Euler logarithm truncated at `N`. Then
  `E_N(s) + χ(s)E_N(1 − s)` has all its strip zeros on the line above height `2π e^{2ψ(N)+1}`
  (`eulerCarrier_re_eq_half`). There it is a simple phase lattice, counted by its phase
  (`eulerStage_deriv_ne_zero_above_horizon`, `ncard_eulerStage_zeros`). The contraction pays for
  the prime mass `ψ(N)`.
- *Heat.* For `0 < t ≤ 1/8` the zeros of the heat flow `H_t` above height `2π e^{(2/3+ε)/t}` are real
  and simple (`riemannHeat_zeros_real_simple_twoThirds`). The constant `2/3` is `4μ(½)`, with
  `μ(½) ≤ 1/6` the Weyl exponent, and is the floor of the method. Here contraction and Gaussian
  smoothing pay for the size of `ζ` near the line.

In `ζ`, reality is a *domination phenomenon*: the archimedean phase outruns the arithmetic, and the
dominated configuration is a simple on-line phase lattice. The twins share this domination above
their own horizon but have tilted columns at every height, and Davenport–Heilbronn data have no
Euler logarithm to exponentiate. The route carries the domination down to `ζ` itself.

**The route.**

| Step | Statement | Status |
|---|---|---|
| 1. Start dominated | At height `X` the heat flow is real for `t ≥ t_X = (2/3 + ε)/log X` (`eventually_localNewmanConstant_le_twoThirds`) | Lean |
| 2. RH is the descent | RH holds iff the local de Bruijn–Newman constant `Λ_X` vanishes at every height (`riemannHypothesis_iff_forall_localNewmanConstant_eq_zero`) | Lean |
| 3. Exit only through collision | Along the descent `t ↓ 0`, a zero leaves the line only at a double zero (`riemannHypothesis_iff_forall_zeros_simple`, `exists_first_collision`) | Lean |
| 4. The pincer | A zero of depth `d` at height `X` forces `Λ_X ≥ c d²/log X` (`exists_le_localNewmanConstant_of_offLine_zero`), so any tilt is created by a collision at heat `t ∈ [c d²/log X, t_X]` | Lean |
| 5. The camera fixes the start | The descent is determined by the configuration of `ζ` at `t = 0`, and only there is the image arithmetic: the heat flow destroys the Euler product for `t > 0`. Hiding needs density `≥ 2a/π` near the height of the hidden point (`one_add_pow_le_of_isolated_cancellation`). The zeros of `ζ` and of a mimic with the same local density have joint density `(1/π) log(X/2π)` near `X` (`exists_card_le_sharp_centred`). So at aperture `λ log X`, `λ > ½`, the image determines the isolated points near `X`. It reads near-collisions at second order through the `(log n)²`-weighted prime sum (`norm_pairSignal_sub_sq_mul_curvature_le`, `deriv_deriv_primeChannel_modulate`) | Lean with non-explicit `B`; explicit `B` open (O2) |
| 6. Close the descent | The configuration fixed in step 5 evolves without collision on `(0, t_X]`: it has no tilted pair, and no cluster that collides in the last stretch | open (O1, O3) |

**Obstacles.**
- **O1 Domination below the mean spacing.** Step 1 stops at `t_X ≍ 4μ(½)/log X`, because size
  bounds on `ζ` near the line do not see below the mean spacing. Better exponents lower the floor
  (Bourgain's `μ(½) ≤ 13/84` gives `13/21`). Lindelöf would give `Λ_X = o(1/log X)`, still not `0`.
  Closing the route needs domination that knows the configuration at the scale `1/log X`, not only
  the size of `ζ`.
- **O2 The local camera, quantitatively.** The local density criterion is proved
  (`one_add_pow_le_of_isolated_cancellation`), and so is its count input for `ζ`
  (`exists_card_le_sharp_centred`). For `ζ` the parameters grow with the height: aperture
  `a = λ log X`, density `D ≍ log X`, count error `C₀ ≍ log X`, and isolation `η ≍ 1/log X` at
  the mean spacing. The theorem applies at height `X` once `(1 + R)^{2k−2} > B(1 + X)² S` for some
  `R ≤ X/2`, the range of the sharp count. So `B` must be explicit. It is, given the bump:
  `B = localCameraConst a D C₀ η ε C_m C_0 = (windowGrowth · C_m C_0 e^ε)² e^a (5/4)/windowFloor²`
  (`one_add_pow_le_of_isolated_cancellation_of_bump`). The window constants are of size
  `X^{O(log log X)}` and `X^{−O(log(1/η) log log X)}`. With a bump of explicit decay
  `C_m ≤ c^m (1 + m/ε)^m` (a smooth bump convolved with a box power), `B ≤ X^{O((log log X)²)}` is
  expected. Then `k ≍ (log log X)²` gives `R = X^δ` for every
  `δ > 0`, and the local camera of `ζ` works at every bandwidth `λ > ½`. This is analysis inside
  the programme, and the next target.
- **O3 Repulsion in the last stretch.** Every tilted pair of `ζ` at height `X` must disappear by a
  collision before heat time `t_X`, since `H_{t_X}` is real there. An isolated pair of squared
  half-gap `−δ²` collides at heat `δ²/2` (the single-pair law `w² + 2t`, proved for polynomials),
  so an isolated tilt at height `X` would need `δ² ≲ 2t_X ≍ 1/log X`. Deeper tilts need a cluster of
  zeros at the heat scale `√t_X` that drives the collision. O3 asks the arithmetic image fixed in
  step 5 to exclude both: shallow tilts, which it reads only at second order through coalescent
  prime pairs below the mean spacing (`primeCoalSum_eq_oddEvenShiftPrimeCoalSum`), and colliding
  clusters. This is the arithmetic input of Q3. It must use the Euler product with the strict
  Euler bound, since for the twins the same descent fails. The calibration is exact
  (`twin_tilt_costs_weight`, `exists_twin_tilt_beyond_every_weight`). Finite pieces of the twin's
  data are on the line above their horizon, yet the twin is tilted at every height. The two facts
  are reconciled only by weights growing like `log` of the height, and the weight of `ζ` grows the
  same way. So O3 cannot be closed by the size of the prime sum, only by its cancellation.
- **The endpoint.** `Λ ≥ 0` (Rodgers–Tao): the descent cannot continue past `t = 0`. So whatever
  closes O3 must use a property that `ζ` has exactly at `t = 0`. The Euler product is such a
  property: the heat flow destroys it for `t > 0`.

**Status.** Steps 1–4 are proved in the corpus. Step 5 is proved in local form with a
non-explicit constant; making the constant explicit (O2) is analysis within reach. O1 and O3 are where RH lies. The route is not
closed. What it contributes is the split. ζ-specific domination gives reality down to heat time
`t_X`, and the pincer confines every tilt to the last stretch. The camera fixes the configuration
whose descent must be collision-free. The only arithmetic left is that this configuration has no
shallow tilt and no colliding cluster at the heat scale.

## 11. Big picture

ZCG splits the explicit formula's information into what an image *identifies*, what it can
*hide*, and what it can *certify*.

Identification is cheap and sign-free. For every `r`, a finite piece of the configuration is fixed
by the primes below `e^{2r}`, stably, and data are separated from `ζ` at their first prime. In the
function field the configuration is fixed at lag `g log q`. That is half the `2g`-lag window at
which Weil positivity is proved to decide purity.

Hiding has a price. A cancelling cluster at aperture `a` has density at least `2a/π`. Inside a
separated union it needs two points of different FE orbits closer than `π/a`, or closer than the
Ingham scale `π/(2a)` if it is shallow. Lattices, Euler columns and the lattice pair hide exactly at
these thresholds. Mimicry is a property of dense, arithmetic or crystalline structure.

Certification follows identification where identification is available. In the function field,
purity is the position of the `g` trace points, or the boundedness of the image. The configuration
of `ζ` has unbounded density: no finite aperture identifies it, and no window is blind to it. What
remains are the unbounded-aperture growth laws (AOG, SRT) and deformation. Heat and cosh tilts
contract the strip, and reality is lost only at a collision. Near a collision the camera reads the
squared gap only at second order, through the `(log n)²`-weighted prime sum. Repulsion holds in the
model families, from integrality in the function field and from the archimedean phase speed above
the horizon of an Euler stage. For `ζ` neither mechanism exists below the horizon.

For RH the programme reduces the missing step to one statement about configurations: *in the last
stretch of the heat descent, the arithmetic image excludes tilted near-collisions at every height*
(§10). The estimate routes need the same input. ZCG states it as a property of positions and gaps,
instead of a cancellation bound, a sign or a count.

## 12. Success criteria and contributions

The programme succeeds when two things hold. First, a theorem of the form "the arithmetic image at
every height excludes a tilted point" is proved without a sign of a form, a spectrum, a count or a
Hodge index. Second, that theorem separates `ζ` from twins, sparse flips, Davenport–Heilbronn,
Epstein and golden data.

A contribution must:
1. conclude a position, a relation (identification, mimicry, classification) or a continuation, not
   a sign or a count, as the decisive step;
2. name its camera (aperture, window class) and the mimicry class that camera cannot see;
3. state which arithmetic fakes it separates, and use the Euler product only through what survives
   for twins (the Ramanujan bound) or say so;
4. hold pointwise in height, or state the height dependence explicitly;
5. be unconditional in Lean, with no hypotheses that encode the missing input.
