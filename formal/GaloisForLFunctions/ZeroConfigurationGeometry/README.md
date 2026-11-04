# Zero Configuration Geometry (ZCG)

Namespace `GaloisForLFunctions.ZeroConfigurationGeometry`; umbrella `ZeroConfigurationGeometry.lean`;
25 modules.

## 1. Motivation

The explicit formula is usually read as a sum rule. Either one asks for the sign of the result
(Weil positivity), or one asks how many zeros it certifies on the line (proportion theorems). This
programme excludes both as the decisive step: no positivity of a form, no spectral realization, no
count of zeros, no Hodge index.

ZCG reads the explicit formula as a **camera** instead. A window `f` supported in `[−r, r]` produces
an exact image of the zero configuration (the Weil form, or the Gram matrix of a grid of modulated
windows), and the primes below `e^{2r}` compute that image. RH says where the imaged points lie. The
field asks four questions of the image, none of them about a sign:

- **identification**: when does the image determine the configuration?
- **mimicry**: which configurations share an image, and what shape do they have?
- **certification**: which properties of images force every point onto the real curve?
- **deformation**: how can a point leave the real curve along a family?

Identification turns out to be cheap and sign-free. Certification is the hard part, and the
programme locates exactly where it leaves the sign-free world.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Camera of aperture `r` | `ApertureWindow r` | `C²` windows supported in `[−r, r]` |
| Zero coordinate, depth | `Zeta23.gammaOf`, `depth` | `γ_ρ = (ρ − ½)/i = γ − iδ`, `δ = β − ½` |
| Tilt | `tilt δ f` | `f·e^{δu}`; a point of depth `δ` is a real point of the tilted camera |
| Pair, squared gap | `paperFT_add_add_sub` | FE pair `c ± w`, `w²` real: real pair `w² > 0`, collision `w = 0`, tilted pair `w = iδ` |
| Pair signal, depth signal | `pairSignal`, `depthSignal` | pair minus doubled centre; `depthSignal f x δ = pairSignal f x (iδ)` |
| Second-moment image | `secondMoment` | `(u² f)^(c)` |
| Point image, modification image | `pointImage`, `modImage` | `f̂(γ_z) conj ĝ(conj γ_z)`; its sum against a finite signed multiplicity |
| Differential window | `annihilate z g`, `exists_annihilating_window` | `g' + izg`; transform multiplied by `−i(w − z)` |
| Derivative mass, inverse bound | `derivMass`, `annihilatorBound` | `M_k = ∫|b^{(k)}|`; `Σ_{U ⊆ T} (∏_{T∖U} |z|) M_{k+|U|}` |
| Arithmetic image | `arithmeticImage λ f` | full Weil functional of `f ⋆ f̃` for arithmetic data `λ` |
| Prime channel | `primeChannel λ k` | `Σ_n λ(n) n^{−1/2} (k(log n) + k(−log n))` |
| Prime discrepancy | `primeDiscrepancy λ λ' r` | `Σ_{n ≤ e^{2r}} |λ(n) − λ'(n)|/√n` |
| Frobenius configuration | `CurveDatum`, `spectrum` | `2g` normalized eigenvalues closed under conjugation and `β ↦ β⁻¹` |
| Column, Euler column | `offLineLatticeConfig`, `eulerColumnCoeff` | vertical lattice of spacing `2π/L`; zeros of `1 + Ap^{−s} + p^{1−2s}` |
| Trace point | `norm_eq_one_iff_tracePoint` | `β + β⁻¹` |
| Fakes | `pureDatum`, `goldenRootDatum` | roots of `x^{2g} + 1` and of `x^{2g} − 3x^g + 1` |
| Collision | `IsCollision` | a real common root of `p` and `p'` |
| Heat flow, spread | `heatFlow`, `spread` | `e^{−tD²}` on polynomials; `n Σ x_j² − (Σ x_j)² = Σ_{j<k} (x_j − x_k)²` |
| Strip of depth `b` | `RootsInStrip b p` | all roots satisfy `|Im z| ≤ b` |
| Modulated window | `modulate T f` | `f(u)e^{−iTu}`: the camera moved to height `T` |
| Cosine camera | `cosineWindowTransform` | transform of `cos(2θs)` on `[−½, ½]` at complex frequency |

## 3. Language

- A camera **identifies** a class when equal images force equal configurations.
- Two configurations are **mimics** at aperture `r` when every window of aperture `r` gives the
  same image. Their difference is a **cancelling cluster**.
- The **identification threshold** of a class is the least aperture that identifies it. The **sign
  threshold** is the least aperture at which Weil positivity decides reality. The gap between them
  is the **certification gap**.
- **Depth is tilt**: the image sees depth only through `cosh(δu)` and `sinh²(δu/2)` in the window.
- A point is **pinned** by arithmetic data when no finite modification of the configuration keeps
  the arithmetic image.

## 4. Mechanisms

**The camera.**
1. *Depth is tilt.* `f̂(x − iδ) = (f e^{δu})^(x)`. Every zero is a real point of the camera tilted by
   its depth. In the matrix explicit formula, the Gram summand of a zero is the rank-one block of the
   tilted taper at its real ordinate.
2. *Pairs are analytic in the squared gap.* `f̂(c + w) + f̂(c − w) = (2cos(wu) f)^(c)`, even in `w`.
   An FE pair `{ρ, 1 − ρ̄}` is its real centre seen through `2cosh(δu)`.
3. *The depth signal.* A tilted pair minus its doubled centre is the centre seen through
   `4 sinh²(δu/2)`. At aperture `r` its size is at most `4 sinh²(δr/2) ∫|f|`, and every value below
   this is attained by a smooth window of unit mass. Depth enters quadratically when `δr ≪ 1` and
   like `e^{δr}` when `δr ≫ 1`.
4. *The squared gap is read at second order.* For `|w| r ≤ 1`:
   `|pairSignal + w² M₂| ≤ (5/48)|w|⁴ r⁴ ∫|f|`. A real pair of gap `Δ` and a tilted pair of depth `Δ`
   differ in image by `−2Δ² M₂ + O(Δ⁴r⁴)`. Since `M₂ = −f̂''`, a near-collision is imaged as
   `2f̂(c) + w² f̂''(c)`: reality is the sign of the coefficient of the image's curvature in the
   height variable. At height `T` the kernel is `e^{−iTs} k(s)`, the prime channel is a Dirichlet
   polynomial of length `e^{2r}`, and its height curvature is minus the prime channel of
   `s² k_T(s)`: the `(log n)²`-weighted prime sum. This is the coalescent channel, stated as an exact
   identity.

**Identification.**
5. *Finite modifications are seen at every aperture.* The image difference of two tempered
   configurations differing in finitely many points is the finite sum `Σ c_z f̂(γ_z) conj ĝ(conj γ_z)`.
   Polarization reduces off-diagonal images to diagonal ones. The fundamental lemma and the identity
   theorem turn the vanishing of `Σ a_z f̂(γ_z)` for all windows into the vanishing of the exponential
   polynomial `Σ a_z e^{iγ_z u}`, hence of every coefficient. So cancelling clusters are infinite.
   On the line they also need near-collisions: by Ingham's inequality, distinct on-line mimics at
   aperture `a` contain two points closer than any `g > π/(2a)`. Hiding lives where the image
   reads gaps only at second order. With tilts, Ingham's inequality survives with explicit
   constants. The kernel `∫ cos(at) e^{(σ+ix)t} = 2a cosh((σ + ix)T)/((σ + ix)² + a²)` gives, for
   `g`-separated heights and tilts `|σ_j| ≤ s`, the lower bound `(2a/a'²)(1 − cosh(2sT)B')Σ|c_j|²`,
   with `a'² = a² + 4s²`. Tilts below `~1/T` are resolved like real frequencies, and deeper tilts
   cost `cosh(2sT)`. An FE pair `γ ∓ iδ` is one site with a `2×2` block whose smallest eigenvalue,
   the pair gap `A(2δ) − A(0)`, is positive and of order `δ²` (since `π²/2 > 4`). This gives the
   block inequality for pairs. Fed into the lag structure of two-bump tests it gives the tilted
   near-collision constraint: two distinct mimics at aperture `a > V/2` contain two points of
   different FE orbits closer than `g`, or a point deeper than `s`, or an off-line point shallower
   than `ε`, whenever `(16π²/9) a_V² a'² cosh(2sV) < (π² − 8) ε² g²`. A shallow pair is a
   near-collision of the pair with itself, resolved only against sites at distance `≍ 1/ε`. For a
   real even window the two coefficients of a pair are `cQ` and `cQ̄` with `Q = κ̂(γ − γ₀ − iδ)²`.
   The block degenerates only in the antialigned direction, which these coefficients reach only in
   the dark sector `Re κ̂⁴ < 0`. Since a tilt by `δ` moves `κ̂_w` by at most
   `(e^{|δ|w} − 1)‖κ_w‖₁`, the dark sector lies where the camera is dim.
   The degeneration itself is an artifact of the basis. Writing a pair as
   `P cosh(δv) + R sinh(δv)/(δV)`, `P = p + q`, `R = Vδ(p − q)`, the two profiles are orthogonal
   for the weight `cos(av)`, with `∫ cos(av) cosh² ≥ 2/a` and `∫ cos(av)(sinh(δv)/δ)² ≥
   ∫ cos(av) v² = 2V²/a − 4/a³ > 0` (again `π² > 8`), uniformly in `δ`. Two integrations by parts
   make every off-diagonal entry `O(B/x²)` with `B = O(1/V)`. So resolution is uniform in depth:
   mimics at aperture `a > V/2` with depths `≤ 1/V` contain two points of different FE orbits
   closer than `90/V`, or a deeper point. Shallow pairs hide nothing.
6. *Differential windows invert the camera.* `(g' + izg)^(w) = −i(w − z)ĝ(w)`. Composing these
   operators over the other points of a finite modification gives a window, of any aperture, that
   reads one coefficient exactly: `W_Z(f, g) − W_{Z'}(f, g) = c(z₀) ∏_{z ≠ z₀} (−i(γ_{z₀} − γ_z))`.
   The inverse is conditioned by the product of the gaps, depths included. Its mass is at most
   `annihilatorBound`: each operator costs one derivative of the base window and one factor `|γ_z|`.
   With integer multiplicities this gives quantitative identification. If two images agree to
   precision `ε` per unit window masses and `ε · annihilatorBound · e^{|Im γ_{z₀}| r}` is smaller
   than `∏_{z ≠ z₀} |γ_{z₀} − γ_z|`, the configurations agree at `z₀`. Modulating the windows to a
   height `T` replaces `γ_z` by the offsets `γ_z − T`, so the precision depends only on the local
   geometry of the cluster and is uniform in height.
7. *The primes pin every finite piece of `ζ`.* The arithmetic image at aperture `r` depends on
   `λ(n)` only for `log n < 2r`. Combined with the unconditional explicit formula, any data agreeing
   with `Λ` below `e^{2r}` fix every finite piece of the zeros of `ζ`. The pinning is stable: data
   `λ` with prime discrepancy `D_r(λ, Λ)` change the image of a kernel by at most `2D_r sup|k|`.
   So a configuration produced by `λ` agrees with `ζ` at every point of a finite modification whose
   gap product exceeds `2D_r · annihilatorBound · sup|g|`, at every height.
8. *Function-field identification.* With `∏ β = 1`, Newton's identities give `e_1, …, e_g` from
   `t_1, …, t_g`, and inversion symmetry gives `e_{2g−k} = e_k`. The camera reads `t_m` for
   `m log q < 2a` (two-bump tooth `2(t_0 − t_m)`), so aperture `a > g log q/2` identifies the
   configuration. Mimics at aperture `a` are exactly the data with equal traces below lag `2a`.
   Purity is then a function of the image: equal images above lag `g log q` force equal purity,
   and purity is the position of the trace points `β + β⁻¹` in `[−2, 2]`. Certification happens
   at the identification threshold, without a sign.

**Arithmetic fakes.**
9. *Ramanujan is reality.* In `x = p^{−s}`, the factor `1 + Ap^{−s} + p^{1−2s}` is a real reciprocal
   quadratic. A zero has `Re s = ½` iff `A² ≤ 4p`; otherwise `2cosh(δ log p)√p = |A|`. For curves
   (`p = 1`): `|β| = 1` iff the trace point `β + β⁻¹` is real and lies in `[−2, 2]`.
10. *Euler columns are lattices.* With `A_δ = −2√p cosh(δ log p)` the zero set is exactly
   `{½ ± δ + 2πik/log p}`. It has the image of the doubled on-line lattice at every aperture
   `≤ log p/2`. The first lag at which it differs is `log p`, where the signal is `|A_δ|/√p`.
   The threshold is sharp: above aperture `log p/2` the two-bump window at lag `log p` gives the
   column the image `4 log p ‖κ‖²(1 − cosh(δ log p)) ≠ 0` and the on-line lattice `0`. For a lattice
   pair of Riemann–von Mangoldt density at height `T` (`L = ½ log(T/2π)`) and the matrix camera of
   exponent `λ`, mimicry holds iff `λ ≤ ½`, for every depth and height.

**Deformation.**
11. *Reality leaves only through collision.* A real-rooted polynomial of degree `n` with simple
    roots stays real-rooted under small perturbations: sign changes persist, and the intermediate
    value theorem keeps `n` distinct real roots. Coefficient limits of real-rooted polynomials of
    bounded degree are real-rooted. So along a continuous family whose leading coefficient never
    vanishes, the first exit from reality happens at a real double root.
12. *Heat time spreads the configuration.* `e^{−tD²}` keeps the coefficients of `xⁿ`, `x^{n−1}` and
    lowers that of `x^{n−2}` by `t n(n−1)`. By Vieta the centre is fixed and
    `Σ_{j<k} (x_j − x_k)²` grows exactly by `2n²(n−1)t`. For one pair the squared half-gap moves as
    `w² + 2t`, so a tilted pair of depth `δ` collides at `t = δ²/2` and is real afterwards. For a
    real configuration the total squared gap is a sum of squares, so it cannot become negative:
    backward heat time `S/(2n²(n−1))` already forces a non-real point.
    Pointwise, heat steps never shrink the mesh. At a root `y` of `p + cp'` the logarithmic
    derivative `Σ_k 1/(y − x_k)` equals `−1/c`, so two roots `y < y'` give
    `Σ_k 1/((y − x_k)(y' − x_k)) = 0`. If `y' − y` were below the mesh `μ` of `p`, at most one `x_k`
    lies between them, contributing `−1/(uv)`; the others contribute at most the telescoping sums
    `1/(dv)` and `1/(du)`, `d = u + v`, whose total is `1/(uv)`. Simplicity survives because
    `(p + cp')' = −cp Σ_k 1/(y − x_k)²` at a root. Also no Laguerre step deepens a configuration. At a new root `z` of `p + cp'` outside
    the strip of `p`, `p'/p(z) = Σ 1/(z − z_k)` would have imaginary part of one strict sign while it
    equals the real number `−1/c`. Hence `p − c²p'' = (1 − cD)(1 + cD)p` keeps the strip: the
    maximal depth never increases along the discrete heat flow. One step cannot contract strictly:
    a triple root on the edge of the strip, as in `(x − ib)³(x + ib)³`, survives every step.
    The strict law comes from shift averages (de Bruijn's lemma). The cosh-tilted window
    `2cosh(λu)φ` has transform `f(z + iλ) + f(z − iλ)`. For a conjugation-closed configuration of
    depth `≤ Δ`, every root of the shift average is real or has `(Im z)² + λ² ≤ Δ²`. Each
    conjugate pair factor `g(Y) = |w − ζ|²|w − ζ̄|²` satisfies
    `g(y + λ) − g(y − λ) = 8yλ((x − a)² + y² + λ² − b²) > 0` above the contracted strip. A tilt
    `λ ≥ Δ` makes every zero real. Iterated averages of sizes `μ_j` (the tilt `∏ cosh(μ_j u)`)
    lower the squared depth from `D` to `max(D − Σ μ_j², 0)`. For window transforms the continuum
    limit `∏ cosh → e^{tu²}` is `RHTower.DeBruijn.cosTransform_heat_zeros_im_sq_le`. There the zero
    strip of `∫ g(x)e^{izx} dx` contracts to `max(Δ² − 2t, 0)` under the heat tilt `e^{tx²}`, and
    for `ζ` this is `riemannHeat_zeros_im_sq_le`, i.e. `Λ ≤ ½`.

**Window design.**
13. *The cosine camera has only real kernel zeros.* At complex frequency the window transform
    satisfies `((πζ)² − θ²)K(ζ) = πζ sin(πζ) cos θ − θ sin θ cos(πζ)`. Its zeros solve
    `z sin z = (θ tan θ) cos z`. For `z = u + iv` this forces
    `(u² + v²) sinh v cosh v = −C v|cos z|²`, impossible when `v ≠ 0` and `C > 0`. The complex
    additive-triple question therefore reduces to the real one. Against a whole real configuration:
    for the lattice `hℤ` and any aperture `r > π/h`, the window `b(u + π/h) − b(u − π/h)` has
    transform `−2i sin(πw/h) b̂(w)`, which vanishes on the lattice and at no point off it where
    `b̂ ≠ 0`. A single window then separates every tilted point from the lattice, at exactly the
    threshold where tilted columns of spacing `h` stop hiding.
14. *Shifts multiply the transform by exponential polynomials.* `Σ_k c_k b(u + ν_k)` has transform
    `(Σ_k c_k e^{−iwν_k}) b̂(w)` and costs `max|ν_k|` in aperture. So every real zero set of an
    exponential polynomial of width `W` is blinded at every aperture `> W`. Products of the factors
    `sin(π(w − τ_j)/h_j)` blind finite unions of lattices of total density `D` at every aperture
    `> πD`, the Jensen bound. Convolving the bump with a density `φ` on `[−W, W]` multiplies its
    transform by `∫ φ(t) e^{−iwt} dt`, which blinds zero sets such as those of `J₀`. Blindness is
    bought by width, not by separation. Linear factors cost nothing: the differential window
    `g' + iκg` multiplies the transform by `−i(w − κ)`, and at a zero `κ` of `f̂` the solution of
    `g' + iκg = f` vanishes outside the support of `f` (above it, it equals `e^{−iκu} f̂(κ) = 0`).
    Dividing a blind window at a simple zero gives an isolating window: one camera of the density
    aperture sees a chosen lattice point and no other. For one lattice
    nothing cheaper exists: below `π/h` the periodization of a blind window has vanishing Fourier
    coefficients and non-overlapping translates, so the window is zero.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Depth is tilt; Gram block of a zero | `paperFT_gammaOf`, `Gsummand_eq_tilted` | unconditional |
| Pairs analytic in the squared gap | `paperFT_add_add_sub`, `paperFT_gammaOf_add_reflect`, `paperFT_realPair_eq_cos` | unconditional |
| Depth signal, sharp | `depthSignal_eq`, `norm_depthSignal_le`, `exists_depthSignal_ge` | unconditional |
| Second-order law; curvature form | `norm_pairSignal_add_sq_mul_secondMoment_le`, `norm_realPair_sub_tiltedPair_le`, `deriv_deriv_paperFT_eq_neg_secondMoment`, `norm_pairSignal_sub_sq_mul_curvature_le` | unconditional |
| Finite modifications seen at every aperture | `eq_of_weil_eq_on_aperture_of_finite`, `infinite_modification_of_mimic` | unconditional |
| Hiding needs near-collisions (on-line) | `exists_near_pair_of_onLine_mimic` | unconditional |
| Ingham's inequality with tilts; block inequality for pairs | `tiltedKernel_eq`, `tilted_ingham_inequality`, `pairGap_pos`, `block_ingham_inequality`, `eq_zero_of_pairSum_eq_zero` | unconditional |
| Tilted resolution; shallow pairs are near-collisions | `eq_of_weil_eq_of_pairSeparated`, `pairGap_ge`, `tiltB_le`, `exists_near_pair_or_shallow_pair_of_mimic` | unconditional |
| Aligned pairs; the dark sector lies where the camera is dim | `pairWeight_modScaledBump_eq_sq`, `not_inDarkSector_of_bright`, `exists_near_pair_or_dim_shallow_pair_of_mimic` | unconditional |
| Resolution is uniform in depth, at the Nyquist scale | `uniform_block_inequality`, `norm_integral_cos_mul_mul_cexp_le`, `eq_of_weil_eq_of_heightSeparated`, `exists_near_pair_of_mimic`, `exists_near_pair_of_mimic_of_le` | unconditional |
| Explicit inverse by differential windows | `paperFT_annihilate`, `exists_window_sum_eq_coeff_mul_gaps`, `exists_windows_W_sub_W_eq` | unconditional |
| Quantitative identification, uniform in height | `exists_annihilating_window_bound`, `norm_multDiff_mul_gaps_le`, `multDiff_eq_zero_of_precision`, `norm_multDiff_mul_gaps_le_at_height` | unconditional |
| Primes pin finite pieces of `ζ` | `arithmeticImage_congr_of_eq_below`, `eq_zeta_of_arithmeticImage_of_finite` | unconditional |
| Coalescent channel = height curvature of the prime channel | `weilTest_modulate`, `primeChannel_modulate`, `deriv_deriv_primeChannel_modulate` | unconditional |
| Stable arithmetic pinning | `norm_weilFullFunctional_sub_le`, `norm_multDiff_mul_gaps_le_of_arithmetic`, `multDiff_eq_zero_of_arithmetic_precision` | unconditional |
| Function-field identification at `g log q` | `spectrum_eq_of_powerSum_eq`, `spectrum_eq_of_weil_eq_on_aperture` | unconditional |
| Mimic column clusters = equal low traces | `curveConfig_weil_eq_iff_trace_eq` | unconditional |
| Pure and totally tilted mimics up to `g log q` | `identification_threshold_sharp` | unconditional |
| Function-field certification at the identification threshold | `pure_iff_of_powerSum_eq`, `pure_iff_of_weil_eq_on_aperture` | unconditional |
| Square-root threshold for columns of RvM density | `rvmLattice_mimic_iff` | unconditional |
| Ramanujan is reality | `localFactor_zero_depth`, `localFactor_zero_re_eq_half_iff`, `curveDatum_pure_iff_tracePoints` | unconditional |
| Euler columns hide below their prime | `localFactor_eulerColumnCoeff_eq_zero_iff`, `eulerColumn_mimics_onLineLattice`, `no_bounded_aperture_excludes_eulerColumns` | unconditional |
| Sharp separation of lattices and Euler columns | `offLineLattice_separated_above_nyquist`, `offLineLattice_mimic_iff`, `eulerColumn_mimic_iff` | unconditional |
| Collision exit | `eventually_splits_of_simple`, `isClosed_splits`, `exists_first_collision` | unconditional |
| Laguerre steps never deepen; sharp for one step | `rootsInStrip_add_smul_derivative`, `rootsInStrip_heatStep`, `heatStep_keeps_triple_edge_root` | unconditional |
| Shift averages contract the depth (de Bruijn's lemma), iterated rate | `pairFactor_lt`, `im_eq_zero_or_sq_add_sq_le_of_shiftAverage`, `roots_shiftAvgList_im_sq_le` | unconditional |
| Heat steps never shrink the mesh | `sum_le_sum_range_of_sep`, `sum_inv_mul_ne_zero`, `meshGe_add_smul_derivative`, `nodup_roots_add_smul_derivative`, `eval_derivative_derivative_eq`, `iterate_heatStep` | unconditional |
| Heat-time spread law; bounded backward exit | `coeff_heatFlow_sub_two`, `sum_sq_roots_heatFlow`, `spread_roots_heatFlow`, `exists_nonreal_root_heatFlow` | unconditional |
| Windows blind to a lattice | `paperFT_shift`, `exists_window_blind_to_lattice` | unconditional |
| Blind windows at the density aperture; exponential-polynomial zero sets | `apertureWindow_expPoly`, `exists_window_blind_to_expPoly_zeros`, `exists_window_prod_sine`, `exists_window_blind_to_lattices` | unconditional |
| Windows blind to zero sets of transforms of densities | `densityTransform`, `integrable_mul_cexp_of_support`, `exists_window_blind_to_densityTransform_zeros` | unconditional |
| Division at transform zeros; isolating windows | `exists_window_div`, `exists_isolating_window`, `exists_window_isolating_lattice_point` | unconditional |
| The lattice threshold `π/h` is sharp | `tsum_add_int_eq_zero_of_fourier_eq_zero`, `eq_zero_of_blind_to_lattice`, `exists_window_blind_to_lattice_iff` | unconditional |
| Cosine camera: real zeros, complex additive rigidity | `im_eq_zero_of_cosineWindowTransform_eq_zero`, `no_complex_additive_zero_triple` | unconditional, `0 < θ < π/2` |

## 6. Questions and what the programme answers

- **Q1 Identifiability.** Finite modifications are identified at every aperture, without a sign
  and constructively: one pair of differential windows reads each coefficient, multiplied by the
  product of the gaps to the other points. The required precision is explicit (gap product over
  inverse-window mass and `e^{|Im γ| r}`), depends only on the offsets of the cluster from its
  height, and with approximate prime data it is the prime discrepancy below `e^{2r}`: only
  near-collisions can absorb prime-side error. Frobenius configurations are identified exactly
  above lag `g log q`. A single pair carries a depth signal of exactly `4 sinh²(δr/2)` per unit
  mass. Against column mimics of Riemann–von Mangoldt density the least identifying exponent of the
  matrix camera is `λ = ½`, uniformly in depth and height (`rvmLattice_mimic_iff`). Against all
  other mimics the depth-uniform resolution gives an exponent of order one: if the union is
  separated, apart from FE partners, at a fraction `c` of the mean spacing `2π/L` and the depths are
  at most `2πc/(90L)`, the image at every aperture above `V/2`, `V = 90L/(2πc)`, identifies the configuration
  (`exists_near_pair_of_mimic_of_le`). *Open:* mimics whose unions have near-collisions below a
  fixed fraction of the mean spacing; the exponent for those is the coalescent question Q3.
- **Q2 Cancelling clusters.** Finite clusters never cancel. On-line cancelling clusters at aperture
  `a` contain near-collisions at every scale above `π/(2a)`, and the lattice pair attains it.
  Column clusters of a common spacing cancel at aperture `a` exactly when their traces agree below
  lag `2a`. Euler columns and lattices cancel against on-line lattices exactly below their dual
  frequency. Off the line, a cancelling cluster at aperture `a` contains two points of different
  FE orbits closer than `g`, or a point deeper than `s`, as soon as `D(V) > 2π²B(V, s)/(3g²)`
  (`exists_near_pair_of_mimic`). The scale depends on the aperture and the depth budget only:
  for depths `≤ 1/V` it is `90/V` (`exists_near_pair_of_mimic_of_le`). Resolution is uniform in
  depth, and shallow pairs hide nothing. In the basis `e^{±δv}` the same argument only gave the
  scale `g ≳ 1/ε` for pairs of depth `≥ ε`, with a dim-camera refinement; that loss was the
  basis. So hiding needs a near-collision in height. *Open:* the optimal constant, between the
  `90/V` proved here and the column mimics, which hide at separation `π/V`.
- **Q3 Sub-spacing geometry.** Near a collision the camera reads the squared gap linearly, as the
  coefficient of the height curvature `f̂''` of the image; real against tilted is the sign of that
  coefficient, to relative precision `(Δr)²`. Through the explicit formula the height curvature of
  the prime channel is exactly the `(log n)²`-weighted prime sum below `e^{2r}`. *Open:* the
  arithmetic input itself, control of this weighted prime sum at every height.
- **Q4 Deformation.** In finite dimension, reality is lost only at a real double root. In heat time
  the total squared gap grows at the exact rate `2n²(n−1)`, so a real configuration of total
  squared gap `S` loses reality before backward time `S/(2n²(n−1))` (the averaged Lehmer bound,
  exact for one pair); pointwise, every heat step keeps a real configuration real and simple and
  never shrinks its least gap (`iterate_heatStep`); a single pair moves as `w² + 2t`; no
  discrete heat step increases the maximal depth, while every shift average (cosh tilt of the
  window) strictly contracts it, `Δ² ↦ Δ² − λ²`. Iterated, this gives de Bruijn's rate, and for
  window transforms the continuum heat tilt contracts the zero strip to `Δ² − 2t`
  (`cosTransform_heat_zeros_im_sq_le` in RHTower). Forward heat time is thus repulsive both on
  average and pointwise, while backward time is bounded: the least time at which a finite real
  configuration of total squared gap `S` is real is at least `−S/(2n²(n−1))`. RH is the statement
  that the configuration of `ζ` is still real at time `0` of the backward flow. *Open:* a repulsion
  law that reaches tilt `0`, i.e. reality of `ζ` itself, along backward heat time or Euler depth.
- **Q5 Window design.** The cosine camera of the proportion engine has only real kernel zeros for
  `0 < θ < π/2`, so additive rigidity holds over `ℂ`. Against the real lattice `hℤ` every aperture
  `> π/h` has a window blind to the lattice and seeing any given tilted point. The same holds for
  every finite union of lattices `τ_j + h_jℤ` with arbitrary, possibly incommensurable spacings, at
  every aperture `> πD`, `D = Σ_j 1/h_j` (`exists_window_blind_to_lattices`). This is the least
  aperture that Jensen's formula allows for density `D`, and no separation is needed. For one
  lattice the threshold is proved sharp: at aperture `≤ π/h` every window blind to `hℤ` vanishes
  (`exists_window_blind_to_lattice_iff`, by Poisson summation). More
  generally every configuration inside the real zero set of an exponential polynomial of width `W`
  has, at every aperture `> W`, a window blind to it that sees any given non-zero of the polynomial
  (`exists_window_blind_to_expPoly_zeros`), and so has every configuration inside the zero set of
  `Φ(w) = ∫ φ(t) e^{−iwt} dt` for an integrable density `φ` on `[−W, W]`
  (`exists_window_blind_to_densityTransform_zeros`). The latter class contains perturbed lattices
  such as the zeros of `J₀`, of density `1/π`, blinded at every aperture `> 1 = πD`. *Open:*
  configurations of positive density inside no such zero set; there, sufficiency needs sine-type
  functions and a converse Paley–Wiener theorem. Isolation also costs no aperture: for every
  `r > π/h` one window sees exactly one point of `hℤ` (`exists_window_isolating_lattice_point`).
- **Q6 Selectivity.** Euler columns at `p` are mimics of on-line lattices at aperture `a` exactly
  when `a ≤ log p/2`, and are excluded only by the Ramanujan bound at `p`. Bounded apertures exclude
  no infinite family of twins, while the family of all apertures excludes each twin at the first
  aperture beyond its prime. The golden root datum, with no point on the circle, mimics the pure
  datum exactly up to lag `g log q`.
- **Q0 Certification.** In the function field, purity is certified at the identification threshold
  by the positions of the trace points. For `ζ`, see §10.

## 7. Tools

**Developed.**
- Tilt calculus, the pair formula for complex gaps, exact depth and pair signals with sharp bounds,
  and a second-order Taylor law with explicit constant.
- Differential windows with prescribed transform zeros: exact coefficient extraction, mass bounds,
  modulation to any height, and the prime-discrepancy bound for arithmetic data.
- Polarization for finite signed modifications, exponential independence on an interval, smooth
  windows with prescribed transform value, and the aperture-congruence lemma for arithmetic data.
- Ingham's inequality with tilts (the tilted kernel in closed form), the pair gap with its
  quadratic lower bound, the block inequality for FE pairs with the aligned-coefficient gap, a
  Schur bound for symmetric off-diagonal kernels, the resolution of vanishing pair sums by
  truncation, and the tilt-perturbation bound `‖f̂(x − iδ) − f̂(x)‖ ≤ (e^{|δ|r} − 1)‖f‖₁`.
- The profile basis `cosh(δv)`, `sinh(δv)/δ` of an FE pair, uniform Gram bounds for it, and the
  double integration by parts `‖∫ g e^{ixv}‖ ≤ (|g'(V)| + |g'(−V)| + ∫|g''|)/x²` for `g(±V) = 0`.
- Newton and inversion reciprocity for Frobenius spectra, root-of-unity configurations with
  vanishing low traces, and the reciprocal-quadratic root lemma.
- Sign-change persistence and closedness of real-rootedness along families; the heat operator on
  polynomials with its coefficient law; the logarithmic-derivative strip argument for Laguerre
  steps and the pair-factor argument for shift averages; the second logarithmic derivative
  `p''/p = φ² − Σ 1/(y − x_k)²`, one-sided counting sums over separated points, and the telescoping
  bound behind mesh monotonicity.
- Closed forms for the cosine transform at complex frequency and for lattice-blind windows;
  exponential and sine multipliers of windows (shifts multiply the transform by an exponential
  polynomial at the cost of its width in aperture); Poisson periodization of Fourier-blind
  windows; convolution with densities; division of a window at a transform zero.

**To build.**
- The optimal resolution scale `g(V, s)` of the depth-uniform constraint.
- Kernel design against real configurations of positive density inside no zero set of the
  transform of a compactly supported density (sine-type functions, converse Paley–Wiener).

## 8. Traps

| Trap | Truth |
|---|---|
| Visibility means a negative Weil form | Identification is sign-free; finite modifications are seen at every aperture, while negativity is guaranteed only beyond a logarithmic aperture (`finiteOffLine_visible`) |
| A cluster can hide in a bounded region | Finite modifications never hide; hiding needs infinitely many points |
| An image matching the on-line shadow certifies the line | Lattices, Euler columns and band-limited modulations hide below their dual frequency |
| Bounded bandwidth excludes arithmetic fakes | For every aperture some prime carries Euler columns of every depth that hide |
| Depth is read at first order | The depth and gap signals are quadratic near a collision |
| Certifying reality needs a sign | In the function field, identification at lag `g log q` certifies purity by the positions of the trace points; Weil positivity is proved to decide only with `2g` lags (`curveConfig_weil_nonneg_iff_unitary_of_card_le`) |
| Identification certifies reality for `ζ` too | No finite aperture identifies the zeros of `ζ`: lattice columns of RvM density hide up to `λ = ½`, and infinite mimics beyond columns are not classified |
| Reality can leave the line smoothly | Only through a collision, a real double root |
| Euler products separate `ζ` from twins at finite resolution | Only the Ramanujan bound at each prime does |
| Each heat step contracts the depth | Laguerre steps only keep the strip, since a multiple edge root survives a step; shift averages are the steps that contract strictly |

## 9. Context

| Direction | Programmes (module imports) |
|---|---|
| Uses | RHTower 7, SquareRootThreshold 5, ArithmeticCastelnuovoSeveri 3, HTGeometry 3, SelbergClass 1, IncommensurableGaborPinching 1, Zeta23 |

| Neighbour | Interface |
|---|---|
| Zeta23 | `ZeroConfig`, `paperFT`, `gammaOf`, Weil form, Gram summands of the matrix explicit formula |
| SquareRootThreshold | `multDiff`, `eq_of_multDiff_eq_zero`, `TemperedConfig`, lag-tooth lemma, support of autocorrelations; the sign-based visibility apertures that ZCG contrasts with identification |
| RHTower | vertical lattices and their Nyquist blindness; unconditional bilinear explicit formula; exponential independence; identity theorem on intervals; de Bruijn–Newman collision criterion as the `ζ` counterpart of the exit theorem; de Bruijn's strip contraction for entire window transforms (`DeBruijn.add_shift_ne_zero`, `cosTransform_heat_zeros_im_sq_le`) as the continuum counterpart of the shift-average laws |
| ArithmeticCastelnuovoSeveri | curve data, curve configurations and their lag formula; summability of Weil summands |
| HTGeometry | Newton identities, multiset determination, closedness of real-rootedness |
| SelbergClass | reciprocal Euler factors of the positive twins |
| IncommensurableGaborPinching | cosine kernel and its real additive rigidity |
| ArithmeticOrientationGeometry | growth-rate and index laws, the unbounded-aperture certificates that §10 refers to |

## 10. Big picture

ZCG splits the explicit formula's information into what an image *identifies* and what it can
*certify*.

Identification is cheap and sign-free. A finite piece of the configuration is fixed by the primes
below `e^{2r}` for every `r`. In the function field the configuration is fixed at lag `g log q`,
half the `2g`-lag window at which Weil positivity is proved to decide purity, and the golden root
datum shows that positivity cannot decide below lag `g log q`. Mimicry is a property of infinite
arithmetic structure: lattices, crystals, and the Euler columns of twins. These hide exactly below their dual
frequency. An Euler column at `p` is separated from an on-line lattice only by the Ramanujan bound
at `p`, read at lag `log p`.

Certification follows identification where identification is available. In the function field
the camera at lag `g log q` determines the configuration, and purity is then the position of the
`g` trace points in `[−2, 2]`: certification is sign-free and happens at half the window that Weil
positivity is known to need. For `ζ` the configuration is infinite and no finite aperture identifies
it. Columns of the zeros' density hide up to `λ = ½`, and infinite mimics beyond columns are not
classified, so the positional certificate is unavailable. What remains are the unbounded-aperture
growth laws (AOG, SRT) and deformation: the cosh and heat tilts, which contract the zero strip and
make every configuration real at tilt `≥` its depth (de Bruijn), together with the exit theorem,
which says reality is lost only at a collision. Near a collision the camera reads the squared gap
only at second order, through the `(log n)²`-weighted prime sum. Every route therefore needs the
same arithmetic input: control of that coalescent channel, uniformly in height.

Hiding itself is now located. Two configurations with one image at aperture `a` differ only
through a near-collision in height between different FE orbits, a point deeper than the depth
budget (`exists_near_pair_of_mimic`). Shallow pairs are no obstruction: resolution is uniform in
depth. Every obstruction is a near-collision in height.

For RH the programme reduces the missing step to one statement about configurations: *the
arithmetic image excludes tilted near-collisions at every height*. The estimate routes need this
same input. ZCG states it as a property of positions and gaps instead of a cancellation bound, a
sign or a count.

## 11. Success criteria and contributions

The programme succeeds when a theorem of the form "the arithmetic image at every height excludes a
tilted point" is proved without a sign of a form, a spectrum, a count or a Hodge index, and when
that theorem separates `ζ` from twins, sparse flips, Davenport–Heilbronn, Epstein and golden data.

A contribution must:
1. conclude a position, a relation (identification, mimicry, classification) or a continuation, not
   a sign or a count, as the decisive step;
2. name its camera (aperture, window class) and the mimicry class that camera cannot see;
3. state which arithmetic fakes it separates, and use the Euler product only through what survives
   for twins (the Ramanujan bound) or say so;
4. hold pointwise in height, or state the height dependence explicitly;
5. be unconditional in Lean, with no hypotheses that encode the missing input.
