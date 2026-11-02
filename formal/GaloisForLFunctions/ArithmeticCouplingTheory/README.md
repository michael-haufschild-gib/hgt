# Arithmetic Coupling Theory (ACoT)

Namespace `GaloisForLFunctions.ArithmeticCouplingTheory`; umbrella `ArithmeticCouplingTheory.lean`.
In the review this field was called *the sum–product Hodge theory of the scaling surface*.

## 1. Motivation

Every RH route in the corpus reads one integer, `κ = κ(K_ζ)`: the number of zeros right of the
critical line, which is the negative index of Weil's kernel `K_ζ(u) = W(B, T_{log u} B)` on `ℚ_{>0}`
(`B` the cubic spline). Three corpus results locate that integer.

1. **The index is carried by the coupling.** On a two-prime lattice `⟨p, q⟩` the kernel keeps its
   full glued index. Its canonical split into an axial (separable) part and the inter-tower coupling
   `C(u, v) = K(uv) − K(u) − K(v) + K(1)` puts all zero information in the coupling: separable
   assemblies are blind or diverge, and a continuous profile without coupling is affine
   (`AdelicKreinGeometry/TowerCoupling`).
2. **The prime side is an incidence calculus.** In prime-incidence coordinates the prime part of the
   complete Weil form is made of nonnegative divisibility counts (`CriticalScaleArithmeticRigidity`).
3. **Successor and dilation are jointly rigid**, with the sharp constant `3/4`.

All three describe how the additive structure of `ℤ` couples its multiplicative towers. Over `𝔽_q`
this coupling is geometric: the Frobenius graph couples the two factors of `C × C` and its
intersection numbers are point counts. ACoT is the corresponding theory over `ℤ`, at the level of
Hermitian forms. It asks three things of the coupling: how large it is compared with the kernel
(stability), whether it still carries the index once the separable data are removed (completeness),
and what it is made of on the prime side (incidence). It also asks which rigidity statements can
keep a deformation of coupled kernels from crossing.

The answers are mostly sharp, and they change what the coupling can be used for. The coupling is
exactly as large as the kernel, with absolute constants. It keeps every negative square while
killing every separable kernel and the constant square. On packets, the prime side is a sum of
squares of dilation jumps, and the archimedean counterterm `log N − γ` cancels the Mertens sum
exactly. None of these statements is softer than RH, and the theorems say where each mechanism ends.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Coupling | `coupling K u v` | `K(uv) − K(u) − K(v) + K(1)` on a commutative group; equals AKG's `coprimeCrossDiff` |
| Coupling Laplacian | `lap a K`, `lap a (lap b K)` | `L_a K(g) = 2K(g) − K(ga) − K(ga⁻¹)`; `L_aL_bK(1) = Σ_± C_K(a^±, b^±)` |
| Profile coupling | `profileCoupling Φ x y` | `Φ(x + y) − Φ(x) − Φ(y) + Φ(0)` for a profile in log-coordinates |
| Weil's profile | `weilProfile` | `Φ(x) = F(−x)`, `F(t) = Σ_ρ e^{t(ρ−½)} w_ρ`, so `K_ζ(u) = Φ(log u)` |
| Coupling height | `couplingHeight x y` | `max(|x|, |y|, |x + y|)`: the largest log-height a coupling sample reads |
| Mixed difference | `mixedDiff α β f` | `f(·−α−β) − f(·−α) − f(·−β) + f = (T_α − 1)(T_β − 1)f` |
| Coupling homotopy | `couplingHomotopy A K t` | `A + t(K − A)`, from a coupling-free `A` to `K` |
| Dilation pairs | `dilationPairs N` | `(k, n)`, `k, n ≥ 1`, `kn ≤ N` |
| Prime dilation form | `primeDilationForm N F` | `Σ_{kn ≤ N} (Λ(k)/k) 2F(n)F(kn)/n`: Weil's prime matrix on amplitudes `F(n)/√n` |
| Jump energy | `jumpEnergy N F` | `Σ_{kn ≤ N} (Λ(k)/k)(F(kn) − F(n))²/n ≥ 0` |
| Mertens sum, remainder | `mertensSum M`, `mertensRemainder M` | `ψ₁(M) = Σ_{k ≤ M} Λ(k)/k`; `R(M) = ψ₁(M) − log M + γ → 0` |
| Floor defect | `floorDefect N n` | `log N − log n − log⌊N/n⌋ ∈ [0, log 2]` |
| Incidence packet | `incidencePacket P b` | `F_b(n) = Σ_{p ∈ P} b_p([p ∣ n] − 1/p)`: the coherent prime sector |
| Affine incidence event | `affineEvent k h p n` | `[p ∣ kn + h] − [p ∣ n]`: the successor–dilation jump of one prime |
| Event mean, variance | `affineEventMean`, `affineEventVariance` | period mean `μ_p` and period variance `v_p ≥ 0` |
| Incidence period | `incidencePeriod P` | `∏_{p ∈ P} p`, a complete period of the coherent sector |
| Packet amplitude | `atomAmplitude F`, `packetVector F N` | `x_n = F(n)/√n`; the pole vector is `F ≡ 1` |
| Non-ratio weight, shell degree | `nonRatioWeight`, `shellDegree` | `v_{nm} = NR_{nm}/√(nm) ≥ 0`; `d_n = Σ_m v_{nm}` |
| Affine Dirichlet energy | `affineDirichlet φ c N F` | `Σ_{n,m} v_{nm}(F(n) − F(m))²`: the successor–dilation jumps at overlap |
| Frobenius kernel | `frobKernel D` | `K(n) = Σ_i β_i^n` on the rank-one scaling group of a curve datum |

## 3. Language

- **Axial / coupling-free** across `(H₁, H₂)`: `C_K = 0` on `H₁ × H₂`, equivalently
  `K(uv) = k₁(u) + k₂(v)` there. **Coupled**: anything else.
- **Antidiagonal**: the pairs `(u, u⁻¹)`. Coprime lattices never contain them; their products are dense
  near them.
- **Commensurable towers**: towers whose products hit the antidiagonal exactly, as over `𝔽_q`, where all
  degrees live in one copy of `ℤ`. Over `ℤ` prime towers are incommensurable (`2^a ≠ 3^b`).
- **Lossless**: a two-sided comparison with absolute constants and no loss in the height.
- **Coupling-complete**: vanishes on axial kernels and still determines the index.
- **Coupling form**: the Weil form on mixed-difference tests, i.e. the kernel `L_a L_b K`.
- **Incidence square**: a squared dilation jump `(F(kn) − F(n))²`; on incidence packets it is
  `b_q² [q ∤ n]`.
- **Running counterterm**: the `log N − γ` on the diagonal of the complete Weil matrix.
- **Crossing**: a parameter at which a path of Hermitian forms is degenerate.

## 4. Mechanisms

**A. Coupling calculus** (`TheCouplingCalculus`).
1. *Künneth splitting.* Against coefficients of total mass zero on both factors a kernel pairs only
   through its coupling (`sum_mul_coupling_eq`). Coupling-free is annihilation by the mixed
   augmentation ideal `I₁ ⊗ I₂` (`coupling_eq_zero_iff_annihilates`) and is separability
   (`coupling_eq_zero_iff_separable`).
2. *Characters.* `C_χ(u, v) = (χ(u) − 1)(χ(v) − 1)` (`coupling_monoidHom`). A sum over zeros has
   coupling `Σ_ρ w_ρ (u^{ρ−½} − 1)(v^{ρ−½} − 1)`; the trivial character has none.
3. *Polarization.* For `K(g) = B(f, T_g f)` with `T` an isometry of `B`,
   `C_K(u, v) = B(T_{u⁻¹}f − f, T_v f − f)` (`coupling_correlation`).
4. *Antidiagonal.* For Hermitian `K`, `C_K(u, u⁻¹) = 2(K(1) − Re K(u))`
   (`coupling_inv_of_isHermKernel`). The self-coupling of a scale is the kernel.
5. *Laplacian.* `L_aL_b K(1)` is the sum of the four couplings `C_K(a^±, b^±)` (`lap_lap_one`).
   `L_aL_b` kills every kernel that is coupling-free across subgroups containing `a, b`
   (`lap_lap_eq_zero_of_coupling_eq_zero`). Differencing never raises the index
   (`negIndex_lap_le`, `negIndex_lap_lap_le`).

**B. Stability** (`TheLocalHyersUlamInequality`, `TheCouplingIsAsLargeAsTheKernel`,
`BoundedCouplingIsTheRiemannHypothesis`, `OneTwoPrimeLatticeDecidesTheCriticalLine`,
`TheSingleLatticeCouplingOnTheFiniteStratum`, `TheConeCouplingHasNoDeepestZero`).
6. *Local Hyers–Ulam.* A map that is bounded on `[−L, L]` and `M`-approximately additive on the triangle
   box satisfies `‖ψ(x) − (x/L)ψ(L)‖ ≤ 3M` on `[−L, L]` (`norm_sub_linear_le_three_mul`). Proof: halving
   on `[−L/2, L/2]`, shifts by `L` on the outer halves, and iteration of `B ↦ B/2 + 3M/2`.
7. *Density.* A continuous bound on the coupling over a dense product of log-scales holds on the whole
   plane (`le_of_dense_prod`). A box bound on the lattice holds on the real box
   (`norm_profileCoupling_le_of_dense_box`). No Diophantine input is needed.
8. *Losslessness.* For Hermitian profiles `|Re Φ(x) − Φ(0)| ≤ g(x, −x)/2` whenever `|Re C| ≤ g` on the
   lattice (`abs_re_sub_le_of_dense`). Conversely `|C| ≤ ‖Φ(x+y)‖ + ‖Φ(x)‖ + ‖Φ(y)‖ + ‖Φ(0)‖`
   (`norm_profileCoupling_le`). On dense lattices the full complex profile is affine up to `3M`
   (`norm_sub_affine_le_of_dense_box`).
9. *One lattice, through increments* (`OneTwoPrimeLatticeDecidesTheCriticalLine`). On `⟨p⟩ × ⟨q⟩`
   the axes `aℓ_p`, `bℓ_q` are discrete, so continuity cannot act on `C` itself. It acts on the
   increments of `C`: the second difference of `C(p^a, q^b)` in `(a, b)` is the mixed difference
   `D(s) = S(s + ℓ_p + ℓ_q) − S(s + ℓ_p) − S(s + ℓ_q) + S(s)` of the spline series at
   `s = aℓ_p + bℓ_q`, and every axial term cancels. So `|C| ≤ M` gives `|D| ≤ 4M` on the dense grid
   `ℓ_pℤ + ℓ_qℤ`, hence on `ℝ` (`norm_mixedSeriesDiff_le`). The factorization
   `(2 − X − X⁻¹)(2 − Y − Y⁻¹) = (X − 1)(Y − 1)(1 − X⁻¹)(1 − Y⁻¹)` writes the coupling Laplacian as
   four translates of `D`. That Laplacian is the orbit of the mixed-difference spline
   (`orbitSeries_mixedDiff`), so the orientation rate theorem at `σ = 0` makes it blind to every
   off-line zero.
10. *The cone, read spectrally* (`TheSingleLatticeCouplingOnTheFiniteStratum`). On `ℕ × ℕ` the
   increment transfer fails: the base points `aℓ_p + bℓ_q`, `a, b ≥ 0`, are discrete. The coupling
   of a hyperbolic pair is a product of character differences (`coupling_pairKernel`). Along the ray
   `(p^n, q^{mn})` the product term `χ_ρ(pq^m)^n` dominates every axial and reflected term. Two zeros
   alias in at most one direction `m`, because a second one would make `log p/log q` rational
   (`rightChar_direction_subsingleton`). So some direction separates all zeros of a finite set
   (`exists_generic_direction`), and the top-modulus part is an almost periodic sum that would have
   to vanish.
11. *The cone, through its generating function* (`TheConeCouplingHasNoDeepestZero`). By Hermitian
   symmetry the cone bound holds on `(p^{−a}, q^{−b})`, where the second differences are
   `R(a, b) = Σ_ρ d_ρ X_ρ^a Y_ρ^b`, `X_ρ = p^{ρ−½}`, `Y_ρ = q^{ρ−½}`. If `ρ₀` has maximal real part,
   weighting by `(X_{ρ₀}p^s)^{−a}(Y_{ρ₀}q^s)^{−b}` makes the triple sum absolutely convergent, and
   `Σ_{a,b} R x^a y^b = Σ_ρ d_ρ/((1 − X_ρ x)(1 − Y_ρ y))`. The left side is bounded. On the right
   only `ρ₀` has a double pole at `s = 0`, because a second one would need
   `ρ − ρ₀ ∈ (2πi/log p)ℤ ∩ (2πi/log q)ℤ = {0}` (`eq_of_mult_eq`). Tannery's theorem gives
   `s²Σ → d_{ρ₀}/(log p log q) ≠ 0`. No genericity of directions and no finiteness is used.

**C. Completeness and selectivity** (`MixedDifferencesSeeEveryZero`, `TheCouplingFormIsSelective`,
`FlipTwinsCarryTheirIndexIntoTheCouplingForm`).
12. *Transform.* `ĥ_{f_{α,β}} = (e^{izα} − 1)(e^{izβ} − 1) ĥ_f` (`paperFT_mixedDiff`). The factor never
   vanishes at an off-line ordinate, since `Im z ≠ 0` there (`cexp_I_mul_ne_one`). So mixed
   differences see exactly the off-line zeros the test sees (`seenRightZeros_mixedDiff`).
13. *Coupling form = Laplacian.* The Weil orbit kernel of `f_{log a, log b}` is `L_aL_b` of the orbit
    kernel of `f` (`orbitKernel_mixedDiff`). Each zero's weight is multiplied by
    `(2 − e^{αs} − e^{−αs})(2 − e^{βs} − e^{−βs})`, `s = ρ − ½` (`Wsummand_mixedDiff`).
14. *Twins on the test side.* For every weight `λ` the kernel of a difference test is the second
    difference of the kernel (`weightKernel_diffTest`), and the kernel of a mixed difference is
    `L_aL_b K_λ` (`weightKernel_mixedDiff`): linearity of the Weil functional, sesquilinearity of
    the correlation, and translation covariance. No zero configuration is needed. So the corpus
    flip theorem applies to the mixed difference of any test, and the coupling forms of `ζ` and of a
    single-prime flip twin never both have finite index (`negIndex_lap_lap_zeta_eq_top_or_flip`).
15. *Windows read the flip set.* A test supported in `[−a, a]` with `2a ≤ log(1 + 1/p²)` sees one
    integer near `p` and one near `p²` (`log_one_add_inv_le_abs_log_sub`), so two weight kernels
    differ there by one atom (`weightKernel_sub_of_window`). For any set of primes `P`, the
    `(p, p)`-coupling of the `P`-flip twin differs from that of `ζ` by `−4 log p ‖f‖²/√p` if `p ∈ P`
    and by `0` otherwise (`coupling_primeSetFlip_sub_coupling_zeta`).

**D. Incidence** (`TheMertensPolarization`, `TheCompleteFormOnTheCoherentSector`,
`TheCompleteFormAtEveryOverlap`, `NonpositivePacketsAreNearlyDilationInvariant`,
`NonpositiveDirectionsLocalizeInAConductorSector`, `TheAffineIncidenceEnergy`).
16. *Mertens polarization.* `P_N(F) = Σ_{n ≤ N} F(n)²/n · (ψ₁(⌊N/n⌋) + log n) − J_N(F)`
    (`primeDilationForm_eq`). The two diagonal halves collapse because summing over `k ≤ ⌊N/n⌋` gives
    the Mertens sum and `Σ_{k ∣ m} Λ(k) = log m`. In pole coordinates this is RAPT's ground-state
    identity (`atomicWeilForm_add_poleDefect`): the jump energy is the pole defect
    (`jumpEnergy_eq_poleDefect`).
17. *Incidence squares.* For a prime power `k` with prime `q`,
    `F_b(kn) − F_b(n) = b_q [q ∈ P][q ∤ n]` (`incidencePacket_dilation_jump`), so `J_N(F_b)` counts
    nondivisibility events (`jumpEnergy_incidencePacket`).
18. *Euler cancels Mertens.* Weil's prime matrix on amplitudes `F/√n` is `P_N(F)`
    (`atomicWeilForm_atomAmplitude`). With the strictly separated decomposition of the complete
    matrix, `log N − γ − ψ₁(⌊N/n⌋) − log n = δ_N(n) − R(⌊N/n⌋)` (`log_sub_euler_sub_mertens`). This
    gives the exact identity (`completeWeilEnergy_atomAmplitude`)
    `E(F/√·) = J_N(F) + Σ F(n)²/n (s_c + e_N + δ_N(n) − R(⌊N/n⌋)) + (pole and boundary terms)`.
    Here `R → 0` (`tendsto_mertensRemainder`), `|R| ≤ log 4 + 4 + γ` (`abs_mertensRemainder_le`), and
    `0 ≤ δ ≤ log 2` (`floorDefect_nonneg`, `floorDefect_le_log_two`).
19. *Localization below touching.* The complete energy keeps a fraction `(1 − c)/4` of the pole
    defect (RAPT), which is the jump energy. Every nonpositive packet therefore has
    `J_N(F) ≤ K Σ F(n)²/n` eventually (`eventually_jumpEnergy_le_of_nonpos`). The kernel of `J_N` is
    the pole line (RAPT `poleDefect_eq_zero_iff_horizonPoleVector`).
20. *Affine incidence (sum–product).* `F_b(kn + h) − F_b(n) = Σ_p b_p D_p(n)`, with
    `D_p = [p ∣ kn + h] − [p ∣ n]` periodic modulo `p` (`incidencePacket_affine_jump`,
    `affineEvent_periodic`). Over a complete period, events of distinct primes are independent
    (Chinese remainder; `sum_range_affineEvent_mul`). So
    `mean (F_b(kn + h) − F_b(n))² = Σ_p b_p² v_p + (Σ_p b_p μ_p)²` (`affineIncidenceEnergy_eq`).
    For `p ∤ k` the event has mean zero (`affineEventMean_eq_zero`). For `p ∣ k` it has mean
    `[p ∣ h] − 1/p` (`affineEventMean_of_dvd`). Every prime dividing neither `k` nor `h` contributes
    exactly `2/p` (`affineEventVariance_of_not_dvd`). The successor shift `h` thus decouples every
    prime outside `kh`, and only the primes of `k` carry a coherent part.

21. *Every overlap.* A symmetric form is its degree diagonal minus half its Dirichlet energy
    (`sum_sum_mul_eq_degree_sub_dirichlet`). Applied to the non-ratio prime matrix of RAPT's
    every-overlap decomposition, this gives `⟨NR x, x⟩ = Σ d_n F(n)² − ½ A_N(F)`
    (`inner_nonRatio_packetVector`), with nonnegative weights for nonnegative profiles
    (`fullWeilNonRatioMatrix_nonneg`). The identity at every overlap
    (`completeWeilEnergy_packetVector_at_every_overlap`) reads
    `E = J_N + ½A_N + Σ F²/n (s_c + e_N + δ − R) − Σ d_n F(n)² + (pole, boundary, near overlap)`.
    Prime successor edges give the uniform comparison
    `½A_N(F) ≥ (1/64)[primePoleScale(⌊N/(16Q²)⌋) − primePoleScale(Q)]·nonconstantPacketMass`
    for every conductor packet through `Q≥2`, every `N≥1`, and overlap above a
    profile-dependent constant (`prime_successor_edges_control_nonconstant_packets`).
    The retained edges `(n,pn+1)` sample the coprime-successor gap and have actual weight
    at least `log p/(2N)`. The shell, pole and archimedean terms remain to be paid jointly.
22. *Conductor capture.* At every fixed overlap the complete form pays a fixed fraction of the pole
    defect (CACT), so nonpositive unit vectors have bounded jump energy
    (`eventually_poleDefect_le_of_nonpos`). Bounded jump energy is conductor structure (RAPT). Prime
    dilations have spectral gap `≍ log p` on divisibility by `p`, so only small conductors carry low
    jump energy. Hence nonpositive directions localize in a finite conductor sector
    (`eventually_nonpos_localizes_in_conductor_sector`). CACT's polynomial reserve (fraction `a/c⁷`,
    cost `Cc⁹`, valid for `N ≥ Hc⁸`) makes this uniform in the overlap: nonpositive unit vectors
    have jump energy at most `(C/a)c¹⁶` (`poleDefect_le_of_nonpos_at_growing_overlap`).

**E. Rigidity** (`TheCouplingHomotopyIsCrossingFree`).
23. *Coupling ray.* If `A` is coupling-free across `H₁, H₂`, then on `H₁H₂` the coupling form of
    `A + t(K − A)` is `t · L_aL_b K` (`lap_lap_couplingHomotopy`). It is crossing-free for `t > 0`
    (`negIndex_lap_lap_couplingHomotopy`) and vanishes at `t = 0`.

**F. Calibration** (`TheCouplingOfACurve`).
24. *Curves.* `C(a, b) = Σ_i (β_i^a − 1)(β_i^b − 1)` (`coupling_frobKernel`). Two towers of degrees
    `d₁, d₂` are commensurable: `(d₁d₂k, −d₁d₂k)` lies in `d₁ℤ × d₂ℤ`, and `C(n, −n) = 2(K(0) − K(n))`
    (`coupling_frobKernel_inv`).

## 5. Answers to the programme questions

**Q1. Size of the inter-tower coupling of `ratCorr`; cancellations forced by coprimality.**
The coupling is exactly as large as the kernel. For any two pairs of distinct primes:
`RH ⇔ sup_{⟨p,q⟩×⟨r,s⟩} |C| < ∞` (`riemannHypothesis_iff_exists_bound_coupling`, with
`riemannHypothesis_iff_exists_bound_coupling_2357` for `⟨2,3⟩ × ⟨5,7⟩`). For every `σ ≥ 0` the
growth `|Re C| = O(e^{σh})` in the coupling height is equivalent to `zero width ≤ σ`
(`zetaZeroWidth_le_iff_coupling_rate`). So the size of the coupling is the zero width, with no loss.
One lattice already decides: for the minimal prime set `S = {p, q}` (AKG's `interTowerCoupling`),
`RH ⇔ sup_{a,b ∈ ℤ} |C(p^a, q^b)| < ∞` (`riemannHypothesis_iff_exists_bound_coupling_zpow`), with no
finiteness assumption on the off-line zeros. On the cone `a, b ≥ 0` alone, boundedness forces RH
unless the zero width is not attained, i.e. unless no zero has maximal real part
(`riemannHypothesis_or_no_deepest_zero_of_bounded_coneCoupling`). In particular it forces RH on the
finite stratum (`riemannHypothesis_of_bounded_coneCoupling_of_finite`,
`riemannHypothesis_of_bounded_singleLatticeCoupling`).
Coprimality forces no cancellation in the four-window prime sum: the coupling is the profile coupling
of `Φ` at `(log u, log v)` (`coupling_zetaKernel_eq`) and depends only on these two reals. The lattices
enter only through density. Arithmetic cancellation appears only at exact incidence, i.e. for narrow
tests. There the prime form is a sum over single towers `k = q^j`
(`primeDilationForm`, Euler/Kronecker law of ACS), so coprime towers do not meet at any finite place.

**Q2. A local Hyers–Ulam inequality with polynomial constants.** Yes, and the constants do not
depend on the height. On triangle boxes the general inequality has constant `3`
(`norm_sub_linear_le_three_mul`). For Hermitian kernels the real part has constant `½`, by the
antidiagonal identity (`abs_re_sub_le_of_dense`). On two dense lattices the transfer from the lattice
to all scales is lossless and needs no Baker-type input.

**Q3. Is the complete form on the coherent sector incidence squares minus an exact Mertens term?**
Yes, exactly, at every overlap.
- Prime part: the Mertens diagonal minus the jump energy (`primeDilationForm_eq`). The jumps of
  incidence packets are nondivisibility events (`primeDilationForm_incidencePacket`).
- Complete form below touching: the archimedean `log N` and Euler's `−γ` cancel the Mertens sum.
  What remains is the Mertens remainder `R(⌊N/n⌋) → 0`, a floor defect in `[0, log 2]`, and the pole
  and boundary terms (`completeWeilEnergy_atomAmplitude`, `completeWeilEnergy_incidencePacket`).
- At overlap `c > 1`: the non-ratio pairs add a nonnegative affine incidence energy `½A_N` and
  subtract the shell degree `Σ d_n F(n)²` (`completeWeilEnergy_packetVector_at_every_overlap`).
  So the exact diagonal becomes Mertens plus shell. On incidence packets the affine jumps are sums
  of affine events, whose period energy is an exact sum of squares (`affineIncidenceEnergy_eq`).

**Q4. Do near-edge negative directions localize in the coherent sector?** Yes, at every overlap,
fixed or growing. The sector is a finite family of Ramanujan conductor profiles; its prime
conductors give the prime-incidence packets.
- At every overlap `c > 0` and every precision `η > 0`, a finite set of conductors captures every
  nonpositive unit vector within squared distance `η`, for all large `N`
  (`eventually_nonpos_localizes_in_conductor_sector`).
- Uniformly in the overlap: there is `H` such that for every `c ≥ 1` and `η > 0` one finite
  conductor set captures every nonpositive unit vector at every horizon `N ≥ Hc⁸`
  (`nonpos_localizes_uniformly_at_growing_overlap`). This covers every schedule `c ≤ (N/H)^{1/8}`,
  in particular `c ≤ (log N)^{1/4}`. The jump energy of such vectors is at most `(C/a)c¹⁶`
  (`poleDefect_le_of_nonpos_at_growing_overlap`), so in RAPT's construction the sector consists of
  divisors of a `P`-smooth modulus with `log P ≍ c¹⁶/η`.
- The mechanism: the complete form pays a fraction of the jump energy, and low jump energy means
  small-conductor structure, because prime dilations have gap `≍ log p` on divisibility by `p`. In
  packet coordinates the inequality reads `J_N + ½A_N ≤ K` at every overlap
  (`jumpEnergy_add_half_affine_le_of_nonpos`) and `J_N ≤ K` below touching
  (`eventually_jumpEnergy_le_of_nonpos`).

**Q5. Which rigidity theorems make source paths crossing-free?** At the level of kernels, none can
make the axial-to-coupled path crossing-free, because the index changes from `κ(A)` to `κ(K)`. At the
level of the coupling form, the annihilation of separable kernels by `L_aL_b` makes the same path a
positive ray. So the coupling homotopy is crossing-free for every `t > 0`, and for `ζ` on `⟨p, q⟩`
it carries exactly `κ(K_ζ)` negative squares throughout
(`negIndex_lap_lap_couplingHomotopy_zeta`). All index changes of the kernel path are axial.

**Q6. The arithmetic analogue of the self-intersection of the Frobenius graph.** Over `𝔽_q`,
`C(n, −n) = 2(2g − τ(n))` is the primitive self-intersection of `Γ_{F^n} − Δ`. Over `ℤ`, the
self-coupling of a scale is the Weil energy of the difference test,
`C(u, u⁻¹) = W(T_{u⁻¹}f − f) = 2(K(1) − Re K(u))` (antidiagonal plus polarization). On atoms its prime
content is the dilation jump energy with Hecke weight `Λ(k)/k` (Mertens polarization). On the
coherent sector this is the count `Σ b_q² Σ_{n ≤ N/q^j, q ∤ n} 1/n` of nondivisibility events: the
incidence of the dilation graph with the diagonal at the place `q`. Two coprime towers have no
finite-place incidence; their coupling is archimedean and polar.

## 6. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Künneth splitting; coupling-free = separable | `sum_mul_coupling_eq`, `coupling_eq_zero_iff_annihilates`, `coupling_eq_zero_iff_separable` | proved |
| Antidiagonal identity; polarization | `coupling_inv_of_isHermKernel`, `coupling_correlation` | proved |
| Laplacian annihilates separable kernels | `lap_lap_eq_zero_of_coupling_eq_zero`, `negIndex_lap_lap_le` | proved |
| Local Hyers–Ulam, constant 3 | `norm_sub_linear_le_three_mul`, `norm_profileCoupling_sub_linear_le` | proved |
| Lossless coupling transfer | `abs_re_sub_le_of_dense`, `norm_sub_affine_le_of_dense_box` | proved |
| Bounded coupling is RH | `riemannHypothesis_iff_exists_bound_coupling` | equivalence |
| One two-prime lattice decides RH | `riemannHypothesis_iff_exists_bound_coupling_zpow`, `norm_mixedSeriesDiff_le`, `orbitSeries_mixedDiff` | equivalence |
| The cone of one lattice excludes a deepest zero | `riemannHypothesis_or_no_deepest_zero_of_bounded_coneCoupling`, `riemannHypothesis_of_bounded_coneCoupling_of_finite`, `riemannHypothesis_of_bounded_singleLatticeCoupling` | proved |
| Coupling rate is the zero width | `zetaZeroWidth_le_iff_coupling_rate` | equivalence |
| Coupling completeness | `negIndex_orbitKernel_mixedDiff`, `orbitKernel_mixedDiff`, `negIndex_lap_lap_zetaKernel` | proved |
| RH is positivity of the coupling form | `riemannHypothesis_iff_negIndex_lap_lap_zetaKernel` | equivalence |
| Selectivity of the coupling form | `negIndex_lap_lap_orbitKernel`, `negIndex_lap_lap_golden`, `coupling_flip_sub_coupling_zeta` | proved |
| Twin kernels of difference tests; twin coupling index is a kernel index | `weightKernel_diffTest`, `weightKernel_mixedDiff`, `negIndex_lap_lap_weightKernel` | proved |
| Flip twins carry their index into the coupling form | `negIndex_lap_lap_zeta_eq_top_or_flip`, `negIndex_lap_lap_flip_eq_top_of_finite` | proved |
| The diagonal coupling recovers flip sets of every density | `coupling_primeSetFlip_sub_coupling_zeta`, `mem_iff_coupling_primeSetFlip_ne` | proved |
| Mertens polarization; incidence squares | `primeDilationForm_eq`, `jumpEnergy_incidencePacket`, `jumpEnergy_eq_poleDefect` | proved |
| Euler cancels Mertens on packets | `completeWeilEnergy_atomAmplitude`, `completeWeilEnergy_incidencePacket` | proved |
| Packet identity at every overlap; nonnegative affine weights | `completeWeilEnergy_packetVector_at_every_overlap`, `fullWeilNonRatioMatrix_nonneg`, `affineDirichlet_nonneg` | proved |
| Nonpositive directions localize in a finite conductor sector | `eventually_nonpos_localizes_in_conductor_sector`, `eventually_jumpEnergy_le_of_nonpos_at_overlap` | proved |
| Localization uniform in the overlap | `nonpos_localizes_uniformly_at_growing_overlap`, `poleDefect_le_of_nonpos_at_growing_overlap` | proved |
| Nonpositive packets are nearly dilation-invariant | `eventually_jumpEnergy_le_of_nonpos` | proved |
| Affine incidence energy is a sum of squares | `affineIncidenceEnergy_eq`, `affineEventMean_eq_zero`, `affineEventVariance_of_not_dvd` | proved |
| Crossing-free coupling homotopy | `negIndex_lap_lap_couplingHomotopy`, `negIndex_lap_lap_couplingHomotopy_zeta` | proved |
| Curve calibration | `unitary_iff_bounded_tower_coupling`, `spanHodgeIndex_iff_bounded_tower_coupling`, `not_bounded_tower_coupling_golden` | proved |
| EHT threshold read by the coupling form; no edge = bounded coupling | `forall_positiveAt_width_iff_couplingForm`, `eventually_hyperplaneEdge_eq_top_iff_bounded_coupling` | proved / equivalence |
| ACoT packets are CSAR prime-incidence packets | `incidencePacket_eq_normalizedConductorPacket` | proved |

## 7. Tools

**Developed.**
- Coupling calculus on commutative groups: Künneth pairing, separability, characters, polarization,
  antidiagonal, Laplacian with Gram identity (`hermQuad_gram_lap`).
- Local Hyers–Ulam on triangle boxes; density transfer on boxes and with continuous gauges.
- Profile form of Weil's kernel (`weilProfile`, `weilProfile_neg`, `coupling_zetaKernel_eq`) and dense
  log-scales of two-prime lattices (`dense_range_logScale_twoPrimeLattice`).
- Mixed-difference tests: transform, visibility, orbit-kernel identity, summability of shifted zero
  sums (`summable_cexp_mul_Wsummand`).
- Packet coordinates for the complete Weil matrix: dilation pairs and their fibration
  (`sum_dilationPairs_eq`), the divisor half of Weil's prime kernel (`divisorKernel`), Mertens
  polarization, incidence jumps, Mertens remainder and floor defect.
- Affine incidence events and their period calculus: independence of distinct primes over complete
  periods (`sum_range_mul_of_coprime`, `sum_range_affineEvent_mul`), exact counts of affine residues
  (`sum_range_dvd_affine`).
- Coupling homotopy and its ray identity.
- Frobenius kernels of curve data and tower couplings.
- Interfaces (`TheCouplingInterfaces`): the EHT threshold at width `w` is the positivity of the
  coupling form of the atom, and "no edge" is bounded coupling; ACoT incidence packets are CSAR's
  normalized conductor packets with prime-incidence coefficients.

- Laplacian polarization of symmetric forms and its packet form for the non-ratio matrix; shell
  degree and affine Dirichlet energy; nonnegativity of non-ratio weights.
- Conductor capture of nonpositive directions, at fixed overlap and uniformly in the overlap.
- The increment transfer on one lattice: axial cancellation in the second difference of the coupling,
  density of `ℓ_pℤ + ℓ_qℤ`, and the factorization of the coupling Laplacian into mixed differences
  (`norm_mixedSeriesDiff_le`); real-time orbit series of mixed-difference tests
  (`orbitSeries_mixedDiff`).
- Twin calculus: kernels of difference tests for arbitrary weights (`weightKernel_diffTest`), the
  sesquilinear correlation of differences (`weilTest_sub_sub`), and the one-atom window comparison
  of two weights (`weightKernel_sub_of_window`).

- The cone generating function: absolute convergence below the deepest zero, the double-pole
  extraction by Tannery's theorem, and separation of double poles by irrationality of
  `log p/log q` (`eq_of_mult_eq`, `tendsto_cdiv_one_sub_exp`, `mul_one_sub_exp_le`).

**To build.**
- A sampling theorem for exponential sums on the cone `ℕℓ_p + ℕℓ_q` whose top exponent is not
  attained (topic 1 below).
- A sum–product inequality for the shell degree against the affine incidence energy on conductor
  packets (topic 2 below).

## 8. Open research topics

1. **The cone when the zero width is not attained.** On the whole lattice `⟨p⟩ × ⟨q⟩` bounded
   coupling is RH (mechanism 9). On the cone `a, b ≥ 0` it excludes every zero of maximal real part
   (mechanism 11). So the only case left is infinitely many off-line zeros whose real parts
   approach their supremum `½ + Θ` without reaching it. The generating function cannot settle that
   case alone, for two reasons.
   - A weight that isolates a zero below the supremum makes the sums over the deeper zeros diverge.
   - On `Re w > Θ` the series `Σ_ρ d_ρ g(w − ρ + ½)` agrees with a function holomorphic on all of
     `Re w > 0`, while its poles accumulate on `Re w = Θ` from the left. Series of poles with summable
     residues can agree with a holomorphic function across their accumulation set (Wolff's series
     `Σ A_n/(z − a_n)` vanishing outside the disc), so analytic continuation does not force the
     residues to vanish.

   The positive survivor is `riemannHypothesis_or_no_deepest_zero_of_bounded_coneCoupling`. Closing
   the case needs input specific to `ζ`: a lower bound for the spline weights of the zeros that
   approach the supremum, played against their spacing modulo `2π/log p` and `2π/log q`.
2. **The sign on the non-ratio sector.** Every positivity statement of the theory is an identity
   or an equivalence, and the sign of the coupling form is RH
   (`riemannHypothesis_iff_negIndex_lap_lap_zetaKernel`). On packets the ratio part is a sum of
   jump squares, the Mertens and archimedean diagonals cancel, and nonpositive directions live in a
   finite conductor sector. What carries the sign is the non-ratio, successor–dilation part
   `½A_N − Σ d_n F(n)²` on that sector. A sum–product inequality bounding the shell degree by the
   affine incidence energy on conductor packets is the mechanism the theory points to.

**Questions handed to neighbouring programmes.** ACoT reduces each of the following exactly to a
question that is native to another programme.
- *Sector size at growing overlap* (CACT). Localization holds uniformly in the overlap, and the
  jump energy of nonpositive directions is the cost-to-fraction ratio of CACT's reserve:
  `(C/a)c¹⁶` from fraction `a/c⁷` and cost `Cc⁹` (`poleDefect_le_of_nonpos_at_growing_overlap`). The
  conductor cutoff `log P ≍ c¹⁶/η` improves exactly as CACT's reserve exponents do.
- *Coupling index of a flip twin off the finite stratum* (HKT). The coupling index of a twin at `f`
  is the twin's kernel index at the mixed difference of `f` (`negIndex_lap_lap_weightKernel`). The
  selectivity question of ACoT is closed by the diagonal coupling
  (`mem_iff_coupling_primeSetFlip_ne`) and by the dichotomy `negIndex_lap_lap_zeta_eq_top_or_flip`.
  The corpus's unconditional negative directions for finite flip sets come from conductor blocks.
  These have low jump energy and are nearly dilation-invariant, the part that `L_aL_b` removes, so
  they do not transfer by themselves.

## 9. Traps

| Trap | Truth |
|---|---|
| Bounded inter-tower coupling is a softer target than a bounded kernel | It is the same with absolute constants (`abs_re_sub_le_of_dense`); bounded coupling is RH |
| Baker-type density constants are needed to transfer the coupling | No Diophantine input is needed anywhere: on two lattices continuity acts on the coupling, on one lattice on its increments, and on the cone irrationality alone separates the double poles |
| One lattice cannot decide because its axes are discrete | The axial terms cancel in the second difference, which lives on the dense grid |
| The cone needs generic directions or finitely many zeros | Its generating function has a double pole only at the deepest zero, by irrationality of `log p/log q`; only an unattained zero width escapes |
| Coprimality forces cancellation in the four windows | The coupling depends only on `(log u, log v)`; arithmetic cancellation lives only at exact incidence |
| Killing the separable part loses the zeros | The coupling form keeps every seen right zero (`negIndex_orbitKernel_mixedDiff`) |
| A positive coupling form is new positivity | It is RH (`riemannHypothesis_iff_negIndex_lap_lap_zetaKernel`) |
| The Mertens polarization is a new identity | It is RAPT's ground-state identity in packet coordinates (`jumpEnergy_eq_poleDefect`) |
| Incidence positivity of the prime side is positivity of the form | The prime part enters with a minus sign; positivity needs the diagonal and pole terms |
| The coherent sector is the prime-incidence span | Low jump energy captures all small conductors, composite ones included; the sector is a finite conductor family |
| Localization is a soft statement | It is a theorem at every overlap with an explicit jump-energy bound `(C/a)c¹⁶`; the size of the sector is what the reserve exponents control |
| Flip twins are invisible to a coupling-free test | The diagonal coupling at `(p, p)` changes by exactly `−4 log p ‖f‖²/√p` for every flipped `p`, at every density |
| Separable data approximate the correlation | Separable assemblies annihilate the coupling (AKG) |
| Noncrossing along the axial-to-coupled path | Only on the coupling form; the kernel path must cross |
| Positive point counts force the sign | The golden curve has them and an infinite coupling index |

## 10. Context

| Programme | Interface |
|---|---|
| `AdelicKreinGeometry/TowerCoupling` | `coprimeCrossDiff` = `coupling`; coupled/axial assemblies; ACoT supplies the stability and completeness of the coupling |
| `RenormalizedIntersectionTheory` | spline series, bounded-kernel criterion; ACoT proves its coupling form (A16 of the review) |
| `ArithmeticOrientationGeometry` | spline-orbit and orientation rate theorems, used for the coupling rate and for the one-lattice decision |
| `HeckeKreinToeplitz` | orbit kernels, index law, two-prime lattices, golden curve, weight kernels and the flip theorem on the finite stratum |
| `ArithmeticCountingPositivity`, `RenormalizedIntersectionTheory` (flip twins) | `primeSetFlip` for prime sets of any density; ACoT reads the flip set from the diagonal coupling |
| `RenormalizedArithmeticPotentialTheory`, `CriticalArithmeticCorrelationTheory` | complete Weil matrix, ground-state identity, strictly separated decomposition |
| `CriticalScaleArithmeticRigidity` | prime-incidence coordinates, coherent receiving mode, joint rigidity |
| `ArithmeticCastelnuovoSeveri`, `ArithmeticPositiveDuality` | curve data, golden datum, power-sum bounds, Kronecker law |
| `EdgeHodgeTheory` | the threshold curve and the edge, read by the coupling form (`forall_positiveAt_width_iff_couplingForm`, `eventually_hyperplaneEdge_eq_top_iff_bounded_coupling`) |

In the obstacle map ACoT closes the work item A16 (RH ⇔ bounded coupling in Lean) and answers Q2 of
§2.3 and 2.5.2. It turns Σ-6 and Σ-7 into exact reformulations, and states the coherent-sector part of
Q1(a) as an identity in the strictly separated regime.

## 11. Success and contribution criteria

The programme meets the criteria of the review as follows:
1. coupling-completeness: proved (§4.C, §4.E);
2. stability with explicit constants: proved, with constants `3` and `½`;
3. incidence positivity with the pole entering only through Mertens' constant and the counterterm:
   proved below touching. At every overlap the prime side is ratio and affine incidence squares, with
   nonnegative weights, minus the Mertens and shell diagonal (§4.D);
4. edge validity: the positivity and transfer statements are identities or stability theorems;
   only the localization below touching inherits RAPT's eventual defect reserve;
5. calibration over `𝔽_q`: proved, and the golden datum fails;
6. rigidity output: dilation-neutral packets are the pole line, and the coupling homotopy is
   crossing-free;
7. selectivity: the coupling form counts seen right zeros of every tempered configuration; it never
   has finite index for both `ζ` and a flip twin; and the diagonal coupling recovers the flip set of
   every twin, at every relative density.

A contribution must be an unconditional Lean theorem about explicitly defined coupling, incidence or
rigidity objects that does one of three things: (a) proves an identity or inequality with explicit
constants; (b) answers a question of §5 or a topic of §8; (c) closes a mechanism with an exact
obstruction together with its strongest positive survivor. Renaming an existing identity does not
count. The bridges to existing identities (`jumpEnergy_eq_poleDefect`) are recorded so that this
cannot happen silently.

## 12. Big picture

Coupling theory removes the separable part of Weil's kernel and keeps everything that counts. The
coupling is as large as the kernel, carries all its negative squares, and on packets its prime side is
a count of nondivisibility events. Within the theory these facts close three hopes:
- a bounded or slowly growing coupling would be a zero-free strip of matching width;
- a positive coupling form would be RH;
- an incidence identity cannot settle the sign by itself, because the prime side enters with a minus
  sign.

The theory therefore relocates the problem rather than softening it. Its six questions are answered:
the coupling is the kernel, one two-prime lattice decides, stability is lossless without Diophantine
input, the complete form is an exact incidence identity at every overlap, nonpositive directions live
in a finite conductor sector at every overlap, and the coupling separates `ζ` from every flip twin.
What none of these supplies is the sign of the coupling form, which is RH. Any further mechanism has
to act on the non-ratio, successor–dilation part of the form, the only place where the additive and
multiplicative structures of `ℤ` meet.
