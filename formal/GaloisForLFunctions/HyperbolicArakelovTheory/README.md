# Hyperbolic Arakelov Theory of Spec ℤ (HAT)

Namespace `GaloisForLFunctions.HyperbolicArakelovTheory`; umbrella `HyperbolicArakelovTheory.lean`.
Source: [review 0811, §2.8 and §2.13](../../../docs/reports/review-0811/obstacles-summary.md).
Programme card: [hat-hyperbolic-arakelov-theory.md](../../../docs/drafts/pipeline/1-in-progress/hat-hyperbolic-arakelov-theory.md).

Everything in this folder is unconditional. A theorem whose name starts with
`riemannHypothesis_iff_` is an equivalence, not a proof of RH.

## 1. Motivation

Weil's proof of the Riemann hypothesis for a curve `C` over `𝔽_q` is a sign on a surface: the
graphs `Γ_n` of the powers of Frobenius on `C × C` satisfy the Castelnuovo–Severi inequality
`D² ≤ 2 (D·H)(D·V)`, and on the plane `⟨Γ_0, Γ_n⟩` this inequality is the Hasse–Weil bound.
Arakelov theory completes an arithmetic surface over `Spec ℤ` by archimedean fibres that carry
Green functions; intersection numbers become a finite part plus an archimedean part, and the Hodge
index theorem survives (Faltings, Hriljac). Manin observed that for Schottky-uniformized fibres the
Arakelov Green function is computed by geodesics of a hyperbolic handlebody: the archimedean place
behaves like a three-dimensional hyperbolic fibre.

The corpus has found this structure for the missing surface `Spec ℤ × Spec ℤ`. Between the Frobenius
graphs `Γ_m, Γ_n` (atoms of Weil's distribution at `log m`, `log n`)

  `√(mn)·W(m, n) = (m + n) − Γ_m·Γ_n`,   `Γ_m·Γ_n = (Γ_m·Γ_n)_fin + (Γ_m·Γ_n)_∞`,

* the **pole** `m + n` is the bidegree pairing, a class of rank two;
* the **finite part** `G(m, n)·I(m, n)` is the gcd-twisted intersection of the Galois orbits of
  roots of unity on `ℙ¹_ℤ`, equal to `√(mn)·Λ(n/m)(n/m)^{−1/2}` when `m ∣ n`, and an Abel limit of
  positive torsion energies;
* the **archimedean part** is `2π√(mn)·G_{1/2}(d(z_m, z_n))`, where `G_s(d) = e^{−(s−1)d}/(4π sinh d)`
  is the Green function of `Δ − s(2 − s)` on hyperbolic three-space `ℍ³` and `z_n = (0, n)` are
  points of one vertical geodesic; the dilation `x ↦ nx` is translation along that geodesic.

So the surface of `Spec ℤ` has an Arakelov model whose fibre at infinity is `ℍ³` with one marked
geodesic. HAT builds this surface only as far as Weil's proof needs it — divisors, an intersection
pairing, a diagonal, Riemann–Roch, an ample class, the Hodge index — and decides which hyperbolic
geometries can carry it. Its topological branch asks for the cohomological shadow of the same
proof: Möbius cancellation as the vanishing of a middle cohomology of an orientation cover.

**Main conjecture (hyperbolic Hodge index).** The coupled-damping pairing on the divisors of the
hyperbolic Arakelov surface `S` is negative semidefinite on primitive classes; on `⟨Γ_1, Γ_n⟩` it is
Hasse–Weil at every integer degree, i.e. RH.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Upper half-space, isometries | `SurfaceOfSpecZ.H3`, `h3Act`, `h3Dist`, `h3Cosh`, `SL2C` | `ℍ³ = {(z, t) : t > 0}`, Poincaré extension of `SL₂(ℂ)` |
| Degree geodesic, degree points | `degPoint`, `natPoint` | `ℓ = {z_t = (0, t)}`; `z_n` for `n ∈ ℕ₊` |
| Arakelov coordinates, image distance | `imageCosh` | `cosh d(z_t, γz_u) = ½(‖a‖²r + ‖d‖²r⁻¹ + ‖b‖²P⁻¹ + ‖c‖²P)`, `r = u/t`, `P = tu` |
| Green functions | `hyperbolicGreen`, `archProfile`, `greenOfCosh` | `G_s`; `2πG_{1/2}(d) = e^{−d/2}/(1 − e^{−2d}) = Σ_k e^{−(2k+½)d}`, also as a function of `cosh d` |
| Spherical functions | `sphericalFn` | `φ_ν(d) = sinh(νd)/(ν sinh d)`, Laplace eigenvalue `1 − ν²` |
| Classes of `S` | `frobeniusIntersection`, `weilDeltaKernel`, `archKernel`, `weilPrimeKernel`, `orbitIntersection`, `gcdTwist` | graphs `Γ_n`, fibres `H, V` with `Γ_n·H = 1`, `Γ_n·V = n`; defect `δ(D, E) = d₁(D)d₂(E) + d₂(D)d₁(E) − D·E` |
| Compensation | `archCompensation` | `C_∞ = pole − archimedean` |
| Archimedean damping | `dampedFrobenius`, `causalJetWave`, `dampedJet` | PSD kernels `√(mn)e^{−d/2}/(1 − r²e^{−2d})`; Gram kernels of causal waves on `L²(0, ∞)` |
| Finite damping | `torsionEnergy`, `twistedEnergy` | `Σ_k (r^k/k) c_m(k)c_n(k)`, gcd-twisted |
| Locked kernel | `lockedKernel` | pole − archimedean damping at `r` + torsion damping at `ρ(r)` |
| Carriers | `carrierSum`, `endWeight`, `EndpointEisenstein`, `ResonanceFree`, `dilationLimit`, `BoundedGeometryAt` | twisted Green sum `F(t, u) = Σ_i w_i·2πG_{1/2}(d(z_t, γ_i z_u))`, its endpoint weight and dilation limit |
| Groups | `Nontriv`, `conjEquiv`, `poincareWeight`, `basePoint` | `Γ∖{1}`, conjugation, Poincaré weight `e^{−d(z_1, γz_1)/2}` at `s = ½` |
| Self-energy along the degree ray | `rayWeight`, `selfEnergy` | `D_Γ(t) = Σ_{γ≠1} e^{−d(z_t, γz_t)/2}`, dominated by the regularized diagonal of the automorphic Green function |
| Boundary of a group | `mobius`, `WanderingEnd`, `MapsOff`, `IsParabolic` | Möbius action on `ℂ`; `∞ ∈ Ω(Γ)`; parabolic elements (trace `±2`, not `±1`) |
| Kernels on quotients | `IsNewtonian`, `CuspExpansion` | unbounded on merging points; zero modes `t^{½}, t^{3/2}` in a cusp with Wronskian `b₁ ≠ a₂` |
| Trees | `treeAdj`, `treeEigen`, `treeGreen` | radial adjacency of the `(q+1)`-regular tree; `λ_s = q^s + q^{1−s}`; `G_s(d) = q^s/(q^{2s} − 1)·q^{−sd}` |
| Smoothed graphs | `splineCycle`, `zetaScalingDatum.orbitCorr` | cubic spline `B`; `c_B(log n) = Γ_1·Γ_n` smoothed; genus `c_B(0)/2` |
| Windows | `windowThreshold` | tests supported in `[−A, 0]`; `windowThreshold A = ⊤` for `A ≤ 181/250` |
| Orientation covers | `factorOrientationCover`, `coefficientOrientationCover`, `primeQuadraticOrientationCount` (RIAC); `coverDefect` | Möbius as point defect over `𝔽_q[T]`; over ℤ the real points of `disc(primeQuadraticPolynomial n)`, `1 + μ(n)` of them; centred count `D(N) = M(N)` |

## 3. Language

- **Degree point** `z_n`; **degree geodesic** `ℓ`; **dilation** = translation along `ℓ`; **rotation** =
  elliptic isometry fixing `ℓ` pointwise.
- **Arakelov coordinates** of `γ = (a b; c d)`: `(‖a‖², ‖b‖², ‖c‖², ‖d‖²)`; **ratio** `u/t` and **product**
  `tu` of a pair of degree points.
- **Archimedean / finite intersection**: the two parts of `Γ_m·Γ_n`.
- **Ratio kernel** (Hecke kernel): a kernel on degrees depending only on `n/m`. **Jump**: a
  discontinuity of a ratio kernel at the logarithm of a prime power.
- **Carrier**: a hyperbolic realization of part of `Γ_m·Γ_n` by Green functions of a quotient of `ℍ³`
  or by a twisted image sum. **End** of `ℓ`: the boundary point `∞` that the degrees approach.
- **Endpoint weight** `ω(γ)`: `‖c‖⁻¹` off the stabilizer of the end, `min(‖a‖, ‖a‖⁻¹)` on it;
  **endpoint Eisenstein condition** `Σ ω(γ_i) < ∞`. **Resonance-free ratio**: no stabilizer element
  translates `ℓ` by `−log r`.
- **Dilation limit**: the limit of `F(Mt, Mu)` as `M → ∞`. **Bounded geometry at `(M, pM)`**: no image
  of `z_{pM}` hits `z_M` and the untwisted Green majorant is bounded.
- **Self-energy** of a degree point: `D_Γ(t)`; an end has **bounded self-energy** if `D_Γ(M) ≤ C` for
  infinitely many degrees. **Point of discontinuity** (wandering end): `{‖z‖ > R}` meets its image
  under finitely many elements.
- **Cusp expansion** of a kernel on a cusped quotient: Fourier expansion in the horizontal variables;
  **zero mode** `t^{½}, t^{3/2}` in each variable; **Wronskian** = the jump of the Green function.
- **Damping** `K_r → K` (`r → 1`) by PSD kernels; **counterterm**: a divergent diagonal subtraction;
  **locking**: running the two channels at matched radii so that their divergences cancel;
  **coupled damping**: a PSD damping of the whole pairing.
- **Genus of a smoothing**: half the self-defect of a smoothed graph, `g = c_B(0)/2`; **atomic genus**:
  the least genus that makes the atomic defect nonnegative on degrees `≤ N`.
- **Ample class**: the pole plane `⟨H, V⟩`; **primitive class**: orthogonal to `H` and `V`.
- **Hyperbolic Hodge index**: `δ ≥ 0` on the span of the (smoothed) graphs.
- **Orientation cover**, **point defect**, **local index**, **Lefschetz localization**; **weight** of a
  cover: the exponent `w` with centred count `D(N) = O(N^{w+ε})`; **purity**: weight `½` (topological
  branch).

## 4. Mechanisms

**Built on (corpus).**
1. *The `ℍ³` identity.* `archKernel m n = 2π√(mn)·G_{1/2}(|log(n/m)|)`; `G_s` solves the radial
   equation; `4πd·G_s(d) → 1` (`SurfaceOfSpecZ.archKernel_eq_hyperbolicGreen`).
2. *Two half-products.* `Γ_m·Γ_n = min/(1 − (min/max)²) + G(m, n)I(m, n)` (`frobeniusIntersection_eq`).
3. *Two positive dampings and a rank-two pole* (`dampedFrobenius_posSemidef`, `tendsto_dampedFrobenius`,
   `sum_sum_twistedEnergy_nonneg`, `tendsto_compensation_add_twistedEnergy`).
4. *Primes are jumps.* No continuous ratio kernel equals the Frobenius intersection
   (`not_exists_continuous_heckeKernel`).
5. *Genus.* Atomic genus `≍ N log N`, carried by the jets; smoothed genus `c_B(0)/2`; Hasse–Weil at every
   integer degree of the smoothed graphs ⇔ RH (`riemannHypothesis_iff_hasseWeil_integerDegrees`).
6. *Zonotope Hodge index.* Over `𝔽₁` the defect is `2Σ_k(Σ_{n>k} a_n)²` (`zonotopeDefect_eq`).
7. *Hyperbolic exclusions* (SOSZ). Only rotations about `ℓ` preserve the profile; Robin constant `¼`
   against `log p`; finite-volume vertical carriers fold or diverge at cusps; atomic counterterm-free
   diagonals `≥ N(log N − 17)/8`; RH ⇔ a counterterm-free PSD damping of `c_B`.
8. *Windows.* `windowThreshold A = ⊤` for `A ≤ 181/250`.

**Proved here.**
9. *Image distances* (`h3Cosh_degPoint_h3Act`, `imageCosh_eq`). The Lagrange identity
   `‖bd̄ + ac̄u²‖² + u²‖ad − bc‖² = (‖a‖²u² + ‖b‖²)(‖c‖²u² + ‖d‖²)` gives
   `cosh d(z_t, γz_u) = ½(‖a‖²r + ‖d‖²r⁻¹ + ‖b‖²P⁻¹ + ‖c‖²P)`. Images with `c ≠ 0` recede with the
   product; the stabilizer of the end acts on the ratio alone, `cosh d → cosh|log(‖a‖²r)|`.
10. *Dilation limits* (`tendsto_carrierSum`). Under the endpoint Eisenstein condition, along pairs with
    ratio `→ r` and product `→ ∞`, `F → L(r) = Σ_{c_i = 0} w_i·2πG_{1/2}(|log(‖a_i‖²r)|)`: seen from
    the end, every such carrier is a Manin–Schottky periodization of the archimedean Green function
    over the stabilizer, a ratio kernel continuous at resonance-free ratios.
11. *The ratio mechanism* (`not_carrierSum_eq_torsion`, `not_carrierSum_eq_torsion_of_boundedGeometry`).
    The torsion kernel jumps by `Λ(p)/√p` between `(M, pM)` and `(M, pM + 1)`; a carrier with a
    dilation limit, or with bounded geometry, moves by `o(1)` there. Bounded geometry works through a
    Newtonian lower bound (a bounded majorant keeps every image at distance `≥ h(B)`) and the
    log-Lipschitz bound `X|g′(X)| ≤ (1 + 1/h)²g(X)` of `g = 2πG_{1/2}(arcosh X)`.
12. *Spherical structure* (`two_cosh_half_eq_spherical`, `archProfile_eq_spherical`,
    `compensation_eq_spherical`). `2cosh(d/2) = (3/2)φ_{3/2} + ½φ_{1/2}` and
    `2πG_{1/2} = 2πG_{3/2} + ½φ_{1/2}`; the complementary-series piece cancels in the compensation,
    `C_∞ = (3/2)φ_{3/2} − 2πG_{3/2}`, and `C_∞ < 0 ⇔ e^{3d} < e^d + 1` (`compensation_neg_iff`): the
    plastic ratio is where the pole's `ν = 3/2` component overtakes the standard Green function.
13. *Locking gives the discriminant* (`tendsto_lockedKernel_self_sub`,
    `not_eventually_posSemidef_lockedKernel`). For any reparametrization the locked diagonal is
    `D(1) − I(n, n)/φ(n)`, the Arakelov self-intersection of torsion orbits; the atomic wall excludes it.
14. *The finite places are trees* (`treeGreen_resolvent`, `treeEigen_eq_iff`,
    `weilPrimeKernel_mul_pow_eq_treeGreen`, `weilDeltaKernel_mul_pow`). `(λ_s − A)G_s = δ_0` on the
    `(p+1)`-regular tree; `λ_s ≥ 2√p` with equality exactly at `s = ½` (the critical line is the
    Ramanujan edge); Weil's `p`-kernel is `log p·((p−1)/√p)·G_{1/2}(k)` along a `p`-ladder. So Weil's
    off-diagonal kernel is the pole minus the local Green kernels of all places (adelic Green formula).
15. *Poincaré domination and the self-energy of the end* (`exists_gap`, `summable_greenOfCosh_imageCosh`,
    `exists_prime_nonsingular_of_diag`, `not_carrierSum_eq_torsion_of_loxodromic`,
    `not_carrierSum_eq_torsion_of_selfEnergy`, `selfEnergy_le_of_near_orbit`). Convergence of the
    Poincaré series at `½` bounds the Green majorant at every pair no image hits; resonant primes have
    `Σ 1/p < ∞`. At a degree `M` of self-energy `≤ C` only `C e^{½}√P` elements move `z_M` by at most
    `1 + log P`; each comes near `z_{pM}` for at most one prime `p ≤ P`, and the primes outnumber them
    (Chebyshev). So bounded geometry holds along a prime ratio. A conical return has self-energy
    `≤ e^R S`.
16. *The boundary* (`not_summable_poincareWeight_of_parabolic`, `endpointEisenstein_of_wandering`).
    A parabolic `γ` has `γ^k = ±(1 + kN)`, `N² = 0`, and a harmonic Poincaré series, so convergence at
    `½` excludes parabolics. At a point of discontinuity every element outside a finite set has
    `‖a‖, ‖d‖ ≤ R‖c‖` and `‖c‖ ≥ 1/(2R + 1)` (test points near the pole `−d/c`), which is the
    endpoint Eisenstein condition.
17. *Finite volume* (`not_eq_frobenius_of_finiteVolume`). With a proper height, degrees of bounded
    height cluster (Newtonian singularity). Degrees that escape put infinitely many points in one cusp.
    Boundedness of the target along pairs of ratio `→ ∞` kills the zero mode `A u^{½} + B u^{3/2}` at
    every lower point, then its coefficients, against the Wronskian of the Green function.
18. *The orientation cover has weight `≥ ½`* (`coverDefect_omega`, `riemannHypothesis_iff_coverDefect_le`).
    The centred count of the discriminant cover over ℤ is `M(N)`. Zeros on the critical line make it
    `Ω_±(√N)`, and weight `½` is Littlewood's criterion.

**Calibration (classical).** Over `𝔽_q(T)` every place, `∞` included, is a tree, and Weil's local
kernel at a place of norm `N` is `log N·N^{−j/2}`, the tree Green function at the Ramanujan edge as in
`weilPrimeKernel_mul_pow_eq_treeGreen`. For `ℙ¹` the local kernels add up to the pole exactly, because
`Σ_{deg P^j = k} deg P = q^k` and `∞` contributes `q^{−k/2}`: genus zero, defect zero. For a curve of
genus `g` the defect is the sum over the `2g` Frobenius eigenvalues and Castelnuovo–Severi is its sign
(ACS). Over `ℤ` the archimedean fibre is `ℍ³` rather than a tree; its jets are the trivial zeros, and
the zonotope (`𝔽₁`) realizes the pole plane and the cusp term `min(m, n)` of `ℍ³`, with Hodge index
`2Σ_k(Σ_{n>k} a_n)² ≥ 0` by counting (`zonotopeDefect_eq`).

**What remains to discover, and its strength.**
- The **diagonal of a smoothing.** For smoothings the archimedean channel locks with itself: the
  Lévy–Khintchine form of Weil's functional has the `ℍ³` Green function as Lévy density and needs no
  counterterm. A damping that makes the whole smoothed form positive is RH (SOSZ).
- **Riemann–Roch on `S`.** In the axiomatics of ACS, Hodge index holds iff some effective cone satisfies
  Riemann–Roch and the ampleness of the pole (`PolarSurface.exists_effectivity_iff_hodgeIndex`), and
  on the scaling surface Hodge index is RH (`scalingSurface_hodgeIndex_iff`): an `h⁰` with Riemann–Roch
  and the ample pole is RH-strength. The genus of a smoothing is half its Weil energy, the weighted
  number of zeros `Re Σ_ρ m_ρ h(γ_ρ) conj h(γ̄_ρ)` (`ArithmeticOrientationGeometry.configScalingDatum_orbitCorr_eq`
  at `t = 0`); the atomic genus is the archimedean Green potential of the configuration.
- **Purity of the orientation cover over ℤ.** The cover exists and its middle cohomology is nonzero of
  weight `≥ ½` (Lean). Weight `½` is RH. A self-map with bounded local indices and Lefschetz number
  `#cover` would give it; the prime-vertex indices localize `1 − M(N)` but are unbounded.

## 5. Questions

| # | Question | Status |
|---|---|---|
| Q1 | Which Hilbert space carries the causal jet waves and the twisted torsion energies together, with locked divergences? | Atoms: **no** — locking produces the discriminant diagonal, which the `N log N` wall excludes (Lean). Smoothed graphs: equivalent to RH (SOSZ). |
| Q2 | What are the sheaves (Euler characteristics) whose linear terms are the genera `N log N` and `c_B(0)/2`? | `2g(B) = c_B(0)` is the weighted zero count `Re Σ_ρ m_ρ h(γ_ρ)conj h(γ̄_ρ)`, the trace of the identity on the spectral `H¹` (AOG); the atomic genus is the archimedean Green potential of the configuration, not a locked self-intersection (Lean + SOSZ). An `h⁰` with Riemann–Roch is RH-strength (Q3). |
| Q3 | Which class is ample, and does Hodge index follow from Riemann–Roch plus that class? | The pole plane; on the fibre it is the spherical pair `(3/2)φ_{3/2} + ½φ_{1/2}` (Lean). Hodge index ⇔ Riemann–Roch on an effective cone with the ample pole (ACS), and on the scaling surface Hodge index ⇔ RH; so the reduction holds both ways and its input is RH-strength. |
| Q4 | (B118′) Does any hyperbolic 3-manifold carry Weil's form? (1) finite volume, every embedding; (2) twisted infinite-volume carriers | **No.** (1): for every Newtonian kernel with a cusp expansion (every moderate-growth Green function of `Δ − ¾` on a lattice quotient), no injective embedding of the degrees reproduces the Frobenius intersection (Lean). (2): for a group with Poincaré series convergent at `½` and weights `‖w‖ ≤ 1`, no carrier when the degree end is a point of discontinuity, or the self-energy stays bounded along it, in particular at a conical limit point (Lean). Such a group has no parabolic elements (Lean), so for geometrically finite groups every boundary point is one of these (Beardon–Maskit), and every finitely generated group with `δ < 2` is geometrically finite (Canary, tameness). Residue: infinitely generated groups whose degree ray has unbounded self-energy at every degree (topic 1). |
| Q5 | Which trace discriminant defines an orientation cover over ℤ, and what is its cohomology? | The discriminant of `primeQuadraticPolynomial n`: its real points number `1 + μ(n)` (RIAC). Its middle cohomology is nonzero of weight `≥ ½`: `D(N) = Ω_±(√N)` unconditionally. Weight exactly `½` ⇔ RH (Lean). Over `𝔽_q[T]` the cover has no middle cohomology. |
| Q6 | (M2, M4) A locked presentation on windows of aperture `≤ 181/250`; Hodge index on windows of growing aperture | Smoothings: the counterterm-free presentation is the Lévy–Khintchine form `weilQuad = 2c₀‖f‖² + levyEnergy − primeSum + pole` (SpacingScaleHarmonicAnalysis, RHTower), whose Lévy density is the `ℍ³` Green function; its positivity on windows `≤ 181/250` is the corpus window theorem. Atoms: no locked presentation (Q1). M4 at all apertures is RH. |

## 6. Tools

| Tool | Status |
|---|---|
| Arakelov coordinates of isometries relative to `ℓ` | `imageCosh`, `h3Cosh_degPoint_h3Act`, `imageCosh_mul_right_le` |
| Dilation limits and endpoint Eisenstein series of carriers | `tendsto_carrierSum`, `endpointEisenstein_of_poincare` |
| Green function as a function of `cosh d`: bounds, monotonicity, log-Lipschitz | `greenOfCosh_le`, `greenOfCosh_anti`, `le_greenOfCosh_of_le_two`, `mul_abs_deriv_greenOfCosh_le`, `abs_greenOfCosh_sub_le` |
| Spherical analysis of the fibre | `sphericalFn`, `sphericalFn_radial`, `compensation_eq_spherical` |
| Locked dampings | `lockedKernel`, `tendsto_lockedKernel_of_ne`, `tendsto_lockedKernel_self` |
| Riemann–Roch for Frobenius graphs | axiomatic form in ACS (`RiemannRochAxiom`, `AmpleAxiom`); an `h⁰` with these axioms is RH-strength |
| Poincaré domination, gaps, finiteness of near orbit points | `exists_gap`, `finite_near`, `greenOfCosh_imageCosh_le_poincare`, `exp_neg_half_dist_le` |
| Loxodromic and conical carriers | `imageCosh_diag_conj`, `exists_prime_nonsingular_of_diag`, `exists_nat_card_primes_gt` |
| Tree Green functions | `treeGreen_resolvent`, `sum_treeGreen_apartment_nonneg`, `weilDeltaKernel_mul_pow` |
| Self-energy of the degree end | `rayWeight`, `selfEnergy`, `summable_rayWeight`, `finite_card_le_of_summable_exp`, `selfEnergy_le_of_near_orbit` |
| Boundary classification of groups convergent at `½` | `coe_pow_of_trace_eq_two`, `poincareWeight_pow_ge`, `mobius_shift`, `norm_mobius_shift_ge`, `norm_a_le_of_mapsOff`, `one_le_of_mapsOff` |
| Cusp zero modes | `CuspExpansion`, `eq_zero_of_bounded_zeroMode`, `abs_frobeniusTarget_le` |
| Weight of an orientation cover | `coverDefect`, `coverDefect_eq_mertensPartialSum`, `coverDefect_eq_mertensFunctionReal` |

## 7. Pillar theorems

| Pillar | Lean | Status |
|---|---|---|
| Archimedean part = `ℍ³` Green function at `s = ½` | `SurfaceOfSpecZ.archKernel_eq_hyperbolicGreen` | corpus |
| Off-diagonal = pole − (archimedean damping) + (torsion damping) | `tendsto_dampedFrobenius`, `tendsto_compensation_add_twistedEnergy` | corpus |
| Image distances in Arakelov coordinates | `h3Cosh_degPoint_h3Act`, `imageCosh_of_c_eq_zero` | proved |
| Dilation limit of an Eisenstein carrier | `tendsto_carrierSum` | proved |
| No Eisenstein carrier carries the torsion | `not_carrierSum_eq_torsion`, `not_carrierSum_eq_torsion_of_poincare` | proved |
| No bounded-geometry carrier carries the torsion | `not_carrierSum_eq_torsion_of_boundedGeometry`, `not_carrierSum_eq_torsion_of_frequently_boundedGeometry` | proved |
| No carrier of a group with a loxodromic along the degree geodesic | `not_carrierSum_eq_torsion_of_loxodromic` | proved |
| No carrier along an end of bounded self-energy; in particular at a conical end | `not_carrierSum_eq_torsion_of_selfEnergy`, `not_carrierSum_eq_torsion_of_conical` | proved |
| Convergence at `½` excludes parabolic elements | `not_summable_poincareWeight_of_parabolic`, `not_isParabolic_of_summable` | proved |
| No carrier at a point of discontinuity | `endpointEisenstein_of_wandering`, `not_carrierSum_eq_torsion_of_wandering`, `not_carrierSum_eq_torsion_of_convergent` | proved |
| No embedding into a compact or finite-volume quotient | `not_eq_frobenius_of_mapClusterPt`, `not_eq_frobenius_of_compact`, `not_eq_frobenius_of_finiteVolume` | proved |
| The orientation cover over ℤ has weight `≥ ½`; weight `½` ⇔ RH | `coverDefect_omega`, `riemannHypothesis_iff_coverDefect_le` | proved |
| Weil's `p`-kernel is the tree Green function at the Ramanujan point; adelic Green formula | `weilPrimeKernel_mul_pow_eq_treeGreen`, `treeEigen_eq_iff`, `weilDeltaKernel_mul_pow`, `weilDeltaKernel_of_offLadder` | proved |
| Finite-volume vertical carriers fold or diverge | `kleinian_thin_thick_dichotomy`, `parabolic_poincare_not_summable_half` | corpus (SOSZ) |
| Pole and Frobenius are spherical; the compensation is `(3/2)φ_{3/2} − 2πG_{3/2}` | `compensation_eq_spherical`, `weilKernel_eq_spherical` | proved |
| Plastic law as a spectral crossing | `compensation_neg_iff`, `compensation_pos_iff` | proved |
| Locked dampings give the discriminant; no locked atomic presentation | `tendsto_lockedKernel_self`, `not_eventually_posSemidef_lockedKernel` | proved |
| Hyperbolic Hodge index ⇔ RH | `riemannHypothesis_iff_hasseWeil_integerDegrees` (SOSZ) | corpus |
| Counterterm-free presentation of smoothings | Lévy–Khintchine form `weilQuad_eq` (SSHA), `archForm_eq_levyEnergy` (RHTower) | corpus |
| Riemann–Roch with the ample pole ⇔ Hodge index ⇔ RH | `PolarSurface.exists_effectivity_iff_hodgeIndex`, `scalingSurface_hodgeIndex_iff` (ACS) | corpus |

## 8. Traps

| Trap | Truth |
|---|---|
| A hyperbolic 3-manifold carries the finite places | in finite volume the degrees cluster (Newtonian pole) or escape into a cusp (zero mode with nonzero Wronskian); twisted infinite-volume carriers need an end of unbounded self-energy; the finite part jumps in the ratio |
| A cusp can absorb the degrees | the Poincaré series diverges there, and every Green function grows like `t^{½}u^{3/2}` or `t^{3/2}u^{½}` along the cusp |
| The orientation cover over ℤ may have no middle cohomology, as over `𝔽_q[T]` | its centred count is `M(N) = Ω_±(√N)` |
| A limit-point end can hide the jump | at a conical return only `≲ √P` group elements come near and each spoils at most one prime `≤ P`; the primes win |
| The finite places have no geometry | each is a Bruhat–Tits tree, Weil's `p`-kernel its Green function at the Ramanujan edge |
| A twisted character can cancel the jump | the dilation limit is a sum over the stabilizer of the end, continuous at resonance-free ratios; resonant primes have `Σ p^{−1/2} < ∞` |
| The archimedean Green function supplies the sign | it enters Weil's form with a minus sign; its positivity is that of `G_{3/2}` plus a complementary-series spherical function |
| The pole is a nuisance | it is the ample class, the spherical pair at `ν = 3/2, ½`; its `ν = ½` part cancels the complementary part of the Frobenius |
| A constant Robin constant renormalizes the diagonal | `¼` against `((p−2)/(p−1))log p` |
| Locking the two dampings gives the Arakelov diagonal the Hodge index needs | it gives the discriminant `I(n, n)/φ(n)`, bounded by `log n`; the Hodge index needs `≍ N log N` |
| Renormalization carries a sign | every form arises from some counterterm |
| Atomic Hodge index is RH | it holds unconditionally with genus `≍ N log N`; RH is the fixed-genus statement for smoothings |
| Manin's handlebody is the fibre | the fibre is `ℍ³` itself with one geodesic and `U(1)` symmetry; no quotient |

## 9. Open research topics

1. B118′(2) for infinitely generated groups: a carrier needs the self-energy to diverge along the
   whole degree end. For torsion-free `Γ` this is excluded classically: on the `ε`-thick part the
   self-energy is bounded (Sullivan's `λ₀ = 1` for `δ ≤ 1` and an interior elliptic estimate), and a
   ray that stays in one Margulis tube ends at a loxodromic fixed point, which is conical. Lean
   formalization of the thick-part bound.
2. A Lean construction of the cusp expansion for the continued Poincaré series of a Bianchi group.
3. Hodge index on windows of growing aperture (M4); at every aperture it is RH.
4. An `h⁰` on classes of `S` constructed from the archimedean and tree Green functions, with Riemann–Roch
   (RH-strength by Q3; a construction would be a new object, not a new equivalence).
5. The archimedean asymmetry: at `p` the critical parameter is the edge of the tempered spectrum, at
   `∞` it is the complementary point `¾` of `ℍ³`, and the pole cancels exactly that complementary
   piece. A Hodge index statement place by place in standard quantization.
6. Purity of the orientation cover (with RIAC): a self-map of the discriminant cover with bounded local
   indices and Lefschetz number `#cover` (weight `½` is RH).

## 10. Context

| Programme | Interface |
|---|---|
| SurfaceOfSpecZ (SOSZ) | half-products, `ℍ³` identity, genus, integer-degree Hasse–Weil, hyperbolic exclusions, dampings; HAT owns the archimedean fibre and the carriers |
| ArithmeticIntersectionTheory (AIT) | torsion orbits, adjunction `I(n, n)/φ(n)`, Gauss digamma; the finite part and the locked diagonal |
| ArithmeticEffectivityTheory, ArithmeticElectrostatics | torsion energies and their Abel limits |
| ArithmeticCastelnuovoSeveri, ArithmeticOrientationGeometry | scaling surface, Hodge index ⇔ RR + ample, orbit correlations, finite-field calibration |
| RenormalizedIntersectionArithmeticCounts (RIAC) | orientation covers, prime-vertex indices, prime-quadratic discriminant cover |
| FrustratedArithmeticDirichletForms | Weil's form as a Dirichlet form; the archimedean jump kernel is the `ℍ³` Green function |
| CountingHolography, ArithmeticHolographyOfTheModularHorizon, BlackHoleRingdown | count door; the modular horizon as the scattering face of the same `ℍ³` |
| WindowVisibilityLaw, ArithmeticHodgeTheoryOfDegenerations | window thresholds |

## 11. Success criteria and contributions

**Success.** (i) B118′ decided in Lean with explicit classes of carriers; (ii) the hyperbolic Arakelov
pairing with both parts, its Hodge index equivalent to RH and unconditional on windows of aperture
`≤ 181/250`; (iii) a diagonal produced by a coupled damping, not a counterterm, on those windows;
(iv) Riemann–Roch identities explaining both genera; (v) the ample class and the reduction of Hodge
index to Riemann–Roch, calibrated on `C × C` over `𝔽_q` and on the zonotope; (vi) the orientation-cover
question over ℤ answered or sharply obstructed.

**A contribution must** answer or sharpen one of Q1–Q6; be unconditional; reduce correctly on the
calibrations (`C × C` over `𝔽_q`, zonotope, fakes where relevant); never take a sign from a
counterterm; use no finite-volume quotient as carrier; not restate an RH-equivalent without new
mathematical content; not optimize constants.

## 12. Big picture

The archimedean fibre of the surface of `Spec ℤ` is rigid. Its isometries act on the degree geodesic
through four Arakelov coordinates. A hyperbolic carrier that sees the end of the geodesic as a point
of discontinuity produces only kernels continuous in the ratio of degrees, periodizations of the
archimedean Green function; along an end of bounded self-energy, conical ends included, the group has
too few near elements to spoil every prime ratio. Convergence at `½` leaves no parabolic points, so for
every finitely generated group these cases are all. In finite volume the degrees cluster or run into a
cusp, where every Green function grows through its zero mode. Either way the primes, which are jumps
in the ratio, cannot live in a hyperbolic 3-manifold. They live in the integer structure of `ℙ¹_ℤ`, and each prime has its own rank-one space,
the Bruhat–Tits tree, whose Green function at the Ramanujan edge is Weil's local kernel; the
critical line is that edge at every finite place. The pole is not foreign to the fibre: it is a pair of spherical functions, and its complementary piece
cancels that of the Frobenius, so the archimedean compensation is the `ν = 3/2` spherical function
against the standard resolvent, with the plastic ratio as their balance. What the fibre cannot
supply is the diagonal. Locking the two natural dampings reproduces only the discriminant, while
the Hodge index needs the Green potential of the whole configuration; the sign of RH sits in the
diagonal of a smoothing, which no counterterm and no locking of atoms provides. The topological
shadow says the same: the orientation cover over ℤ exists, its middle cohomology never vanishes, and
RH is its purity.
