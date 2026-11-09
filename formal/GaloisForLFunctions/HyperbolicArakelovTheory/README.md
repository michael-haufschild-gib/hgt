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
| Trees | `treeAdj`, `treeEigen`, `treeGreen` | radial adjacency of the `(q+1)`-regular tree; `λ_s = q^s + q^{1−s}`; `G_s(d) = q^s/(q^{2s} − 1)·q^{−sd}` |
| Smoothed graphs | `splineCycle`, `zetaScalingDatum.orbitCorr` | cubic spline `B`; `c_B(log n) = Γ_1·Γ_n` smoothed; genus `c_B(0)/2` |
| Windows | `windowThreshold` | tests supported in `[−A, 0]`; `windowThreshold A = ⊤` for `A ≤ 181/250` |
| Orientation covers | `factorOrientationCover`, `coefficientOrientationCover` (RIAC) | Möbius as point defect over `𝔽_q[T]` |

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
- **Damping** `K_r → K` (`r → 1`) by PSD kernels; **counterterm**: a divergent diagonal subtraction;
  **locking**: running the two channels at matched radii so that their divergences cancel;
  **coupled damping**: a PSD damping of the whole pairing.
- **Genus of a smoothing**: half the self-defect of a smoothed graph, `g = c_B(0)/2`; **atomic genus**:
  the least genus that makes the atomic defect nonnegative on degrees `≤ N`.
- **Ample class**: the pole plane `⟨H, V⟩`; **primitive class**: orthogonal to `H` and `V`.
- **Hyperbolic Hodge index**: `δ ≥ 0` on the span of the (smoothed) graphs.
- **Orientation cover**, **point defect**, **local index**, **Lefschetz localization** (topological
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
15. *Poincaré domination and conical returns* (`exists_gap`, `summable_greenOfCosh_imageCosh`,
    `exists_prime_nonsingular_of_diag`, `not_carrierSum_eq_torsion_of_loxodromic`,
    `not_carrierSum_eq_torsion_of_conical`). Convergence of the Poincaré series at `½` bounds the
    Green majorant at every pair no image hits; resonant primes have `Σ 1/p < ∞`; at a conical return
    at most `≲ S e^{R}√P` group elements come near, each spoils at most one prime `≤ P`, and the primes
    outnumber them (Chebyshev); so bounded geometry holds along a prime ratio.

**To discover.**
- The **diagonal of a smoothing**: a coupled damping of smoothed graphs whose divergences cancel
  between channels without a counterterm.
- **Riemann–Roch on `S`**: an `h⁰` on classes of `S` whose Euler characteristic has the genera as linear
  terms, and **Hodge index from Riemann–Roch plus the ample pole**.
- An **orientation cover over ℤ** with a weight-`½` cohomology.

## 5. Questions

| # | Question | Status |
|---|---|---|
| Q1 | Which Hilbert space carries the causal jet waves and the twisted torsion energies together, with locked divergences? | Atoms: **no** — locking produces the discriminant diagonal, which the `N log N` wall excludes (Lean). Smoothed graphs: equivalent to RH (SOSZ). |
| Q2 | What are the sheaves (Euler characteristics) whose linear terms are the genera `N log N` and `c_B(0)/2`? | The atomic genus is the archimedean Green potential of the configuration, not a locked self-intersection (Lean + SOSZ); a sheaf-theoretic `h⁰` is open. |
| Q3 | Which class is ample, and does Hodge index follow from Riemann–Roch plus that class? | The pole plane; on the fibre it is the spherical pair `(3/2)φ_{3/2} + ½φ_{1/2}` (Lean). The abstract reduction HI ⇔ RR + ample is in ACS/AET; an `h⁰` on `S` is open. |
| Q4 | (B118′) Does any hyperbolic 3-manifold carry Weil's form? (1) finite volume, every embedding; (2) twisted infinite-volume carriers | (2): **no.** For a group with Poincaré series convergent at `½` and any weights `‖w‖ ≤ 1`: excluded when the degree end `∞` is a point of discontinuity (bounded `γ^{±1}(∞)`, bounded isometric radii, finite stabilizer) and when it is a conical limit point (Lean); for geometrically finite groups with `δ < ½` every boundary point is one of the two (classical). Also excluded: every carrier of bounded geometry along one prime ratio, every group whose degree geodesic is the axis of a loxodromic. Open: non-conical limit points of geometrically infinite groups. (1): vertical embedding excluded (SOSZ); in finite volume the Poincaré series at `½` diverges (`δ = 2`), so a carrier there is a continued resolvent; general embeddings into cusps open. |
| Q5 | Which trace discriminant defines an orientation cover over ℤ, and what is its cohomology? | Delegated to RIAC: the prime-quadratic family `F_n = Π(X² + p)^a` has `sign disc F_n = μ(n)`; the square-root estimate is open. |
| Q6 | (M2, M4) A locked presentation on windows of aperture `≤ 181/250`; Hodge index on windows of growing aperture | Smoothings: the counterterm-free presentation is the Lévy–Khintchine form `weilQuad = 2c₀‖f‖² + levyEnergy − primeSum + pole` (SpacingScaleHarmonicAnalysis, RHTower), whose Lévy density is the `ℍ³` Green function; its positivity on windows `≤ 181/250` is the corpus window theorem. Atoms: no locked presentation (Q1). M4 at all apertures is RH. |

## 6. Tools

| Tool | Status |
|---|---|
| Arakelov coordinates of isometries relative to `ℓ` | `imageCosh`, `h3Cosh_degPoint_h3Act`, `imageCosh_mul_right_le` |
| Dilation limits and endpoint Eisenstein series of carriers | `tendsto_carrierSum`, `endpointEisenstein_of_poincare` |
| Green function as a function of `cosh d`: bounds, monotonicity, log-Lipschitz | `greenOfCosh_le`, `greenOfCosh_anti`, `le_greenOfCosh_of_le_two`, `mul_abs_deriv_greenOfCosh_le`, `abs_greenOfCosh_sub_le` |
| Spherical analysis of the fibre | `sphericalFn`, `sphericalFn_radial`, `compensation_eq_spherical` |
| Locked dampings | `lockedKernel`, `tendsto_lockedKernel_of_ne`, `tendsto_lockedKernel_self` |
| Riemann–Roch for Frobenius graphs | to build |
| Poincaré domination, gaps, finiteness of near orbit points | `exists_gap`, `finite_near`, `card_near_le`, `greenOfCosh_imageCosh_le_poincare`, `exp_neg_half_h3Dist_le` |
| Loxodromic and conical carriers | `imageCosh_diag_conj`, `exists_prime_nonsingular_of_diag`, `exists_nat_card_primes_gt` |
| Tree Green functions | `treeGreen_resolvent`, `sum_treeGreen_apartment_nonneg`, `weilDeltaKernel_mul_pow` |
| Twisted Green functions at non-conical limit points | to build |

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
| No carrier at a conical degree end | `not_carrierSum_eq_torsion_of_conical` | proved |
| Weil's `p`-kernel is the tree Green function at the Ramanujan point; adelic Green formula | `weilPrimeKernel_mul_pow_eq_treeGreen`, `treeEigen_eq_iff`, `weilDeltaKernel_mul_pow`, `weilDeltaKernel_of_offLadder` | proved |
| Finite-volume vertical carriers fold or diverge | `kleinian_thin_thick_dichotomy`, `parabolic_poincare_not_summable_half` | corpus (SOSZ) |
| Pole and Frobenius are spherical; the compensation is `(3/2)φ_{3/2} − 2πG_{3/2}` | `compensation_eq_spherical`, `weilKernel_eq_spherical` | proved |
| Plastic law as a spectral crossing | `compensation_neg_iff`, `compensation_pos_iff` | proved |
| Locked dampings give the discriminant; no locked atomic presentation | `tendsto_lockedKernel_self`, `not_eventually_posSemidef_lockedKernel` | proved |
| Hyperbolic Hodge index ⇔ RH | `riemannHypothesis_iff_hasseWeil_integerDegrees` (SOSZ) | corpus |
| Locked presentation of smoothings on windows | — | open |
| Riemann–Roch on `S` reproducing both genera | — | open |

## 8. Traps

| Trap | Truth |
|---|---|
| A hyperbolic 3-manifold carries the finite places | finite volume folds or diverges; twisted infinite-volume carriers are excluded at points of discontinuity and at conical limit points; the finite part jumps in the ratio |
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

1. B118′(2) at non-conical limit points (geometrically infinite groups with `δ < ½`).
2. B118′(1) for general embeddings: embeddings escaping into a cusp of a lattice, with the
   automorphic resolvent at eigenvalue `¾` as carrier.
3. The diagonal of smoothed graphs as a coupled damping (M2 on windows `≤ 181/250`, M4).
4. An `h⁰` on classes of `S` with a Riemann–Roch formula.
5. The archimedean asymmetry: at `p` the critical parameter is the edge of the tempered spectrum, at
   `∞` it is the complementary point `¾` of `ℍ³`, and the pole cancels exactly that complementary
   piece. A Hodge index statement place by place in standard quantization.
6. Orientation covers (with RIAC): the square-root estimate for the prime-quadratic family.

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
archimedean Green function; at a conical end the group has too few near elements to spoil every
prime ratio. Either way the primes, which are jumps in the ratio, cannot live in a hyperbolic
3-manifold. They live in the integer structure of `ℙ¹_ℤ`, and each prime has its own rank-one space,
the Bruhat–Tits tree, whose Green function at the Ramanujan edge is Weil's local kernel; the
critical line is that edge at every finite place. The
pole is not foreign to the fibre: it is a pair of spherical functions, and its complementary piece
cancels that of the Frobenius, so the archimedean compensation is the `ν = 3/2` spherical function
against the standard resolvent, with the plastic ratio as their balance. What the fibre cannot
supply is the diagonal. Locking the two natural dampings reproduces only the discriminant, while
the Hodge index needs the Green potential of the whole configuration; the sign of RH sits in the
diagonal of a smoothing, which no counterterm and no locking of atoms provides.
