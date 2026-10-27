# Arithmetic Effectivity Theory (AET)

**One question.** Over `𝔽_q` Weil's sign is the nonnegativity of a dimension: Riemann–Roch on
`C × C` reads `h⁰(D) − h¹(D) + h²(D) = ½ D·(D − K) + χ(𝒪)`, dropping `h¹ ≥ 0` leaves
`h⁰(D) + h⁰(K − D) ≥ ½ D·(D − K) + χ(𝒪)`, and sections cannot exist in negative degree. Over `ℤ`
the integers that could play `h⁰` are not dimensions: they are log-orders of finite groups and
log-volumes of lattices. Which real-valued cohomology on `Spec ℤ` and its correspondence surface
has a Riemann–Roch proved without the sign, which effectivity laws does it obey, and which signs can
integers produce?

AET is the theory of **real-valued effectivity**. Its basic object is an *effectivity function*: a
real function `h` on the classes of a polar surface, playing `h⁰`. Its basic invariants are the
**Euler characteristic** `χ` that `h` satisfies Riemann–Roch against, and the **growth** of `h` along
the ample ray and along classes of degree zero. Its guiding sentence:

> *RH is the Hodge index theorem of an arithmetic surface whose points are the primes with residue
> size `log p`, whose cohomology is measured by volume, whose Frobenius is the Hecke correspondence
> ring, and whose boundary is the archimedean place.*

Its basic principle:

> *A sign from integers is a comparison of two computations of one Euler characteristic, in which
> positivity enters only through the existence of a section or the order of a finite group.*

Namespace `GaloisForLFunctions.ArithmeticEffectivityTheory`; umbrella
`ArithmeticEffectivityTheory.lean`. Everything is unconditional; RH and its partial forms appear only
inside equivalences.

---

## 1. Place in the research

The frontier has a complete map of the mechanisms that can be built from the positivity of `Λ`, the
functional equation, the simple pole and strip holomorphy on the line, and each has a sharp limit.
It also knows which layer of Weil's argument is missing over `ℤ`: identities, the theorem of the
square and the budget are free, Rosati positivity is RH (ACP). Every attempt to supply the missing
layer through an *effective cone* is tautological: an ample cone of nonnegative degree has
Riemann–Roch iff it contains the open positive cone and the defect is nonnegative (the universal
floor law, ACS), and a Boolean section count with Riemann–Roch and Bézout exists iff the sign holds
(ACP P29). AET moves the question from cones to functions: effectivity is a *growth law* of a real
function, and the growth must be proved from the definition of the function.

| Programme | What AET takes | What AET adds |
|---|---|---|
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | polar surfaces, the scaling surface and `scalingSurface_hodgeIndex_iff`, curve data, the golden datum, effectivity axioms, the universal floor law, prime-node section counts | the real-valued effectivity calculus: Riemann inequality, Hilbert–Samuel growth, degree-zero growth |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | the theta `h⁰` of `Spec ℤ` with its Riemann–Roch (`arithH0_riemannRoch`), orbit Rosati positivity | the theta surface: characteristics, the free polarization, the failure of the base `h⁰` to extend |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Nyquist rank bounds, `E(s) = h⁰`-supply `− h¹`-obstruction, Boolean `h⁰`, section cones | log-volume counts in place of rank counts |
| [BiarithmeticGeometry](../BiarithmeticGeometry/README.md) | `E(log(N+1)) = N − log Q_N` (`boxDefect_eq_degree_sub_log_torsion`), prime-power transition groups | the log-torsion dictionary of the whole explicit formula; the product formula as Bézout |
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | correspondence ring, normalized graphs and the free theorem of the square, the layer map L1–L6, P29 (a section count is the sign), P30 (the Stepanov count is the sign) | the naive-height form of L5 (Tate limits); the Stepanov method as Siegel abundance + integrality floor |
| [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | the gauge torus, gauge charge, the boundary of a dilation = the archimedean degree | the additive characteristic of the theta surface as the gauge-charged direction |
| [ArithmeticPolarization](../ArithmeticPolarization/README.md) | the polarization law, local types at reflection pairs, twists, the diagonal collapse of lattice counts on the square | the *counting* mechanism of a polarization, with its Riemann–Roch and its growth laws |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | `κ = 1` rigidity, the quantum budget, Beurling rigidity | the base axioms against Beurling models |
| [SquareRootThreshold](../SquareRootThreshold/README.md), [BiScaleUncertainty](../BiScaleUncertainty/README.md), [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | the square-root threshold, large sieve, Nyquist diagonal | the emptiness test "sections over `ℤ` are large-sieve sections" |
| RHTower | explicit formula, zero detection, zero density, von Koch | the Stepanov reading of zero detection and local counts |

APol and AET split the polarization problem along its two conceivable sources over `ℤ`: APol studies
positivity coming from a non-hyperbolic localizing symmetry or from charge; AET studies positivity
coming from counting.

---

## 2. Why

**Weil's sign is a dimension.** In Weil's proof three identities (Lefschetz, adjunction, the
theorem of the square) hold for fake data as well as for curves; the sign enters once, through
Riemann–Roch on `C × C`: a class `D` with `D² > 0` and `D·A = 0` would have
`h⁰(nD) + h⁰(K − nD) ≥ ½ n² D² − O(n)`, while classes of degree zero carry boundedly many
sections. A growth that is quadratic in the class against a growth that is not: that is the whole
mechanism. Its ingredients are a function `h ≥ 0`, an Euler characteristic that is *quadratic*, and
a growth bound on degree zero. None is a cone axiom.

**Over `ℤ` the integers are log-torsions.** The prime side of the explicit formula is a sum of
`Λ(n)`, and `Λ(n)` is the logarithm of the order of the kernel of `ℤ/lcm(1..n) → ℤ/lcm(1..n−1)`;
`ψ(N) = log |ℤ/lcm(1..N)ℤ|`. The box Euler characteristic is integer degree minus logarithmic
torsion, `E(log(N+1)) = N − log Q_N`, and it is not a difference of dimensions (BAG). The explicit
formula is the second computation of the same quantity:
*logarithmic torsion = oscillation of the zeros + archimedean density*. A cohomology adapted to this
must be real-valued — log-volumes, as in van der Geer–Schoof, where `h⁰ = log θ` — and effectivity
must be the size of a log-volume, not membership in a cone.

**Over `ℤ` there is one intrinsic integrality inequality.** A nonzero integer has `|n| ≥ 1`;
equivalently the archimedean degree `log |n|` equals the finite log-torsion `Σ v_p(n) log p ≥ 0`. It
is the product formula read as Bézout: an effective principal divisor has nonpositive archimedean
part. Every sign from integers proved over `ℤ` — Liouville, Chebyshev's bounds, Nair's `lcm` bound,
Thue–Siegel, determinant methods, Northcott, the positivity of Néron–Tate heights — is this
inequality applied to an auxiliary object built by Siegel's lemma. Siegel's lemma is the abundance
statement of the base: small sections exist when the lattice is large. AET asks what this mechanism
can and cannot reach for `ζ`.

**Positivity of a quadratic form from counting is a theorem elsewhere.** On an abelian variety over a
number field the Néron–Tate height is a positive semidefinite quadratic form, and the proof uses only
(i) the theorem of the square up to a bounded error and (ii) the nonnegativity of naive heights,
which is the product formula; Northcott makes it definite. Tate's limit is the arithmetic form of
Weil's polarization. ACP shows that (i) is free on the correspondence ring of `ℤ`. AET makes the
missing input explicit: a *naive height* on the integral correspondence ring, nonnegative for an
arithmetic reason and at bounded distance from the Rosati trace form.

**One variable is a base.** The theta `h⁰` of `Spec ℤ` has an exact Riemann–Roch, and its Mellin
transform is `Λ(s)`; it gives the functional equation and holds for every datum with one. Its
Euler characteristic is linear in the degree. A surface needs an Euler characteristic quadratic in
the class, hence growth quadratic along the ample ray (Hilbert–Samuel). No function of the degree
with subquadratic growth satisfies a quadratic Riemann inequality on any polar surface: the base
`h⁰` is never the restriction of a surface `h⁰`. The scale is visible on the box class `√N · A`:
its Euler characteristic is `N`, the number of degrees of freedom of the polar box of length `N`.
A surface `h⁰` has the size of a dimension of Dirichlet polynomials of length `N`; the base `h⁰`
has the size of the degree `log N`. Arithmetic surfaces over `ℤ` show the same pattern: the rank of
the lattice of sections grows with the class and its log-volume grows quadratically.

---

## 3. Objects and language

| Over `𝔽_q` | AET object | Over `ℤ` | Lean |
|---|---|---|---|
| `C × C`, intersection form | polar surface `(E, ·, H, V)`, ample class `A = H + V` | scaling surface (ACS) | `PolarSurface`, `scalingSurface` |
| `χ(D) = ½ D·(D − K) + χ(𝒪)` | Euler characteristic `χ(x) = ½ x·(x − κ) + χ₀`, Serre symmetric | canonical class in the pole plane | `eulerChar`, `eulerChar_serre` |
| `h⁰ + h² ≥ χ` | Riemann inequality `χ(x) ≤ h(x) + h(κ − x)` | — | `RiemannInequality` |
| `h⁰` bounded in degree zero | `DegreeBounded`, `DegreeZeroSubquadratic` | — | — |
| `D` with `D² > 0`, `D·A = 0` | abundant class; abundance rate `max(0, ½ x²)` | an off-line zero | `Abundant`, `optimalEffectivity` |
| `h⁰(nA) ~ n² A²/2` | Hilbert–Samuel along the ample ray | box class `√N · A`, `χ = N` | `hilbertSamuel_of_riemannInequality`, `boxClass` |
| theta `h⁰` of the base | function of the degree | `h⁰(d) = log Σ e^{−π n² e^{−2d}}` | `thetaEffectivity`, `arithH0` |
| Néron–Tate height | naive height: bounded below, at bounded distance from a quadratic form; Tate limit | integral correspondence ring `ℤ[G]`, integral Rosati form | `tateLimit`, `intRosatiForm` |
| `#ker(m − nF)` | the degree form on `ℤ²` | — | `intEndDeg` |
| `#C(𝔽_{q^m})` | log-torsion of the horizon `log |ℤ/lcm(1..N)ℤ|`; transition kernels of log-order `Λ(N+1)` | `ψ(N)` | `logTorsion` |
| principal divisors have degree `0` | product formula `log n = log |ℤ/nℤ| = Σ v_p(n) log p` | Bézout of `Spec ℤ` | `log_eq_logTorsion` |
| theta divisor, characteristics | theta surface `h⁰(a, d)`, dual `h⁰∨(a, d)`, exponential characteristic `ϑ(J, t)` | even Hurwitz kernels | `thetaH0`, `thetaH0Dual`, `thetaChar` |
| `ℓ`-adic torsion | torsion characteristics `j/N`, finite Fourier transform, Gauss sums, root numbers | Dirichlet L-functions | Mathlib `ZMod.completedLFunction` |
| Frobenius graphs meeting the diagonal | torsion orbits `O_n` on the characteristic circle; archimedean intersection `I(m, n) = Σ log |ζ − η| = log |Res(Φ_m, Φ_n)|`; Abel energy `T_r` | `Λ` as an intersection number; Ramanujan sums as Fourier coefficients | `orbitIntersection`, `ramanujanSum`, `torsionEnergy` |
| Stepanov's auxiliary polynomial | auxiliary integer polynomial; integrality floor; analytic ceiling | `lcm(1..n+1) ∫₀¹ P ∈ ℤ` | `nairPoly` |
| `ℙ¹ × ℙ¹` | hyperbolic plane with `h⁰ = (a+1)⁺(b+1)⁺` | — | `hyperbolicPlane`, `p1SquareH0` |
| fake curves | battery: golden datum, complex fake, Beurling systems, shifted pair, twins | — | ACS, ACP |

**Words.**

- *Effectivity function*: a real function `h` on classes. *Linear* or *quadratic Riemann
  inequality*: according to whether its Euler characteristic is affine or quadratic.
- *Hilbert–Samuel*: `h(nA)` grows like `n²`. *Subquadratic in degree zero*:
  `h(nx) + h(κ − nx) = o(n²)` along every class with `x·A = 0`.
- *Abundant class*: a degree-zero class along which every function with the Riemann inequality
  grows quadratically. *Abundance rate*: the least such growth rate.
- *Naive height*, *Tate limit*, *Northcott*: as for heights on abelian varieties.
- *Log-torsion*: the logarithm of the order of a finite group. *Box class*: `√N · A`.
- *Characteristic*: the translation parameter of a theta series; *torsion characteristic*: `j/N`.
- *Soft*: holding on every datum of a family, hence carrying none of its arithmetic.
- *Integrality floor*: `|nonzero integer| ≥ 1`. *Ceiling*: the analytic bound it is compared with.
- *Torsion orbit*: the primitive roots of unity of one order; *Hecke translate*: `O_m ↦ O_{mt}`.
  *Renormalized energy*: the finite part of an Abel-regularized log-energy after subtracting the
  self-energy `log 1/(1 − r)` of each point.

Parameters: the class `x`, its degree `x·A`, the scaling `n`, the characteristic, the degree `d`,
the horizon `N`. Every theorem states which are fixed and which grow.

---

## 4. Mechanisms

1. **Weil's argument as a growth law** (`TheEffectivityCalculus`). On every polar surface the
   quadratic Riemann inequality and subquadratic growth in degree zero force the Hodge index
   (`hodgeIndex_of_riemannInequality`); bounded values on degree levels suffice
   (`degreeZeroSubquadratic_of_degreeBounded`). Conversely, under the Hodge index and with `κ` in
   the pole plane, `max(0, χ)` is such a function (`exists_effectivity_of_hodgeIndex`, via the
   level bound `eulerChar_le_levelBound`). A degree-zero class is abundant iff `x² > 0`
   (`abundant_iff`); the least growth rate along any class is exactly `max(0, ½ x²)`
   (`pair_self_le_two_mul_rate`, `eventually_optimalEffectivity_le`). On primitive classes
   `x² = −δ(x, x)`, so on the scaling surface the negative part of Weil's form is twice the least
   abundance rate. Four equivalent forms: `hodgeIndex_tfae`.
2. **The base does not extend** (`TheBaseDoesNotExtend`). The Riemann inequality forces
   Hilbert–Samuel along `nA` at every rate `< 1` (`hilbertSamuel_of_riemannInequality`); a function
   with affine growth in the degree has no Riemann inequality
   (`not_riemannInequality_of_affine_bound`). The theta `h⁰` of the degree obeys every linear law —
   positivity, `h(x) − h(−x) = x·A`, constancy on degree levels, vanishing in negative degree — on
   every polar surface (`thetaEffectivity_linear_laws`) and the quadratic one on none
   (`thetaEffectivity_not_riemannInequality`). Functions of the degree are effectivity functions
   exactly under the Hodge index, and then they grow quadratically
   (`exists_degree_effectivity_iff_hodgeIndex`, `degree_effectivity_quadratic`).
3. **Tate's limit** (`TatesLimitLaw`). Approximate doubling gives a unique homogeneous limit at
   distance `C/3` (`tendsto_tateSeq`, `abs_tateLimit_sub_le`, `tateLimit_two_nsmul`,
   `eq_of_two_nsmul_of_bounded`); an approximate parallelogram law gives an exact one
   (`tateLimit_parallelogram`, `parallelogram_nsmul`); boundedness below gives positivity
   (`tateLimit_nonneg`), Northcott gives definiteness modulo torsion
   (`isOfFinAddOrder_of_tateLimit_eq_zero`). A function homogeneous of degree two is nonnegative
   iff it has a naive height (`exists_naiveHeight_iff_nonneg`). Rosati positivity at a cycle is
   decided on integral correspondences, by rounding `⌊nc⌋/n → c` (`sum_sum_nonneg_of_int`,
   `orbitHodgeIndex_iff_int`), and is the existence of a naive height there
   (`orbitHodgeIndex_iff_exists_naiveHeight`).
4. **Naive heights are traces** (`NaiveHeightsAreTraces`). On a curve datum of any genus the
   integral Rosati form on `ℤ[F]` has a naive height iff the datum is unitary
   (`exists_naiveHeight_iff_unitary`). Kernel counts do not supply one: on the complex fake every
   kernel count is nonnegative while the Rosati form is `−2304` at `F² + 16`
   (`complexFake_kernelCounts_nonneg_no_naiveHeight`). The positive example is the theta count:
   its Tate limit is exactly `πJ²/t` (`tateLimit_log_thetaChar`).
5. **The horizon torsion** (`TheHorizonTorsion`). `log |ℤ/lcm(1..N)ℤ| = ψ(N)`
   (`logTorsion_eq_psi`), and each new point adds the log-order of a cyclic kernel, `Λ(N + 1)`
   (`logTorsion_succ_sub`). The product formula is the Bézout of the base (`log_eq_logTorsion`,
   `log_eq_sum_factorization_logs`). The box class has `χ = N` (`eulerChar_boxClass`).
6. **The theta surface** (`TheThetaSurface`). Poisson summation exchanges translation for
   modulation: `h⁰(a, d) − h⁰∨(a, −d) = d` (`thetaH0_riemannRoch`), with the dual count positive
   (`cosKernel_pos`) and the fibre at `0` maximal (`evenKernel_le_evenKernel_zero`). Completing the
   square: `ϑ(J, t) = e^{πJ²/t} · (shifted count)` (`hasSum_thetaChar`), so `log ϑ` is a
   nonnegative naive height for `πJ²/t` (`abs_log_thetaChar_sub_le`, `log_thetaChar_nonneg`) with
   exact quasi-periodicity (`thetaChar_add_period`). The quadratic term is the same on every
   translate of the lattice (`hasSum_shifted_thetaChar`): the polarization is soft. The fibre at
   characteristic `0` is `Λ(s)` (`completedHurwitzZetaEven_zero`).
7. **Torsion characteristics** (`TheTorsionCharacteristics`). For a nontrivial character of a
   finite field, `|τ(χ, ψ)|² = |F|` by orthogonality (`normSq_gaussSum_eq_card`,
   `norm_gaussSum_eq_sqrt_card`); the root number of a nontrivial character modulo a prime is a
   unit (`norm_rootNumber_eq_one`). Square-root cancellation is a count at every finite level.
8. **The Stepanov method** (`TheStepanovMethodOverZ`). Integrality
   `lcm(1..n+1) ∫₀¹ P ∈ ℤ` (`exists_int_eq_lcmUpto_mul_integral`); the integrality floor bounds the
   log-torsion by the auxiliary section, `log(1/∫₀¹ P) ≤ ψ(n + 1)` (`log_inv_integral_le_psi`);
   with `P = X^m(1 − X)^m` the ceiling `∫₀¹ P ≤ 4^{−m}` gives `lcm(1..2m+1) ≥ 4^m`
   (`nair_four_pow_le_lcmUpto`, `nair_psi_ge`). With `θ(x) ≤ x log 4` the log-torsion and the
   degree are comparable (`horizon_logTorsion_comparable`): the effectivity of the base.
   Over a finite field `𝔽_q` the same count reaches the sign (Stepanov's method, `RHTower.Stepanov`):
   the sections `Σ_{j<J} X^{jq}(r_j + s_j h^{(q−1)/2})` outnumber their vanishing conditions because
   `D^{(k)}(X^{jq} g) = X^{jq} D^{(k)} g` for `k < q` and `x^q = x` (`hasseDeriv_mul_X_pow`), they are
   nonzero by the Frobenius-flat expansion and descent (`stepanov_independence`), and the degree
   bound gives the Weil bound for hyperelliptic sums (`stepanov_count`, `abs_sum_quadraticChar_le`)
   and for Kloosterman sums (`RHTower.WeilKloosterman.kloosterman_weil_bound`). Over `ℤ` the method
   has the integrality floor and the degree bound but no flat coefficients.
9. **Calibration on `ℙ¹ × ℙ¹`** (`TheProjectiveSquareCalibration`). `h⁰ = (a+1)⁺(b+1)⁺` satisfies
   the Riemann inequality as `h¹ ≥ 0`, with equality on the effective and anti-effective quadrants
   (`p1SquareH1_nonneg`, `riemannInequality_p1SquareH0`), vanishes in negative degree and is bounded
   on degree levels (`p1SquareH0_degreeBounded`); the calculus returns the Hodge index
   (`hyperbolicPlane_hodgeIndex`).
10. **The base axioms** (`TheBaseAxioms`). The golden datum is a Beurling system with integral zeta
    series and functional equation, has an abundant class and no naive height
    (`goldenDatum_multiplicative_axioms_not_effective`). For `ζ` the currencies of effectivity are
    one statement (`riemannHypothesis_effectivity_tfae`).

11. **The prime side is an intersection** (`TheArchimedeanComputationOfTheLogTorsion`,
    `TheQDeformationOfTheHorizonPeriod`, `TheFourierCoefficientsOfTheTorsionMeasure`,
    `TheLogEnergyOfRootsOfUnity`, `TheIntersectionOfTorsionOrbits`,
    `TheWeilPrimeKernelIsARenormalizedTorsionEnergy`). `Λ(n) = Σ_{ζ ∈ O_n} log |1 − ζ|`, so `ψ(N)` is
    the potential at `1` of the Farey torsion, whose first Fourier coefficient is `M(N)`; `ψ(N)` is the
    value at `q = 1` of the count `log Π_{2≤n≤N} Φ_n(q) = Σ_d M(⌊N/d⌋) log [d]_q`. The energy of `μ_a`
    against `μ_b` is `gcd(a, b) log lcm(a, b)` (`logEnergy_eq`); distinct orbits meet in `φ(n) Λ(m/n)`
    when `n ∣ m` and not at all otherwise (`orbitIntersection_eq`), so an orbit meets its Hecke
    translate of degree `t` in `Λ(t)` per point (`orbitIntersection_hecke`). The Abel energies are
    Gram matrices of Ramanujan sums; twisted by the positive kernel `d/φ(d)` of the gcd they tend to
    `−Λ(t) t^{−1/2}` off the diagonal and, after subtracting `log 1/(1 − r)`, to minus the
    log-discriminant per point (`weilPrimeKernel_renormalized_torsion_energy`). The prime side of
    Weil's form is a renormalized positive energy; the sign is lost in the renormalization.
12. **Calibration on curves** (`TheHyperellipticCalibration`, `RHTower.HyperellipticRiemannHypothesis`).
    For `f ∈ 𝔽_p[X]` squarefree, split, of odd degree `2g + 1`, the L-function of `y² = f(x)` is a
    curve datum of genus `g` whose Lefschetz numbers are the point counts of the projective curve
    (`hyperellipticDatum_pointCount`). It is unitary by counting alone — Stepanov's section count on
    the even extensions bounds `|ω_i| ≤ √p`, and the Gauss-sum modulus fixes `|Π ω_i| = p^g` through
    the top degree sum (`riemannHypothesis_splitHyperelliptic`) — so every Frobenius window carries
    an effectivity function and `ℤ[F]` a naive height (`hyperellipticDatum_window_exists_effectivity`,
    `hyperellipticDatum_exists_naiveHeight`).

---

## 5. Pillar theorems

| Pillar | Statement | Lean |
|---|---|---|
| **E1 The effectivity calculus** | quadratic Riemann inequality + subquadratic growth in degree zero ⇔ Hodge index on every polar surface; abundance ⇔ `x² > 0`; least abundance rate `max(0, ½ x²)` | `hodgeIndex_tfae`, `abundant_iff`, `pair_self_le_two_mul_rate`, `eventually_optimalEffectivity_le` |
| **E2 The base does not extend** | Hilbert–Samuel is forced; the theta `h⁰` of the degree satisfies every linear law and no quadratic Riemann inequality, on every surface | `hilbertSamuel_of_riemannInequality`, `thetaEffectivity_linear_laws`, `thetaEffectivity_not_riemannInequality`, `exists_degree_effectivity_iff_hodgeIndex` |
| **E3 Tate's limit law** | naive heights produce positive quadratic parts; Rosati positivity is decided on `ℤ[G]` and is a naive height there; a naive height must be a trace, not a kernel order | `tateLimit_parallelogram`, `tateLimit_nonneg`, `isOfFinAddOrder_of_tateLimit_eq_zero`, `orbitHodgeIndex_iff_exists_naiveHeight`, `exists_naiveHeight_iff_unitary`, `complexFake_kernelCounts_nonneg_no_naiveHeight` |
| **E4 The integer of the sign** | RH ⇔ `log |ℤ/lcm(1..N)ℤ| = χ(√N A) + O(√N log² N)` on every polar surface | `riemannHypothesis_iff_logTorsion_sub_eulerChar` |
| **E5 The theta surface** | Riemann–Roch with characteristic; a nonnegative naive height whose Tate limit is `πJ²/t`; the polarization is soft | `thetaH0_riemannRoch`, `abs_log_thetaChar_sub_le`, `tateLimit_log_thetaChar`, `hasSum_shifted_thetaChar` |
| **E6 Counting gives square roots at each level** | `|τ(χ, ψ)|² = |F|`; unit root numbers | `normSq_gaussSum_eq_card`, `norm_rootNumber_eq_one` |
| **E7 The Stepanov method reaches the base** | integrality floor `log(1/∫P) ≤ ψ(n+1)`; Nair `ψ(2m+1) ≥ m log 4` | `log_inv_integral_le_psi`, `nair_psi_ge`, `horizon_logTorsion_comparable` |
| **E8 Calibration** | `ℙ¹ × ℙ¹` satisfies the calculus with dimensions; genus one: naive height ⇔ Hasse; split hyperelliptic curves of every genus are unitary by counting and carry effectivity functions and naive heights; golden datum: abundant, no naive height | `hyperbolicPlane_hodgeIndex`, `genusOne_exists_naiveHeight_iff`, `riemannHypothesis_splitHyperelliptic`, `hyperellipticDatum_window_exists_effectivity`, `goldenDatum_multiplicative_axioms_not_effective` |
| **E9 One statement in five currencies** | RH ⇔ effectivity function ⇔ no abundant class ⇔ naive heights ⇔ fixed tensor loss ⇔ log-torsion law | `riemannHypothesis_effectivity_tfae` |
| **E10 The prime side is an intersection** | `J(a, b) = gcd(a, b) log lcm(a, b)`; `I(m, mt) = φ(m) Λ(t)`; Weil's prime kernel plus the log-discriminant diagonal is minus the renormalized limit of positive gcd-twisted torsion energies | `logEnergy_eq`, `orbitIntersection_hecke`, `weilPrimeKernel_renormalized_torsion_energy` |

---

## 6. The questions and their answers

1. **Which integer, attached to the integers themselves and not to the zeros, bounds the
   oscillation of the zero sum?** The order of the finite group `ℤ/lcm(1..N)ℤ`. Its log-order is
   `ψ(N)`, it grows by the log-order of a cyclic kernel at each prime power, and RH says it equals
   the Euler characteristic `N` of the box class `√N · A` to `O(√N log² N)` (E4). The integrality
   floor gives `log |ℤ/lcm(1..N)ℤ| ≥ (N − 1) log 2`, the product formula an upper bound of the same
   order (E7): integrality alone fixes the size of the torsion, not its deviation from the degree.
2. **What is a section on `Spec ℤ × Spec ℤ`, and when do sections exist in quadratic abundance?**
   Whatever a section is, its count must be a function `h` with the quadratic Riemann inequality and
   subquadratic growth in degree zero, and this is exactly the Hodge index (E1). The count must grow
   like a dimension of Dirichlet polynomials (`χ(√N A) = N`), not like a degree: the base `h⁰` is
   excluded on every surface (E2). Sections in quadratic abundance exist on the theta surface in
   the characteristic direction (E5), but there the abundance is the free polarization `πJ²/t`,
   identical on every fibre. On the scaling surface the abundant classes are exactly the classes of
   positive square in degree zero, and their abundance rate is half the negative part of Weil's form
   (E1).
3. **What couples `+` and `×` strongly enough to separate the arithmetic point from its gauge
   twins?** At each finite level the finite Fourier transform of `ℤ/Nℤ`: additive characteristics
   `j/N` of the theta surface and multiplicative characters are exchanged by Gauss sums, whose
   modulus `√p` is a count (E6), and the sign of each functional equation is a unit. Square-root
   cancellation from counting holds at every level; the walls ask for it at the arithmetic point,
   uniformly in the level, where no finite group computes it. The archimedean intersection of
   torsion orbits couples the two operations exactly: the additive positions of the orbits of
   orders `m` and `mt` meet in `Λ(t)` per point (E10). Over `𝔽_q` the coupling that carries the
   sign is the Frobenius: `q`-th powers are flat under Hasse derivatives and fixed on points, so
   Stepanov's auxiliary-section count reaches square roots (`RHTower.Stepanov`) and, with the
   Gauss-sum modulus in the top degree sum, unitarity of actual curves (E8); over `ℤ` no
   coefficients are flat.
4. **How does a positivity proved on average over heights localize at one height below the zero
   spacing?** In AET the sign is pointwise in the class: each class carries its own abundance rate
   `max(0, ½ x²)` (E1). Averaged positivity is a statement about a family of classes and controls no
   single rate; localizing it is the selection problem of the averaged theorems (ACS, SRT), and AET
   supplies the pointwise invariant it would have to bound.
5. **What is the base?** At receiver level a fixed tensor loss, equivalent to RH (ACP). It cannot be
   axiomatized by multiplicative data: the golden datum satisfies the Beurling, integrality and
   functional-equation axioms and has an abundant class and no naive height (E8, E9). The base
   `h⁰` of `Spec ℤ` is a linear theory valid on every datum (E2).

The field-level question — *which positive structure supplies the sign* — has the following answer
form in AET: a naive height on `ℤ[G]` (E3), equivalently an effectivity function (E1), equivalently
a count of a finite group at square-root precision (E4). Each is RH; each has been reduced to the
others; none has been constructed.

---

## 7. Traps

| Trap | Truth |
|---|---|
| An effective cone with Riemann–Roch is an effectivity | Its Riemann–Roch is the defect floor (universal floor law); a Boolean count with RR and Bézout is the sign (ACP P29) |
| The theta `h⁰` of `Spec ℤ` is half of Weil's argument | Its Riemann–Roch is linear in the degree; it holds on every surface and satisfies the quadratic inequality on none (E2) |
| A surface `h⁰` should be a log-volume of the degree | It must grow like `χ`, i.e. like the square of the class coefficient: a dimension of sections of the box, not its degree |
| Integrality of point counts constrains the sign | The golden datum has integral counts, integral zeta and the functional equation, and an abundant class (E9) |
| A positive polarization on a surface over `ℤ` is Weil's | The theta surface carries one at every characteristic; it is soft (E5) |
| The integrality floor reaches the sign | It reaches Chebyshev's bounds (E7); the deviation of log-torsion from degree is invisible to it |
| Stepanov's method is integrality plus a degree bound | Over `𝔽_q` it needs Frobenius-flat coefficients to make the sections outnumber the conditions (`RHTower.Stepanov`); without them the count stops at Chebyshev's order (E7) |
| Square-root cancellation needs analysis | At each finite level it is a count (E6); the open part is uniformity at the arithmetic point |
| A naive height exists because the theorem of the square is free | Freeness of the quadratic part says nothing about a nonnegative function at bounded distance (E3) |
| Orders of finite kernels give a naive height | They are determinants; the complex fake has nonnegative kernel counts and no naive height (E3) |
| Positivity on integral correspondences is weaker than on real ones | They are equivalent: rounding transports positivity (E3) |
| A positive energy whose off-diagonal is Weil's prime kernel gives Weil positivity | The torsion energy carries the divergent self-energy `log 1/(1 − r)` on the diagonal; at atomic resolution it bounds the prime form only as the Schur test does, and atomic tests are blind to the zeros (E10) |
| The prime matrix separates the gauge twins | `λ(m) λ(mt) = λ(t)`: the Liouville kernel is a `±1` congruence of Weil's; selectivity lives in the archimedean and polar parts |
| Abundance is a property of a family | It is pointwise: each class has the rate `max(0, ½ x²)` (E1) |

---

## 8. Tools

**From sibling programmes:** polar surfaces, the scaling surface and its Hodge index, curve data and
fakes, the theta `h⁰` of `Spec ℤ`, the box Euler characteristic and transition groups, the
correspondence algebra with Rosati and orbit Hodge index, the fixed-loss criterion, the golden
Beurling system, von Koch; Stepanov's method and the Weil bounds over `𝔽_q` (`RHTower.Stepanov`,
`RHTower.WeilKloosterman`) and RH for split odd-degree hyperelliptic curves
(`RHTower.HyperellipticRiemannHypothesis`); from Mathlib: Gaussian Poisson summation, even Hurwitz kernels and their
functional equation, `ZMod` L-functions, Gauss sums, root numbers, Chebyshev's functions and
`lcmUpto`.

**Built here:** the effectivity calculus (Riemann inequality, degree control, abundance and its
rate, optimal effectivity); Hilbert–Samuel and the non-extension of degree functions; Tate's limit
machine on abelian groups; integral Rosati forms and the rounding principle; the horizon log-torsion
and the box class; the theta surface with characteristic, its free polarization and its softness;
Gauss-sum moduli and unit root numbers; the integrality floor for auxiliary integer polynomials and
Nair's bound; the `ℙ¹ × ℙ¹` calibration; the golden base countermodel; the five-currency
equivalence for `ζ`; torsion orbits with their intersection law, Ramanujan-sum Fourier
coefficients, the q-deformed horizon, Abel energies and the gcd twist.

**To build:** a section count on the scaling surface defined without the sign; a naive height on
`ℤ[G]` from arithmetic; the limit of the Stepanov method (integer Chebyshev constant); charged
sections at torsion characteristics with selectivity at characteristic `0`.

---

## 9. Open research topics

1. **A section count on the scaling surface with a quadratic Euler characteristic**, defined from
   arithmetic, of the size of a dimension of Dirichlet polynomials on box classes, with its growth
   laws proved from its definition. By E1 this is RH; partial forms are growth bounds in degree
   zero, each of which bounds the negative part of Weil's form.
2. **A naive height on `ℤ[G]`**: a function nonnegative for an arithmetic reason (a cardinality, a
   product formula) at bounded distance from the integral Rosati form. Kernel orders are
   determinants and are excluded (E3); the height must be of trace type, as the theta count is,
   but not soft.
3. **Selective sections at torsion characteristics**: positivity on the theta surface that
   separates characteristic `0` from its neighbours, i.e. a non-soft polarization.
4. **The limit of the Stepanov method over `ℤ`**: how close `log(1/∫₀¹ P)` can come to `ψ(n+1)`
   is the integer Chebyshev problem; a proof that it stays below `n` would show that the
   integrality floor cannot reach the prime number theorem. Over `𝔽_q` the method reaches the
   sign through Frobenius-flat coefficients (`RHTower.Stepanov`); its analogue over `ℤ` would be a
   family of coefficients invisible to the vanishing conditions.
5. **Uniform square-root cancellation from counting**: a family of finite groups, one per level,
   whose orders compute `ψ(N) − N` at the arithmetic point.
6. **Emptiness tests**: whether every section count with the Riemann inequality on box classes is
   bounded by a large-sieve count in degree zero; whether a source bound for the collision charge
   exists (AOG, APol).
7. **The archimedean place of the torsion picture**: a positive structure whose renormalized limit
   is Weil's archimedean term, so that the whole form, not only its prime side, is a renormalized
   energy; and a regularization finer than the uniform self-energy of a point.

---

## 10. Success criteria and contribution standard

AET succeeds when it produces a real-valued effectivity whose Riemann inequality and growth laws are
proved from its definition and which is selective for `ζ`, or a theorem naming why a stated class of
constructions cannot be one, with its positive survivor.

| Criterion | Test |
|---|---|
| Calibration | reproduces `ℙ¹ × ℙ¹` with dimensions, Hasse in genus one by naive heights, unitarity of curve data, the theta Riemann–Roch of the base |
| Fakes | fails on the golden datum and the complex fake, for a reason the construction names |
| Selectivity | separates `ζ` from the shifted pair, Beurling systems, the Liouville twin and pole-order-two models |
| Quadratic Euler characteristic | its Riemann–Roch is quadratic in the class; linear Riemann–Roch is free |
| Scale | its count on the box class has the size of `χ(√N A) = N` |
| Counting origin | its positivity is a cardinality, a log-order of a finite group or a log-volume |
| Growth | Hilbert–Samuel along the ample class and a pointwise bound in degree zero, each proved |
| Non-circularity | defined before its sign; no interface field carries the conclusion |

A contribution must:

1. be an unconditional Lean theorem about an object of §3;
2. state its Euler characteristic and whether it is linear or quadratic;
3. state which effectivity law it proves (Riemann inequality, Hilbert–Samuel, degree-zero growth,
   naive height, Northcott) and from what;
4. say what it gives on the golden datum, the complex fake, curves and the battery;
5. keep identities apart from signs and name the integer or log-volume that carries any sign;
6. record the positive survivor of every no-go.

Principles: effectivity is a growth law; integers over `ℤ` are log-torsions; the product formula is
the Bézout of the base; Riemann–Roch on the base is linear and free; a polarization from counting
needs a quadratic Euler characteristic and must not be soft; identities first, sign last; a
reformulation is not a reduction.
