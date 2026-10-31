# Arithmetic Effectivity Theory (AET)

Namespace `GaloisForLFunctions.ArithmeticEffectivityTheory` (the 𝔽₃ elliptic files use the sub-namespace
`…ArithmeticEffectivityTheory.FiniteFieldEllipticBase`); umbrella `ArithmeticEffectivityTheory.lean`; 50 modules. All
results unconditional; statements "⇔ RH" are proved equivalences.

## 1. Motivation

Over $\mathbb F_q$ Weil's sign is the nonnegativity of a dimension: Riemann–Roch on $C\times C$ with $h^1\ge0$ dropped gives
$h^0(D)+h^0(K-D)\ge\chi(D)$, and degree-zero classes carry few sections. Over $\mathbb Z$ the integers that could play $h^0$ are
log-orders of finite groups and log-volumes of lattices. AET asks which real-valued "section counts" exist on $\operatorname{Spec}\mathbb Z$ and
its scaling surface, which effectivity laws they obey, which signs integers can produce, and how far counting reaches
(Tate heights, Stepanov, Gauss sums, Burgess). It also builds one positive-genus function field over $\mathbb F_3$ completely,
as the calibration of what a base with a zeta function looks like.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Euler characteristic | `eulerChar` | $\chi(x)=\tfrac12x\cdot(x-\kappa)+\chi_0$, Serre symmetric |
| Riemann inequality | `RiemannInequality` | $\chi(x)\le h(x)+h(\kappa-x)$ |
| Degree-zero growth | `DegreeBounded`, `DegreeZeroSubquadratic` | bounded on degree levels; $o(n^2)$ along degree-zero classes |
| Abundant class | `Abundant`, `optimalEffectivity`, `levelBound` | degree 0 class along which every RI function grows quadratically |
| Theta $h^0$ of the degree | `thetaEffectivity` (with AOG `arithH0`) | $h(x)=\log\sum_ne^{-\pi n^2e^{-2(x\cdot A)}}$ |
| Tate limit | `tateSeq`, `tateLimit` | $\lim4^{-n}h(2^nx)$ |
| Integral Rosati forms | `intRosatiForm`, `intRosatiDeg`, `intEndDeg` | $\tau_x(\xi\xi')$ on $\mathbb Z[G]$; $\operatorname{Tr}(P(F)P(F)')$ on $\mathbb Z[F]$; $\deg(m-nF)$ |
| Horizon log-torsion, box class | `logTorsion`, `boxClass` | $\log|\mathbb Z/\operatorname{lcm}(1..N)|=\psi(N)$; $\sqrt N\cdot A$ with $\chi=N$ |
| Polar box counts | `polarBoxCount`, `nodeBoxCount` | $(t/2)^2$; $(t/2)^2-\psi((t/2)^2)$ |
| Theta surface | `thetaH0`, `thetaH0Dual`, `thetaChar` | $h^0(a,d)$ with characteristic; $\vartheta(J,t)=\sum e^{-\pi n^2t+2\pi nJ}$ |
| Auxiliary sections | `nairPoly` | $x^m(1-x)^m$ |
| $\mathbb P^1\times\mathbb P^1$ | `hyperbolicPlane`, `p1SquareH0`, `p1SquareCanonical` | $h^0=(a+1)^+(b+1)^+$ |
| Torsion of the circle | `torsionLogSum`, `ramanujanSum`, `torsionFourier`, `logEnergy`, `orbitIntersection` | Farey log sums; $c_n(m)$; $\hat\nu_N(1)$; $J(a,b)$; $I(m,n)$ |
| Horizon polynomial | `horizonPoly`, `qInt`, `mertens` | $\prod_{2\le n\le N}\Phi_n$; $[d]_q$; $M(k)$ |
| Torsion energy | `torsionEnergy`, `gcdTwist`, `twistedEnergy`, `weilPrimeKernel` | $\sum-\log|1-r\zeta\bar\eta|$; $\sum_{e\mid(m,n)}\mu(e)^2/\varphi(e)$; $\Lambda(n/m)(n/m)^{-1/2}$ |
| Hyperelliptic datum | `hyperellipticDatum` | curve datum of $y^2=f(x)$, $f$ squarefree of odd degree |
| Burgess objects | `shiftSum`, `EvenTuple`, `burgessEnergy`, `burgessS`, `burgessConst` | $T(x)=\sum_b\chi(x+b)$; box energy; $S(M,N)$ |
| 𝔽₃ elliptic base | `curve`, `CoordinateRing`, `FunctionField`, `poleDegree`, `geometricGenus` | $Y^2Z=X^3-XZ^2$ over $\mathbb F_3$ |
| 𝔽₃ arithmetic | `RingOfIntegers`, `FinitePlace`, `infinityValuation`, `Adeles`, `adeleHaar`, `ellipticAdditiveDomain`, `AdditiveQuotient` | places, adeles, gap domain, $\mathbb A/K$ |
| 𝔽₃ zeta | `datum`, `numerator`, `zeta`, `zetaFunction`, `shiftedZetaQuotient`, `arithmeticZetaRatio` | point-count zeta, $Z(T)/Z(T/3)$, $\zeta(s)/\zeta(s+1)$ |

## 3. Language

- **Effectivity function**: real $h$ with the Riemann inequality; **linear / quadratic** RR by the degree of $\chi$.
- **Hilbert–Samuel**: quadratic growth along the ample ray, forced by any quadratic RI.
- **Abundance rate**: least growth of $h(nx)+h(\kappa-nx)$; equals $\max(0,\tfrac12x^2)$.
- **Naive height**: function bounded below at bounded distance from a degree-two form. **Convex height**: midpoint-convex
  function at bounded distance.
- **Soft**: holding on every datum of a family (every characteristic, every polar surface), hence carrying no arithmetic.
- **Integrality floor / analytic ceiling**: $|n|\ge1$ for nonzero integers vs size bounds of the auxiliary.
- **Torsion characteristics**: roots of unity on $\mathbb R/\mathbb Z$; **arithmetic point**: $a=0$ (or $q=1$).
- **Renormalized energy**: positive Abel energy minus the divergent diagonal $\log\frac1{1-r}$.
- **Gap domain**: fundamental domain of $\mathbb A/K$ built from the single Weierstrass gap at $\infty$.

## 4. Mechanisms

**A. Effectivity calculus**
1. RI along $nx$: $\chi(nx)=\tfrac{n^2}2x^2-O(n)$; if $x\cdot A=0$, $x^2>0$, quadratic growth contradicts degree-zero bounds ⇒ Hodge
   index. Conversely $\max(0,\chi)$ with the level bound from $x^2\le2(x\cdot H)(x\cdot V)$.
2. Affine growth in $|x\cdot A|$ cannot satisfy a quadratic RI (Hilbert–Samuel along $nA$).

**B. Heights from counting**
3. Tate: geometric series of increments $\le C/4^{n+1}$; parallelogram survives the limit; bounded below ⇒ $q\ge0$;
   finite sublevel sets ⇒ Northcott.
4. Rounding principle: $\lfloor nc\rfloor/n\to c$ ⇒ integer-nonnegative quadratic forms are real-nonnegative.
5. Cauchy–Schwarz for counts: $\log\sum w_ie^{a_iJ}$ is midpoint convex ⇒ convex heights.
6. Completing the square in $\vartheta(J,t)$: $\log\vartheta=\pi J^2/t+O(1)$ uniformly, same quadratic part on every translate.

**C. Integers of the base**
7. $\operatorname{lcm}(1..n+1)\int_0^1P\in\mathbb Z$ (Stepanov over $\mathbb Z$); Nair's $\int_0^1x^m(1-x)^m\le4^{-m}$.
8. $\Lambda(n)=\log\Phi_n(1)=\sum_{\mu\text{ prim}}\log|1-\mu|$ (product formula in $\mathbb Q(\zeta_n)$); $\psi(N)=$ Farey sum of
   $\log(2\sin\pi a)$.
9. Möbius inversion of $\prod_{n\mid d}\Phi_n=[d]_q$: $\log P_N(q)=\sum_dM(\lfloor N/d\rfloor)\log[d]_q$.
10. Ramanujan sums by Möbius inversion of orthogonality: $\sum_{\zeta\text{ prim}}\zeta=\mu(n)$ ⇒ first Fourier coefficient of the
    torsion measure is $M(N)$.
11. Power maps on $\mu_a$ + circle sum $\sum_{\theta^b=1,\theta\ne1}\log|1-\theta|=\log b$ ⇒ $J(a,b)=\gcd\cdot\log\operatorname{lcm}$; double
    Möbius inversion ⇒ orbit intersections (Apostol).
12. $-\log|1-w|=\sum\Re(w^k)/k$ ⇒ torsion energy is a Gram matrix of Ramanujan sums; Schur product with the PSD gcd twist.

**D. Counting reaches short sums**
13. Gauss sums by orthogonality $|\tau|^2=|F|$; completion $\chi(a)\tau(\bar\chi)=\sum\bar\chi(x)e(ax/p)$ + Jordan
    $\sum1/\sin(\pi k/p)\le p(1+\log p)$.
14. Burgess: $2r$-th moment over shifts (Weil bound on $y^2=\prod(x+b_i)$ for non-even tuples, count of even tuples), box
    energy (small congruences are equations), Hölder over fibres, strong induction on length.
15. Vinogradov: residues up to $y$ ⇒ smooth numbers are residues; Mertens window $\sum_{X<q\le X^u}1/q\to\log u$.

**E. Building a base over $\mathbb F_3$**
16. Weights 2, 3 for $x,y$; pole degree $=\deg$ Norm; parity separates the two basis terms; leading-term cancellation.
17. Trace/norm integrality + squarefree $x^3-x$ ⇒ coordinate ring is integrally closed (Dedekind).
18. Dual-number derivation $x\mapsto x+\varepsilon y$, $y\mapsto y+\varepsilon$ ⇒ $dy\ne0$; chart identities ⇒ regular forms $=\mathbb F_3\,dy$.
19. Ideal norm $=3^{\text{pole degree}}$ ⇒ product formula; finite approximation + CRT + pole reduction ⇒ unique gap representative.
20. Weil circle $|T|^2=1/3$ ⇒ no cancellation in $Z(T)/Z(T/3)$; poles on $\Re s=-\tfrac12$.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Hodge index ⇔ RI degree-bounded $h$ ⇔ RI subquadratic $h$ ⇔ no abundant class | `hodgeIndex_tfae` | proved |
| Abundant ⇔ $x^2>0$; least rate $\max(0,\tfrac12x^2)$ | `abundant_iff`, `pair_self_le_two_mul_rate`, `eventually_optimalEffectivity_le` | proved |
| RH ⇔ effectivity function on the scaling surface ⇔ no abundant class | `riemannHypothesis_iff_exists_effectivity`, `riemannHypothesis_iff_no_abundant_class` | proved |
| Theta $h^0$ obeys every linear law, the quadratic RI on no polar surface | `thetaEffectivity_linear_laws`, `thetaEffectivity_not_riemannInequality` | proved |
| Degree-only RI functions exist ⇔ Hodge index | `exists_degree_effectivity_iff_hodgeIndex` | proved |
| Tate limit exists, unique, parallelogram, nonnegative; Northcott | `tendsto_tateSeq`, `tateLimit_parallelogram`, `tateLimit_nonneg`, `isOfFinAddOrder_of_tateLimit_eq_zero` | proved |
| Rosati positivity ⇔ integral ⇔ naive height ⇔ convex height | `orbitHodgeIndex_iff_int`, `orbitHodgeIndex_iff_exists_naiveHeight`, `orbitHodgeIndex_iff_exists_convexHeight` | proved |
| RH ⇔ naive heights ⇔ convex heights for every cycle | `riemannHypothesis_iff_forall_exists_naiveHeight`, `riemannHypothesis_iff_forall_exists_convexHeight` | proved |
| Curves: naive height on $\mathbb Z[F]$ ⇔ unitary; complex fake has counts ≥ 0 and none | `exists_naiveHeight_iff_unitary`, `complexFake_kernelCounts_nonneg_no_naiveHeight` | proved |
| Genus one: naive height ⇔ Hasse; golden datum has none | `genusOne_exists_naiveHeight_iff`, `goldenDatum_no_naiveHeight` | proved |
| Five currencies of effectivity are RH | `riemannHypothesis_effectivity_tfae` | proved |
| Multiplicative base axioms (Beurling, integral zeta, FE) do not give effectivity | `goldenDatum_multiplicative_axioms_not_effective` | proved |
| RH ⇔ $\psi(N)=\chi(\sqrt NA)+O(\sqrt N\log^2N)$ | `riemannHypothesis_iff_logTorsion_sub_eulerChar` | proved |
| Polar box count is RI ⇔ Hodge index; node twist violates RI everywhere | `riemannInequality_polarBoxCount_iff`, `not_riemannInequality_nodeBoxCount` | proved |
| Theta RR with characteristic; free soft polarization $\pi J^2/t$ | `thetaH0_riemannRoch`, `abs_log_thetaChar_sub_le`, `tateLimit_log_thetaChar`, `hasSum_shifted_thetaChar` | proved |
| Stepanov over $\mathbb Z$: $\log(1/\int P)\le\psi(n+1)$; Nair $\psi(2m+1)\ge m\log4$ | `log_inv_integral_le_psi`, `nair_psi_ge`, `horizon_logTorsion_comparable` | proved |
| $\mathbb P^1\times\mathbb P^1$ section count gives the Hodge index | `hyperbolicPlane_hodgeIndex` | proved |
| $\Lambda(n)=\sum\log|1-\mu|$; $\psi(N)$ = Farey sum; RH ⇔ Farey sum $=N+O(\sqrt N\log^2N)$ | `vonMangoldt_eq_sum_log_norm_one_sub`, `psi_eq_fareySum`, `riemannHypothesis_iff_fareySum` | proved |
| $\psi(N)=\sum_dM(\lfloor N/d\rfloor)\log d$; $P_N(1)=\operatorname{lcm}(1..N)$ | `psi_eq_sum_mertens_log`, `sum_log_cyclotomic_eq_mertens`, `horizonPoly_eval_one` | proved |
| $\hat\nu_N(1)=M(N)$; RH ⇔ $\hat\nu_N(1)=O(N^{1/2+\delta})$ | `torsionFourier_eq_mertens`, `riemannHypothesis_iff_torsionFourier` | proved |
| $J(a,b)=\gcd(a,b)\log\operatorname{lcm}(a,b)$; $I(m,mt)=\varphi(m)\Lambda(t)$ | `logEnergy_eq`, `orbitIntersection_eq`, `orbitIntersection_hecke` | proved |
| Weil's prime kernel = renormalized limit of a positive torsion energy | `weilPrimeKernel_renormalized_torsion_energy` | proved |
| Gauss sums $|\tau|^2=|F|$; unit root numbers; Pólya–Vinogradov | `normSq_gaussSum_eq_card`, `norm_rootNumber_eq_one`, `norm_sum_range_le_polyaVinogradov` | proved |
| Odd hyperelliptic curves: effectivity and naive heights unconditionally | `hyperellipticDatum_window_exists_effectivity`, `hyperellipticDatum_exists_naiveHeight` | proved |
| Burgess moment, energy, bound | `sum_pow_two_mul_le`, `burgessEnergy_le`, `abs_burgessS_le` | proved |
| Least quadratic non-residue $\le p^{1/(4\sqrt e)+\varepsilon}$ | `eventually_exists_nonresidue_le` | proved |
| 𝔽₃ base: genus 1, $2g$ zeta zeros on $|T|=3^{-1/2}$ | `geometricGenus_eq_one`, `positiveGenusBaseField_spec` | proved |
| 𝔽₃ base: product formula, local integrals, adelic Haar, unique gap representative | `adelic_product_formula`, `integral_finiteLocalKernel`, `adele_existsUnique_gap_representative` | proved |
| 𝔽₃ base: $\mathbb A/K\cong$ gap domain, Haar probability of covolume 1 | `additiveQuotientHomeomorph`, `adeleHaar_ellipticAdditiveDomain` | proved |
| 𝔽₃ base: every zeta zero is an uncancelled pole of $Z(T)/Z(T/3)$ | `finiteFieldZetaPoleTransfer_spec`, `shiftedZetaQuotient_pole_iff` | proved |

## 6. Tools

**Developed**
- Calculus: `eulerChar_serre`, `eventually_le_of_riemannInequality`, `eulerChar_le_levelBound`,
  `degreeZeroSubquadratic_of_degreeBounded`, `hilbertSamuel_of_riemannInequality`.
- Heights: `abs_tateLimit_sub_le`, `eq_of_two_nsmul_of_bounded`, `exists_naiveHeight_iff_nonneg`, `sum_sum_nonneg_of_int`,
  `logCount_midpoint_convex`, `tateLimit_nonneg_of_midpointConvex`.
- Torsion: `sum_nthRoots_pow`, `ramanujanSum_eq_sum_moebius`, `sum_nthRoots_comp_pow`, `sum_log_norm_sub_nthRoots`,
  `orbitIntersection_formula`, `sum_divisors_twistWeight`, `hasSum_torsionEnergy`.
- Character sums: `mul_gaussSum_inv_eq_sum`, `sum_inv_sin_le`, `card_evenTuples_le`, `card_shift_le`, `sum_gcd_le`,
  `pow_sum_le_holder`, `sum_chiR_ge_vinogradov`, `tendsto_primeRecipSum_window`.
- 𝔽₃ function field: `isIntegral_iff_coordinateRing_image`, `affineIdealNorm_principal`, `exists_scalar_poleDegree_sub_lt`,
  `infinityParameter_isUniformizer`, `finiteAdele_exists_integral_difference`, `completedInfinity_affine_simplePole_remainder`,
  `card_points_eq_closed_place_sum`, `zetaFunction_taylor`, `exists_reducedArithmeticRatio_bound`.

**To build**
- A section count on the scaling surface with quadratic $\chi$, defined from arithmetic, of box-class size $N$.
- A trace-type naive height on $\mathbb Z[G]$ that is nonnegative for an arithmetic reason and not soft.
- Positivity selective at characteristic 0 of the theta surface.
- A regularization of the torsion energy finer than the uniform $\log\frac1{1-r}$ self-energy, recovering Weil's archimedean term.
- The analytic side of the 𝔽₃ base: Tate's thesis (zeta integrals over `adeleHaar`) linking $\mathbb A/K$ to `zeta`.

## 7. Open questions

1. Is there an arithmetic section count on the scaling surface whose growth laws can be proved from its definition?
2. Can the integrality floor of Stepanov over $\mathbb Z$ reach PNT-strength, or is the integer Chebyshev problem the limit?
3. Is there a family of finite groups, one per level, computing $\psi(N)-N$ at the arithmetic point with square-root uniformity?
4. Is every section count with the RI on box classes bounded by a large-sieve count in degree zero?
5. Does a positive structure renormalize to Weil's full form (prime and archimedean parts), not only the prime kernel?
6. Can the 𝔽₃ gap-domain construction be transported to $\mathbb Q$, where the base has no positive-genus surface?
7. Which convex height on $\mathbb Z[G]$ is attached to an arithmetic log-count?

## 8. Traps

| Trap | Fact |
|---|---|
| An effective cone with RR is an effectivity | Effectivity is a growth law of a function; the calculus says what it must do, not how to get it |
| The theta $h^0$ is half of Weil's argument | It obeys every linear law on every surface and the quadratic RI on none |
| A surface $h^0$ is a log-volume of the degree | It must grow like $\chi$: $\chi(\sqrt NA)=N$, a dimension, not $\log N$ |
| Integrality of point counts constrains the sign | Golden datum: Beurling counts, integral zeta, FE, abundant class, no naive height |
| A positive polarization from counting is Weil's | The theta polarization $\pi J^2/t$ is the same at every characteristic: soft |
| Midpoint convexity of log-counts is a new input | Soft on every datum, like cardinality |
| Orders of finite kernels give a naive height | They are determinants; complex fake |
| Integral positivity is weaker than real | Equivalent by rounding |
| The integrality floor reaches the sign | It gives Chebyshev/Nair, comparability of log-torsion and degree only |
| Subtracting the prime-node conditions keeps an effectivity | The node twist violates the RI on every polar surface |
| A positive energy with Weil's prime kernel off-diagonal gives positivity | The sign is lost in the divergent diagonal renormalization |
| Square-root cancellation needs analysis | At each finite level it is a count (Gauss sums, Weil on curves); the open part is uniformity at the arithmetic point |
| Completion transports to $\psi(x)-x$ | Completion needs a period; the arithmetic point has none |

## 9. Context

| Uses | Modules |
|---|---|
| HTGeometry | 9 (Dedekind ideal norms, discrete-valued completions, rank-one local integrals, Hardy Taylor coefficients, fraction-ring derivations) |
| RHTower | 7 (von Koch, hyperelliptic RH and character sums, Mertens, harmonic log bound) |
| ArithmeticCastelnuovoSeveri | 5 (polar and scaling surfaces, curve data, golden datum, Witt integrality) |
| ArithmeticOrientationGeometry, ArithmeticCorrespondencePositivity | 2 each (theta $h^0$, scaling data; kernel counts, base as fixed loss) |
| BiarithmeticGeometry, ArithmeticContinuationAndCriticalEnergy | 1 each (horizon period jumps; divisor convolution) |

| Used by | Modules |
|---|---|
| ArithmeticIntersectionTheory | 5 (torsion orbits, renormalized torsion energy) |
| ArithmeticElectrostatics | 3 (torsion energy, log-energy of roots of unity) |
| CriticalArithmeticCorrelationTheory | 3 (torsion Fourier coefficients, orbit intersections) |
| RenormalizedBiarithmeticGeometry | 3 (renormalized torsion energy, torsion measure) |
| ArithmeticOfSquareRootPrecision, SelectivePositivityAndThresholdLaws, HTGeometry, RHTower | 2 each (Stepanov, hyperelliptic calibration; effectivity calculus, theta surface; 𝔽₃ zeta bounds/continuation; torsion characteristics, 𝔽₃ zeta) |
| TransThresholdPairCorrelation, ArithmeticLorentzianGeometry | 1 each |

| Neighbour | Relation |
|---|---|
| ArithmeticCastelnuovoSeveri | effective cones are tautological there; AET moves effectivity to growth laws of functions |
| ArithmeticCorrespondencePositivity | its Weil layers L1–L6; AET gives L5 as naive heights and L6 (fixed loss) as one of five currencies |
| ArithmeticPolarization | positivity from symmetry and collision; AET is positivity from counting |
| ArithmeticOrientationGeometry | supplies the theta $h^0$ of the base; AET shows it never extends to a surface |
| ArithmeticIntersectionTheory, ArithmeticElectrostatics | continue the torsion-orbit intersection theory of the prime side |
| ArithmeticOfSquareRootPrecision | continues the integrality lattice of the horizon and curve calibration of the exponent |

## 10. Big picture

AET asks where an $h^0$ for the arithmetic surface could come from, and answers with a sharp split. Every quantity that can
be written down from counting turns out to be either soft (the theta polarization, convexity of log-counts, cardinalities —
true for every datum, hence silent about $\zeta$) or exactly as strong as RH (an effectivity function, a naive height, a
log-torsion law at square-root precision, a fixed tensor loss). Nothing intermediate appears. The single integrality
inequality of the base, $|n|\ge1$, reaches Chebyshev-size statements and no further.

At the same time the prime side of Weil's formula turns out to be genuine intersection theory: von Mangoldt is the
intersection number of torsion orbits on the circle, computed by cyclotomic resultants and equivariant under Hecke, and the
Weil prime kernel is the renormalized limit of a positive energy — the sign is lost precisely in the renormalization. And at
each finite level square-root cancellation is a count (Gauss sums, Weil on curves, Burgess). For the RH programme this says
that the missing object is uniformity across levels at the arithmetic point: a structure that counts $\psi(N)-N$ or
regularizes the torsion energy without spending the sign. The complete 𝔽₃ base shows what such a structure has over a
function field: a positive-genus curve, a gap domain of covolume one, and a zeta function whose zeros survive as poles.
