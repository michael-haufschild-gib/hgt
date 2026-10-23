# Arithmetic Castelnuovo–Severi Theory (`GaloisForLFunctions.ArithmeticCastelnuovoSeveri`)

**One question.** Weil proved the Riemann hypothesis for curves over `𝔽_q` by reading the zeta
function as an intersection theory on `C × C` and the positivity of its explicit formula as the
Hodge index theorem of that surface. Which ingredients of that proof exist for `ℤ`, which are
provably absent, and what would a proof of the missing ones have to produce?

Arithmetic Castelnuovo–Severi theory (ACS) is the intersection theory of the **scaling surface** of
`ℤ`: cycles are the pole plane `⟨H, V⟩` (the directions `e^{∓u/2}`) together with Weil tests, the
pairing is the local side of the explicit formula, the Castelnuovo–Severi defect is Weil's form,
and the Hodge index theorem is RH (`scalingSurface_hodgeIndex_iff`). The surface is a vector space
with a pairing, not a constructed scheme. The programme measures its gap to `C × C` ingredient by
ingredient, calibrated over `𝔽_q`, every statement unconditional.

**The open core.** Of the two inputs of Castelnuovo–Severi, the scaling surface has **Bézout
positivity** — distinct effective cycles meet nonnegatively (`localPair_nonneg`) — but not the
**Riemann–Roch** supply of effective cycles in every class of positive square. Such a supply with
ample degrees is equivalent to RH (`riemannHypothesis_iff_exists_effectivity`); no independent
arithmetic source of it is known. The failure of the Hodge index is measured exactly: its defect
is the number of zeros right of the critical line (`zeta_hodgeDefect_iff`).

---

## Place in the research

| Programme | Connection |
|---|---|
| [Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md) | Supplies the Weil–Markov–pole form whose positivity is the Hodge index property. |
| [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | Ratio atoms give the Hecke incidence; its crossing kernels are the collar on the lattice. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Visibility laws for the Weil form; here they become the degree filtration of the Hodge defect. |
| [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | What a bounded reading can see; ACS supplies the calibrated hiding examples over `𝔽_q` and `ℚ`. |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Additive and valuation structure; consecutive integers have no prime Hecke intersection. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Adversarial models; fake curves separate span data from unitarity. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) | The same sign through ground energies; ACS counts it through the signature. |
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | The comb's mean field; why squared majorants exceed the signed pairing. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Exact finite identities versus critical-norm estimates; successor boundaries. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Quantitative transport of positivity; a geometric form still needs a producer. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Keeps the Möbius source when passing from incidence to quadratic forms. |

`RHTower` supplies the explicit formula, the Weil criterion, the Lévy–Khintchine form of the
archimedean symbol and the matrix inertia calculus.

---

## 1. Why

Weil's proof on `C × C` has five ingredients: (i) an intersection pairing; (ii) fibres `H, V` with
`H² = V² = 0`, `H·V = 1`; (iii) Frobenius graphs with `Γ·Δ = #C(𝔽_q)` (Lefschetz); (iv)
`Γ² = q(2 − 2g)` (adjunction); (v) Riemann–Roch on the surface, which forces the Hodge index
theorem. Hodge index gives `D² ≤ 2(D·H)(D·V)`, and on `D = mΓ + nΔ` the bound `|N − q − 1| ≤ 2g√q`.

Over `ℤ` (i)–(iv) are exact: the pole plane is the hyperbolic plane, the prime comb is Lefschetz,
the archimedean term is adjunction. Over `𝔽_q` the same span identities hold for **fake** data that
violate RH, so they cannot force the sign. Weil's sign comes from the ambient surface: effective
divisors are zero sets of sections, they meet nonnegatively, and Riemann–Roch supplies enough of
them. ACS isolates which of these mechanisms the scaling surface has.

---

## 2. What: objects and language

### 2.1 The dictionary

| Weil's proof over `𝔽_q` | The scaling surface of `ℤ` | Lean |
|---|---|---|
| surface `C × C`, pairing | cycles `aH + bV + f`, pairing from the explicit formula | `scalingSurface` |
| fibres `H, V` | pole plane; `f·H = ∫ f e^{−u/2}`, `f·V = ∫ f e^{u/2}` | `PolarSurface`, `poleRow` |
| defect `2(D·H)(D·V) − D²` | Weil's form `W(f, f)` | `scalingSurface_defect_self` |
| Hodge index | Weil positivity = RH | `scalingSurface_hodgeIndex_iff` |
| Frobenius graphs `Γ_k` | Hecke cycles `g(· − log a)` | `heckeIncidence` |
| Lefschetz numbers | prime comb `Λ(n) n^{−1/2}` at `log n` | `graphPair`, `localGram_apply` |
| adjunction `Γ_k² = q^k(2 − 2g)` | archimedean term (Gamma factor) | `graphPair_self`, `localGram_apply` |
| genus `2g` | zero count (infinite) | `eq_zero_of_paperFT_vanish` |
| Bézout: distinct curves meet `≥ 0` | disjoint nonnegative tests meet `≥ 0` | `localPair_nonneg` |
| Riemann–Roch ⇒ Hodge index | effectivity with RR and ample axioms | `exists_effectivity_iff_hodgeIndex` |
| number of eigenvalues `|α| > √q` | number of zeros with `Re ρ > ½` | `pontryagin_law_curve`, `pontryagin_law` |

### 2.2 Objects

| Object | Meaning | Lean |
|---|---|---|
| Polar surface | cycles with symmetric pairing, isotropic `H, V`, `H·V = 1` | `PolarSurface` |
| Defect, primitive part | `δ(x, y) = (x·H)(y·V) + (x·V)(y·H) − x·y`; projection off `⟨H, V⟩` | `defect`, `prim` |
| Curve datum | `q > 1`, normalized eigenvalues `β` closed under `β ↦ β̄` and `β ↦ β⁻¹` | `CurveDatum` |
| Span defect | defect of `Σ d_k Γ_k`, a Toeplitz form in `Re Σ_i β_i^{|k−l|}` | `spanDefect`, `toeplitz`, `spanGram` |
| Fake curves | golden datum (`β = φ, φ⁻¹`, `q = 5`); hiding datum | `goldenDatum`, `hidingDatum` |
| Zero configuration | reflection-symmetric multiset of points in the strip; tempered if `Σ m/(1 + |γ|²) < ∞` | `ZeroConfig`, `TemperedConfig` |
| Intersection Gram | Gram of `H, V, f₁ … f_n` | `intersectionGram`, `localGram`, `zeroGram` |
| Hodge defect | negative squares of `W`; at degree `a`: on tests supported in `[−a, a]` | `hermNegIndex`, `hodgeDefectAt` |
| Effectivity | a set of cycles with the Riemann–Roch and ample axioms | `RiemannRochAxiom`, `AmpleAxiom` |
| Effective cycle | nonnegative real test; without common component: disjoint supports | `localPair` |
| Hecke incidence, tower form | prime part of the pairing of Hecke cycles | `heckeIncidence`, `towerForm` |

### 2.3 Words

* **Degree and aperture.** Ample degree is the pairing with `H + V`; aperture is the support bound
  of a test, the analogue of a Frobenius window. Effectivity axioms concern the first, visibility
  the second.
* **Hodge defect.** The number of negative squares of Weil's form, equivalently the excess
  positive squares of the intersection form beyond the pole plane.
* **Unitary, fake.** A curve datum is unitary when `|β_i| = 1` (RH for the datum); a fake datum has
  the span data of a curve but is not unitary.
* **Kronecker rank.** The rank of the frequencies of the zeta function: one for curves (periodic
  zeros), finite for exponential polynomials, infinite for `ζ`.
* **Collar.** The archimedean part of the pairing of two cycles; in jump form an integral against
  the Lévy density `ω(x) = e^{−x/2}/(1 − e^{−2x})`.

---

## 3. How: the pillar theorems

### 3.1 The polar surface and Weil's step (`PolarSurfaceHodgeIndex`, `AdjunctionThresholdLaw`)

1. `x·y = (x·H)(y·V) + (x·V)(y·H) + x°·y°`; four equivalent forms of Hodge index; under it the
   defect obeys Cauchy–Schwarz, the only inequality of Weil's proof (`pair_eq_polar_add_prim`,
   `hodgeIndex_tfae`, `defect_sq_le_of_hodgeIndex`, `hodgeIndex_iff_no_positive_plane`).
2. **Adjunction carries the bound.** A configuration of `Γ, Δ` is realizable on a Hodge surface iff
   its defect Gram is positive semidefinite; with `Γ² = q(2 − 2g)` this is Hasse–Weil, with `Γ²` free
   it bounds nothing, and only `Γ² ≥ q(2 − 2g)` is used (`realizable_iff`,
   `realizable_adjunction_iff`, `realizable_of_free_selfIntersection`,
   `sq_le_of_realizable_of_selfIntersection_ge`).

### 3.2 Calibration over `𝔽_q`

3. **The span defect is Weil's form**, a Toeplitz form in the power sums
   (`spanDefect_eq_toeplitz`); genus zero makes it vanish (`spanDefect_eq_zero_of_genusZero`).
4. **Hodge index on the span is RH for the datum** (`hodgeIndexOnSpan_iff_unitary`).
5. **Pontryagin law over `𝔽_q`.** The span defect is the number of distinct eigenvalues outside
   the unit circle, reached once the window holds the spectrum (`≤ 2g`); Hodge index on the window
   `2g` is RH (`pontryagin_law_curve`, `negIndex_spanGram_mono`,
   `unitary_iff_negIndex_spanGram_eq_zero`). The span Gram is the reflected evaluation form
   `Σ_i conj E_x(β_i) E_y(1/β̄_i)` (`spanGram_sesq`).
6. **Three Hodge index theorems coincide.** For a curve datum in the strip the zeros
   `q^{ρ−½} = β_i` form a periodic tempered configuration, and RH for the datum, span Hodge index at
   window `2g`, and Hodge index of its scaling surface are equivalent (`curve_hodgeIndex_tfae`). The
   defects differ: the span counts each outer eigenvalue once, the scaling surface once per period
   (`curveConfig_rightZeros_infinite_iff`). The span is the quotient of the scaling surface by the
   period.
7. **Contact law.** For unitary data the window of `n` graphs is positive definite iff `n ≤ #{β}`;
   beyond, the radical is the multiples of the reduced characteristic polynomial
   (`toeplitz_pos_on_window_iff`, `exists_radical_of_lt`).
8. **Fake curves.** The golden datum has integral point counts, a rational zeta function with
   functional equation, and Hodge defect exactly `1` (`goldenDatum_spanDefect_neg`,
   `goldenDatum_negIndex_spanGram`). Its zeta series is integral (Witt integrality is not purity,
   `witt_integral_not_pure`), and its point counts come from nonnegative integral prime counts of a
   subshift (`goldenDatum_beurling_not_pure`): a rank-one Beurling system can satisfy every listed
   arithmetic constraint and fail the Hodge index.
9. **Window law.** Finitely many windows cannot see a deep eigenvalue unless the genus is
   exponential in the window (`two_mul_genus_ge_of_window`, `exists_hidden_on_window`).

### 3.3 The scaling surface (`TheScalingSurface`, `ArithmeticHodgeIndexSignatureLaw`)

10. The scaling surface is a polar surface with defect Weil's form; its Hodge index is RH
    (`scalingSurface`, `scalingSurface_hodgeIndex_iff`).
11. **Signature law.** `#positive squares(H, V, f₁ … f_n) = 1 + #negative squares(W(f_i, f_j))`
    (`posIndex_intersectionGram`); RH iff one positive square on every family
    (`riemannHypothesis_iff_one_positive_square`). For a general prime weight the signature is
    correct iff RH holds and the weight is `Λ` (`one_positive_square_iff_vonMangoldt`).

### 3.4 The Pontryagin law: the Hodge defect counts the right zeros

12. **Exact law.** For every tempered configuration the largest number of negative squares of
    Weil's form on a finite family of tests is `#{distinct ρ : Re ρ > ½}` in `ℕ∞`
    (`pontryagin_law`; finite and finitely-many-right-zeros cases `pontryagin_law_finite`,
    `pontryagin_law_of_tempered`). For `ζ`: the Hodge defect of the scaling surface is the number of
    zeros right of the line (`zeta_hodgeDefect_iff`, `zeta_rightZeros_infinite_iff`).
13. **Reflection sectors.** On `ρ ↦ 1 − ρ` symmetric configurations the even and odd sectors carry
    `#{Re ρ > ½, Im ρ > 0}` and `#{Re ρ > ½, Im ρ ≥ 0}`; for `ζ` each carries half
    (`sector_pontryagin_law`, `zeta_sector_hodgeDefect_iff`).
14. **Degree filtration.** The defect at degree `a` is monotone and exhausts the right zeros
    (`iSup_hodgeDefectAt`); it vanishes iff Weil's form is nonnegative at aperture `a`
    (`hodgeDefectAt_eq_zero_iff`). For `ζ` it is `0` through degree `3/10`
    (`zeta_hodgeDefectAt_eq_zero`), in the odd sector through `181/500`
    (`SchurLendingOddHodgeIndexPastFirstPrime`).
15. **Visibility and hiding.** An isolated pair `½ ± δ + iγ₀` in an on-line lattice of density `L`
    is seen exactly from the degree where `sinh(2δa)/δ = 2L + 2a` (`hodgeDefectAt_isolatedPair`);
    for every degree some configuration with a right zero has defect `0` there
    (`exists_hidden_at_degree`). Over `𝔽_q` the window `2g` sees everything; over `ℚ` no degree does.
16. **Kronecker-rank dichotomy.** Vertically recurrent configurations have defect `0` or `∞`
    (`recurrent_pontryagin_dichotomy`); periodic ones and those cut out by exponential polynomials
    of any finite rank recur (`verticallyRecurrent_of_periodic`, `expPoly_zero_recurs`,
    `expPoly_pontryagin_dichotomy`). A finite nonzero number of off-line zeros needs infinite rank.

### 3.5 Effectivity and Bézout (`HodgeIndexFromEffectivity`, `DistinctEffectiveCyclesMeetNonnegatively`, `BezoutEffectivityAndTheBeurlingObstruction`)

17. **Hodge index ⟺ an effectivity with the Riemann–Roch and ample axioms**
    (`exists_effectivity_iff_hodgeIndex`); for `ℤ` this is RH
    (`riemannHypothesis_iff_exists_effectivity`). Under the Hodge index the effectivities are
    classified (`effectivity_iff`), and every Riemann–Roch effectivity with nonnegative degrees
    contains the open positive cone (`openPositiveCone_subset_of_effectivity`).
18. **Positivity is not effectivity.** The pole quadrant times any scaling-closed proper set of
    tests fails Riemann–Roch (`productCone_not_riemannRoch`, `posTestCone_not_riemannRoch`).
19. **Bézout positivity holds.** The collar of two cycles has the jump form
    `A(0)∫fg + ∫_0^∞ ω(x)∫(f(u) − f(u+x))(g(u) − g(u+x))` (`re_archCross_eq`); for effective cycles
    without common component the intersection is prime incidence plus collar, both positive
    (`localPair_eq_of_disjoint`), hence `≥ 0` (`localPair_nonneg`). Self-intersections carry the
    negative genus term `A(0)‖f‖²`. Bézout together with Riemann–Roch gives the Hodge index on any
    polar surface (`exists_bezout_effectivity_iff_hodgeIndex`).

### 3.6 Infinite genus (`InfiniteGenusLaw`)

20. No nonzero compact test has a transform vanishing at all but finitely many simple critical
    zeros (`eq_zero_of_paperFT_vanish`); RH iff Weil's form is positive definite
    (`riemannHypothesis_iff_weil_positive_definite`). The finite-field radical has no exact
    counterpart; near-radicals remain.

### 3.7 Hecke incidence and the successor cell

21. **Cartesian law.** Two Hecke cycles meet through the primes only when their exponent vectors
    differ in one coordinate `p`, with weight `τ_p(|v_p(a) − v_p(b)|)`: the prime part is a product
    of one tower per prime (`heckeIncidence_eq_towerWeight`, `heckeForm_box_eq`).
22. **Resonators.** On `{p, q}`-boxes the cross-prime remainder against the Euler envelopes is
    negative definite (`resonatorRemainder_neg`); positivity there comes from the collar and the
    pole.
23. **Mean field.** The cross-prime aggregate of wide odd tests is a mean field of size `≍ N`, and
    no polynomial adjunction bound holds (`not_exists_polynomial_adjunction_bound`).
24. **The successor cell `[log k, log(k+1)]`.** Its pole mass is the pronic weight `1/(k(k+1))`
    (`integral_successorCell`); its two Hecke cycles have no prime incidence and meet through the
    collar alone, `≈ ω(log(1 + 1/k)) = (k+1)√(k(k+1))/(2k+1)` per unit mass
    (`successor_localPair_bounds`, `archLevyDensity_log_succ`). Over `𝔽_q[T]` the cell is
    degenerate (`successorCell_functionField`).

---

## 4. Mechanisms

* **Compute the pairing, then read the sign.** Every positivity statement is a term of an exact
  identity: polar decomposition, Toeplitz law, signature law, Lévy jump form.
* **Count squares.** The pole plane has one positive and one negative square; every other
  positive square of the intersection form is a zero right of the line.
* **Interpolate at the zeros.** Negative squares are built by tests whose transforms are `1` at a
  right zero, `−1` at its reflection and small elsewhere (Lagrange over `𝔽_q`, density in `ℓ²` over
  `ℚ`).
* **Polarize the archimedean form.** Cross terms of the collar come from the Lévy–Khintchine
  splitting applied to `f ± g`.
* **Quotient by the period.** Over `𝔽_q` the Frobenius span is the scaling surface modulo the
  vertical period; finite rank gives recurrence, recurrence gives defect `0` or `∞`.

---

## 5. Traps

| Trap | What is true instead |
|---|---|
| Adjunction is the missing ingredient | It is present and exact (the archimedean term); the missing one is Riemann–Roch. |
| Weil needs `Γ²` exactly | Only `Γ² ≥ q(2 − 2g)` is used; without any value of `Γ²` the Hodge index bounds nothing. |
| Hodge index follows from span data | Fake data satisfy all span identities, integrality and the Beurling structure, and fail it. |
| Positive tests are effective cycles | They meet each other nonnegatively (Bézout) but fail Riemann–Roch. |
| `riemannHypothesis_iff_exists_effectivity` is progress | It is a reformulation; progress is an ampleness proof that does not use the sign of the form. |
| Multiplicities count | The defect counts distinct right zeros; depth and multiplicity are invisible. |
| A finite degree certifies positivity | No degree works for all configurations over `ℚ`; over `𝔽_q` the window `2g` does. |
| The comb aggregate is an intersection number | On resonators the prime intersection has no cross-prime terms; the aggregate is a mean-field shadow. |
| The pronic weight is the successor intersection | It is the pole mass of the cell; the intersection is the collar `ω(log(1 + 1/k)) ≍ k/2`. |

---

## 6. Open problems

1. **Riemann–Roch for `ℤ` — the open core.** A notion of section on the scaling surface whose
   effective classes have nonnegative ample degree by definition and which supplies effective
   cycles in every class of positive square. Bézout is available (19); the supply is RH-equivalent
   (17) and cannot come from positive tests (18) or from exact annihilators (20).
2. **Near-radical count (Landau–Widom).** The two-sided law for `h⁰_ε(L)`, the dimension of
   aperture-`L` tests with `|W| ≤ ε‖f‖²`, unconditionally in its upper half, and the rate
   `−log μ(L) ≍ 2π² N(T*)/log N(T*)` for configurations on the line. Known: lower bounds
   (`zeta_weil_near_radical_dimension_smooth`, `RHTower.zeta_weil_near_radical_sharp_count`).
3. **Aperture over `ℚ`.** The degree at which `n` right zeros become visible, with explicit
   constants depending on the local density (exact for an isolated pair, impossible uniformly).
4. **The collar between towers.** On rank-`P` boxes the towers couple through the collar and the
   pole only; bound this coupling against `Σ_p E_p` and decide positivity of the
   finite-Euler-product form on lattice tests.
5. **λ-ring over `ℚ`.** Adams operations on the scaling surface whose Frobenius graphs are the
   Hecke cycles, with the pole plane splitting off as over `𝔽_q`.
6. **The constant `2/3`.** Why rank–trace inertia gives `2/3` of the zeros simple and on the line,
   and no more; it comes from the pair-correlation input, not from the form.

---

## 7. Success criteria and contributions

**The programme succeeds** when the scaling surface carries an effectivity whose ampleness is proved
without the sign of the form and which satisfies Riemann–Roch, or when it is proved that no cone
definable from a stated class of arithmetic data has both — in either case reducing over `𝔽_q` to
Weil's argument.

**A contribution must**

* be an unconditional Lean theorem in this folder, wired into the umbrella;
* name the ingredient of Weil's proof it concerns, in the language of cycles, pairing, defect and
  effectivity;
* state what it gives for fake curve data, for a non-`Λ` weight and for positive tests;
* run first over `𝔽_q` and reduce there to Weil's argument;
* give an identity wherever Weil's step is an identity, and record the positive survivor of every
  no-go.

---

## 8. Principles

1. **Compute, then bound.**
2. **Audit the hypotheses**: every positivity argument must use a constraint that fake data violate.
3. **Fix the source, not the sign**: the weight is `Λ`, the pole has weight one.
4. **Calibrate over `𝔽_q`.**
5. **Separate metrology from geometry**: what a degree can see versus what a cycle is.
6. **Search the corpus first**: `scripts/formal_tools.py research "<query>"`.

---

## Source entry points

| Module | Content |
|---|---|
| `PolarSurfaceHodgeIndex` | polar surfaces, defect, four forms of Hodge index, Cauchy–Schwarz |
| `AdjunctionThresholdLaw` | realizability, Hasse–Weil from adjunction, free self-intersection |
| `FrobeniusSpanCalibration` | curve data, Lefschetz and adjunction, span defect = Toeplitz form |
| `FrobeniusSpanHodgeIndexIsRH` | Hodge index on the span ⟺ unitarity |
| `FakeCurvesAndTheWindowLaw` | golden datum, window visibility and hiding |
| `WittIntegralityIsNotPurity` | zeta series and ghost components; integrality versus purity |
| `TheGoldenCurveIsABeurlingSystem` | orbit counting for subshifts; the golden curve as a Beurling system |
| `SpanContactLaw` | contact window = number of distinct eigenvalues |
| `TheFrobeniusSpanDefectCountsTheOuterEigenvalues` | Pontryagin law over `𝔽_q` |
| `TheScalingSurfaceOfACurve` | zeros of a curve datum; three equivalent Hodge index theorems |
| `HodgeIndexFromEffectivity` | Riemann–Roch and ample axioms ⟺ Hodge index; classification |
| `BezoutEffectivityAndTheBeurlingObstruction` | Bézout + Riemann–Roch ⟺ Hodge index; graph cone; subshift obstruction |
| `DistinctEffectiveCyclesMeetNonnegatively` | collar in Lévy jump form; Bézout positivity of effective cycles |
| `TheScalingSurface` | the scaling surface of `ℤ`; Hodge index ⟺ RH; positivity is not effectivity |
| `ArithmeticHodgeIndexSignatureLaw` | signature law, selection of `Λ`, Pontryagin bound |
| `InfiniteGenusLaw` | no exact transform annihilators; RH ⟺ positive definite |
| `FiniteConfigurationPontryaginLaw` | transform interpolation; exact law for finite configurations |
| `TemperedConfigurationPontryaginLaw` | tempered configurations; dual tests and translated pairs |
| `TheHodgeDefectCountsTheRightZeros` | the exact Pontryagin law; Hodge defect of `ζ` |
| `TheReflectionSectorsOfTheHodgeDefect` | even and odd sector laws |
| `TheDegreeFiltrationOfTheHodgeDefect` | Hodge defect by degree; `ζ` below `3/10` |
| `SchurLendingOddHodgeIndexPastFirstPrime` | odd-sector Hodge index of `ζ` through `181/500` |
| `TheVisibilityDegreeOfAnIsolatedPair` | degree Hodge index = aperture positivity; isolated pair; hiding over `ℚ` |
| `TheKroneckerRankDichotomy` | recurrent configurations have defect `0` or `∞` |
| `TheZerosOfAnExponentialPolynomialRecur` | recurrence of zeros of exponential polynomials |
| `ResonatorKroneckerLaw` | Kronecker law of resonators, additive envelopes |
| `HeckeIncidenceCartesianLaw` | Cartesian law: the prime part is a product of towers |
| `TheResonatorRemainderIsNegative` | cross-prime remainder on resonators is negative definite |
| `TheAdjunctionConjectureMeanField` | mean-field law; no polynomial adjunction bound |
| `ThePronicWeightIsThePoleMassOfTheSuccessorCell` | pronic weight = pole mass of the successor cell |
| `TheSuccessorCollar` | collar bounds; consecutive Hecke cycles meet through the collar alone |
