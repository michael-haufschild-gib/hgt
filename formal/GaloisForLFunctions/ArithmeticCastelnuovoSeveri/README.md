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
is the number of distinct zeros right of the critical line (`zeta_hodgeDefect_iff`), and the whole
defect already lives on the Hecke orbit of a single test (`cyclic_pontryagin_law`), as over `𝔽_q`
it lives on the Frobenius orbit of the diagonal.

---

## Place in the research

| Programme | Connection |
|---|---|
| [Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md) | Supplies the Weil–Markov–pole form whose positivity is the Hodge index property. |
| [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | Ratio atoms give the Hecke incidence; the reflected-prime/polar allocation gives the odd-sector ledger of §3.10. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Visibility laws and the zero width; here they become the degree filtration and the degree-floor law. |
| [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | What a bounded reading can see; ACS supplies the calibrated hiding examples over `𝔽_q` and `ℚ`. |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Additive and valuation structure; consecutive integers have no prime Hecke intersection. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Adversarial models; fake curves separate span data from unitarity. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) | The same sign through ground energies; ACS counts it through the signature. |
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | The comb's mean field; why squared majorants exceed the signed pairing. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Exact finite identities versus critical-norm estimates; successor boundaries. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Quantitative transport of positivity; a geometric form still needs a producer. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Keeps the Möbius source when passing from incidence to quadratic forms. |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Takes this surface as its geometric core. Its width dictionary places Hodge index, effectivity and one positive square beside the other units, and its Nyquist rank bound on section spaces is the finite-dimensional shadow of the missing Riemann–Roch. |
| [Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md) | The analytic engine of the second route to `3/4` in §3.8: it decomposes `RHTower.PrimeSurplusFourThirds` into a Dirichlet mean value and a close-pair kernel. |

`RHTower` supplies the explicit formula, the Weil criterion, the Lévy–Khintchine form of the
archimedean symbol and the matrix inertia calculus.

**The shared target.** The programmes in the table work on RH as the sign of one critical arithmetic
form. ACS reads that sign as the Hodge index of the scaling surface and asks for the geometric input
that produced it over `𝔽_q`: an effectivity with Riemann–Roch supply. Every positivity route of the
corpus — incidence, lag, aperture — meets the same form; ACS contributes the exact count of its
failure (right zeros), its localization on one Hecke orbit, the calibration over `𝔽_q`, and the fake
data any forcing argument must exclude. Read §§1–2 for the dictionary, §3 for the pillar theorems,
§5 for the traps and §§6–7 for the questions and open problems.

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
| fibres `H, V` | pole plane; `f·H = ∫ f e^{−u/2}`, `f·V = ∫ f e^{u/2}` | `PolarSurface`, `poleB`, `poleA` |
| defect `2(D·H)(D·V) − D²` | Weil's form `W(f, f)` | `scalingSurface_defect_self` |
| Hodge index | Weil positivity = RH | `scalingSurface_hodgeIndex_iff` |
| Frobenius graphs `Γ_k` | Hecke cycles `T_a Δ_g`, translates `g(· − log a)` | `heckeCycle`, `translate` |
| Frobenius orbit of `Δ` | Hecke orbit of one spectrally generic test | `cyclic_pontryagin_law` |
| Lefschetz numbers | prime comb `Λ(n) n^{−1/2}` at `log n` | `graphPair`, `arithLefschetz_split` |
| adjunction `Γ_k² = q^k(2 − 2g)` | archimedean collar (Gamma factor, Lévy jump form) | `graphPair_self`, `re_archCross_eq` |
| genus `2g` | zero count (infinite) | `eq_zero_of_paperFT_vanish` |
| Bézout: distinct curves meet `≥ 0` | disjoint nonnegative tests meet `≥ 0` | `localPair_nonneg` |
| Riemann–Roch ⇒ Hodge index | effectivity with RR and ample axioms | `exists_effectivity_iff_hodgeIndex` |
| number of eigenvalues `|α| > √q` | number of distinct zeros with `Re ρ > ½` | `pontryagin_law_curve`, `pontryagin_law` |

### 2.2 Objects

| Object | Meaning | Lean |
|---|---|---|
| Polar surface | cycles with symmetric pairing, isotropic `H, V`, `H·V = 1` | `PolarSurface` |
| Defect, primitive part | `δ(x, y) = (x·H)(y·V) + (x·V)(y·H) − x·y`; projection off `⟨H, V⟩` | `defect`, `prim` |
| Curve datum | `q > 1`, normalized eigenvalues `β` closed under `β ↦ β̄` and `β ↦ β⁻¹` | `CurveDatum` |
| Span defect | defect of `Σ d_k Γ_k`, a Toeplitz form in `Re Σ_i β_i^{|k−l|}` | `spanDefect`, `toeplitz`, `spanGram` |
| Fake curves | golden datum (`β = φ, φ⁻¹`, `q = 5`); hiding datum | `goldenDatum`, `hidingDatum` |
| Zero configuration | reflection-symmetric multiset of points in the strip; tempered if `Σ m/(1 + |γ|²) < ∞` | `ZeroConfig`, `TemperedConfig` |
| Intersection Gram | Gram of `H, V, f₁ … f_n` | `intersectionGram`, `zeroGram` |
| Hodge defect | negative squares of `W`; at degree `a`: on tests supported in `[−a, a]` | `hermNegIndex`, `hodgeDefectAt` |
| Spectrally generic test | a test whose transform vanishes at no zero | `SpectrallyGeneric` |
| Effectivity | a set of cycles with the Riemann–Roch and ample axioms | `RiemannRochAxiom`, `AmpleAxiom` |
| Effective cycle | nonnegative real test; without common component: disjoint supports | `localPair` |
| Hecke incidence, tower form | prime part of the pairing of Hecke cycles | `heckeIncidence`, `towerForm` |
| Odd degree-`r` subsurface | pole plane and odd tests supported in `[−r, r]` | `scalingSubsurface`, `oddRealTestsAt` |

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
* **Zero width.** `sup |Re ρ − ½|` over the zeros of `ζ` (`zetaZeroWidth`); RH is width `0`.

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
15. **Visibility and hiding.** Over `𝔽_q` the window `n_0 + 2 n_+ ≤ 2g` sees all `n_+` outer
    eigenvalues (`card_spectrum_eq_onCircle_add_two_mul_outer`, `negIndex_spanGram_eq_of_onCircle`).
    Over `ℚ`, an isolated pair `½ ± δ + iγ₀` in an on-line lattice of density `L` is seen exactly
    from the degree where `sinh(2δa)/δ = 2L + 2a` (`hodgeDefectAt_isolatedPair`). For `n` pairs,
    any subset `S` whose complement has total pair energy `Σ_{k∉S} (sinh(2δ_k a)/δ_k − 2a) ≤ L`
    bounds the defect by `|S|` (`re_W_multiPairConfig`, `hodgeDefectAt_multiPairConfig_le`,
    `exists_n_hidden_at_degree`). Conversely, with dual tests on `[−a₀, a₀]`
    (`exists_dual_tests_Icc`), all right zeros are visible at `a ≥ a₀ + Δ` once
    `2 · onLineMass Z b + ½ ≤ cosh((Re ρ − ½)Δ) − 1` (`hodgeDefectAt_eq_of_onLineMass`,
    `hodgeDefectAt_eq_of_log_onLineMass`), with explicit on-line mass under lattice, unit-window
    and logarithmic densities (`onLineMass_multiPairConfig_eq`, `hodgeDefectAt_eq_of_locallyBounded`,
    `card_le_hodgeDefectAt_of_visible_pairs`, `zeta_intersectionGram_posIndex_ge_of_visible_pairs`).
    Under a uniform unit-window count `N(t, t + 1] ≤ D`, the height cutoff `H_m` drops out completely
    and `n` separated right zeros at arbitrary heights become visible at the height-uniform degree
    `0 < uniformVisibleMargin D a δ R` (`card_le_hodgeDefectAt_of_uniform_window_count`; cluster
    visibility in a logarithmic background `one_le_hodgeDefectAt_of_isolated_cluster`). For `ζ`, the
    local off-line density `OffLineCopiesLocallyBounded M` of Square-Root Threshold bounds the
    off-line multiplicity in every unit-radius window (`sum_mult_offLine_window_le_of_offLineCopiesLocallyBounded`,
    `offLineDensityBound_zeta_of_offLineCopiesLocallyBounded`), replaces the companion count
    `P = ⌈80 log(180 Γ)⌉` around any near-top record by the height-independent constant `M` and the
    core mass bound by `2 M (e^{w/2} B_w)²` (`zeta_near_top_cluster_collapse_of_offLineCopiesLocallyBounded`,
    `zeta_near_top_visible_of_offLineCopiesLocallyBounded`), and makes the Castelnuovo–Severi
    degree-defect floor rate on `scalingSubsurface` equal to `zetaZeroWidth` unless the off-line
    zeros cluster without bound (`zetaZeroWidth_le_iff_scalingSubsurface_odd_defect_floor_of_offLineCopiesLocallyBounded`,
    `scalingSurface_defectRate_eq_zetaZeroWidth_or_offLine_cluster`).
    Over `𝔽_q` the window `2g` sees everything; over `ℚ` no degree does (`exists_hidden_at_degree`).
16. **Kronecker-rank dichotomy.** Vertically recurrent configurations have defect `0` or `∞`
    (`recurrent_pontryagin_dichotomy`); periodic ones and those cut out by exponential polynomials
    of any finite rank recur (`verticallyRecurrent_of_periodic`, `expPoly_zero_recurs`,
    `expPoly_pontryagin_dichotomy`). A finite nonzero number of off-line zeros needs infinite rank.
17. **The defect is cyclic** (`TheHodgeDefectIsCyclic`). For a test whose transform vanishes at no
    zero (such tests exist, `exists_spectrallyGeneric`), the translates `g(· − d)` by any shifts `d`
    dense in `[0, ∞)` carry the whole Hodge defect (`cyclic_pontryagin_law`): one Hecke orbit sees
    every right zero, as the Frobenius orbit of `Δ` does over `𝔽_q`. The proof is a density
    theorem — coordinates of translates are dense in `ℓ²(Z)` because an exponential sum
    `Σ q_τ e^{(τ̄ − ½)v}` vanishing on a dense set of `v ≥ 0` vanishes identically
    (`eq_zero_of_orthogonal_translates`). For `ζ` the rational Hecke orbit `log ℚ_{>0}`, and
    already the two-prime orbit `ℤ log p + ℤ log q`, suffice; RH iff the Weil Gram matrices of these
    translates of one test are positive semidefinite (`zeta_cyclic_hodgeDefect_iff`,
    `riemannHypothesis_iff_ratHecke_negIndex_eq_zero`,
    `riemannHypothesis_iff_twoPrime_negIndex_eq_zero`). A single prime tower `g(· − k log p)` is
    the period quotient (`TheHeckeTowerOfAPrimeIsThePeriodQuotient`): its Gram matrix is Toeplitz,
    `T_{p^k}` multiplies the coordinate at `ρ` by the Frobenius eigenvalue `p^{ρ − ½}`, and when the
    outer eigenvalues are finitely many the tower defect is exactly the number of them with nonzero
    Frobenius weight `W_b = Σ_{p^{ρ−½} = b} X_ρ(g) conj X_{1−ρ̄}(g)` (`tower_pontryagin_law`);
    in general it is at most the number of distinct outer eigenvalues (`negIndex_towerGram_le`).
    Zeros differing by `2πi/log p` share an eigenvalue and their weights can cancel, as over `𝔽_q`
    each outer eigenvalue is counted once. Over `ℚ` this is rare: two distinct zeros collide at no
    more than one prime, since two would make `log q / log p` rational
    (`subsingleton_resonantPrimes`). With finitely many right zeros, all but finitely many primes
    separate them, and at each such prime one tower of one generic test carries the whole defect
    (`almost_every_prime_tower_sees_every_right_zero`).

### 3.5 Effectivity and Bézout (`HodgeIndexFromEffectivity`, `DistinctEffectiveCyclesMeetNonnegatively`, `BezoutEffectivityAndTheBeurlingObstruction`)

18. **Hodge index ⟺ an effectivity with the Riemann–Roch and ample axioms**
    (`exists_effectivity_iff_hodgeIndex`); for `ℤ` this is RH
    (`riemannHypothesis_iff_exists_effectivity`). Under the Hodge index the effectivities are
    classified (`effectivity_iff`), and every Riemann–Roch effectivity with nonnegative degrees
    contains the open positive cone (`openPositiveCone_subset_of_effectivity`).
19. **Positivity is not effectivity.** The pole quadrant times any scaling-closed proper set of
    tests fails Riemann–Roch (`productCone_not_riemannRoch`, `posTestCone_not_riemannRoch`):
    `H + V + εg` has positive square for small `ε`, and a sign-changing `g` keeps it and its
    negative out of the cone.
20. **Cones defined by the form are tautological.** The closed positive cone satisfies the
    Riemann–Roch axiom and the open positive cone the ample axiom on every polar surface; the other
    axiom of each is the Hodge index (`positiveCone_riemannRoch`, `positiveCone_ample_iff_hodgeIndex`,
    `openPositiveCone_ample`, `openPositiveCone_riemannRoch_iff_hodgeIndex`,
    `strictCoupledArithmeticCone_riemannRoch_iff_hodgeIndex`). Membership in either cone already
    uses the sign of `x²`; an effectivity has to be defined without it.
21. **Bézout positivity holds.** The collar of two cycles has the jump form
    `A(0)∫fg + ∫_0^∞ ω(x)∫(f(u) − f(u+x))(g(u) − g(u+x))` (`re_archCross_eq`); for effective cycles
    without common component the intersection is prime incidence plus collar, both positive
    (`localPair_eq_of_disjoint`), hence `≥ 0` (`localPair_nonneg`). Self-intersections carry the
    negative genus term `A(0)‖f‖²`. Bézout together with Riemann–Roch gives the Hodge index on any
    polar surface (`exists_bezout_effectivity_iff_hodgeIndex`).

### 3.6 Infinite genus (`InfiniteGenusLaw`)

22. No nonzero compact test has a transform vanishing at all but finitely many simple critical
    zeros (`eq_zero_of_paperFT_vanish`); RH iff Weil's form is positive definite
    (`riemannHypothesis_iff_weil_positive_definite`). The finite-field radical has no exact
    counterpart among compact tests; near-radicals remain.

### 3.7 Hecke incidence and the successor cell

23. **Cartesian law.** Two Hecke cycles meet through the primes only when their exponent vectors
    differ in one coordinate `p`, with weight `τ_p(|v_p(a) − v_p(b)|)`: the prime part is a product
    of one tower per prime (`heckeIncidence_eq_towerWeight`, `heckeForm_box_eq`).
24. **Resonators.** On `{p, q}`-boxes the cross-prime remainder against the Euler envelopes is
    negative definite (`resonatorRemainder_neg`); positivity there comes from the collar and the
    pole.
25. **Mean field.** The cross-prime aggregate of wide odd tests is a mean field of size `≍ N`, and
    no polynomial adjunction bound holds (`not_exists_polynomial_adjunction_bound`).
26. **The successor cell `[log k, log(k+1)]`.** Its pole mass is the pronic weight `1/(k(k+1))`
    (`integral_successorCell`); its two Hecke cycles have no prime incidence and meet through the
    collar alone, `≈ ω(log(1 + 1/k)) = (k+1)√(k(k+1))/(2k+1)` per unit mass
    (`successor_localPair_bounds`, `archLevyDensity_log_succ`). Over `𝔽_q[T]` the cell is
    degenerate (`successorCell_functionField`).

### 3.8 Rank–trace inertia: what a Gram functional can certify (`TheTwoThirdsConstantIsPairCorrelation`, `BreakingTheCoalescenceBlindSpotAndThreeQuarters`, `SpectralSlackConservationAndTheHyperbolicDisplacementThreshold`)

Without Riemann–Roch effectivity the intersection form still certifies a *proportion* of zeros,
through rank–trace inertia on the real evaluation Gram `Â = P + Q` of hat-unit tests — `P` from the
critical-line zeros, `Q` from the off-line pairs — with `tr Â = N` and `‖Â‖_F² = κN`. Inertia
replaces the Hodge index `p = 0` by `n₊(Q) ≤ p`.

27. **Capacity `2 − κ` and the coalescence blind spot.** At `c = 2` a double critical zero and a
    coalescing off-line pair produce the identical rank-one matrix `2vvᵀ`
    (`offLine_sub_doubleZero_weight`, `blockA_coalescedPair_eq_doubleZero`). The form certifies
    `(2 − κ)N` simple critical zeros (`unitary_calibration_full_simple` at `κ = 1` over `𝔽_q`;
    `κ ≥ 2` on fake curves with `s₁ = 0`, `goldenDatum_rankTrace_barrier`), and no functional of
    `(Â, N)` alone certifies more (`universal_matrix_functional_barrier`). Below the square-root
    threshold `κ(λ) = 1/λ + λ/3`, so the certificate is at most `2/3`, with equality only at `λ = 1`
    (`subthreshold_cert_le_two_thirds`, `universal_matrix_functional_barrier_at_two_thirds`). This is
    the intersection-theoretic reading of Alpöge–Furman's two-thirds theorem
    (`RHTower.thmA_lam_spectralSlack`): `2/3` is set by stopping pair correlation at `λ = 1`, and a
    finite pair-correlation bound `F ≤ B` beyond `λ = 1` gives `2/3 + 1/(3(3B − 2))`
    (`two_thirds_and_pair_correlation_escape`).
28. **Two routes past the blind spot, each with one unproved input, and the exact spectral-slack
    conservation laws.** The pair `(P, Q)` remembers what `Â` forgets: for `Q = 0` the on-line
    Parseval slack restores the rank at `c = 2` (`onSlack_of_posSemidef_eq`,
    `rank_trace_add_onSlack_of_posSemidef_eq_rank`), and a non-coalesced off-line pair carries
    negative-part credit (`negPart_credit_pos_iff_not_posSemidef`). More generally, adding the full
    spectral slack `totalSlack(P, Q, c) := c tr(Q₋) + posSlack(Q, c) + onSlack(P, Q, c)` to
    `c tr P + 2c tr Q − c² n₊(Q) − ‖P + Q‖_F²` cancels the prime-side quadratic functional
    identically and equals `(c²/4) rank P − couplingDefect(P, Q, c) ≤ (c²/4) rank P`
    (`rank_trace_add_totalSlack_eq`, `zeroside_rank_core_slack_exact`,
    `zeroside_rank_core_slack_le_rank`). Because `P̂(T)` has grid dimension `d(T) = (λ + o(1))N(T, 2T)`,
    `zeroSideSlack(λ, T) ≤ (λ − H(λ) + ε)N(T, 2T)` unconditionally (`seamA_spectralSlack_le_d`,
    `zeroSideSlack_eventually_le_lam_sub_Hfun`), refuting `zeroSideSlack(λ, T) ≥ (3/4 − H(λ))N(T, 2T)`
    for every `λ ∈ (0, 3/4)` (`not_three_quarters_zeroSideSlack_of_lt_three_quarters`). On the
    off-line block, Cauchy–Schwarz amplifies `tr(Q₋) ≥ 2ηb` into `posSlack(Q, 2) ≥ 4η²b` and
    `2 tr(Q₋) + posSlack(Q, 2) ≥ 4bη(1 + η)` (`posSlack_mul_ge_sq_of_rtrace`,
    `offLine_slack_ge_of_rtrace_hermNegPart`). In the hyperbolic displaced-pair block model at
    `κ = 4/3` (`displacedPairBlockData`), non-coalescence (`η > 0`, `2 tr(Q₋) > 0`) is necessary
    but not sufficient for `3/4`: at `s₁ = 179, p = 32, α = √(17/16), β = 1/4` (`N = 243`),
    `2 tr(Q₋) > 0` while `s₁ = (179/243)N < (3/4)N` and `totalSlack < (1/12)N`
    (`displacedPairBlockData_below_three_quarters`,
    `macroscopic_displacedPair_counterexample_at_four_thirds`), and the three exact macroscopic
    thresholds at `κ = 4/3` are `(1 + 2η)² ≥ 4/3` for `s₁ ≥ (3/4)N`, `η ≥ 1/6` for
    `totalSlack ≥ (1/12)N`, and `(1 + 2η)² ≥ 2` for off-line slack `≥ (1/12)N`
    (`hyperbolic_displacedPair_three_thresholds_at_four_thirds`). The joint `(c = 2, c = 3)`
    functional is `((7 − 3κ)/4)N`, i.e. `(3/4)N` at `κ = 4/3`
    (`three_quarters_of_broken_blind_spot_at_four_thirds`). For `ζ` this gives two conditional
    bridges: `zeroSideSlack(λ, T) ≥ (3/4 − H(λ))N(T, 2T)` for `λ ∈ [3/4, 1)`
    (`zeta_three_quarters_of_spectralSlack`), or `RHTower.PrimeSurplusFourThirds` filling the `1/18`
    margin above `43/36 = 5/4 − 1/18` at `λ = 4/3` (`kappa_five_fourths_iff_three_quarters`,
    `zeta_three_quarters_from_prime_surplus`, `double_window_primeFreq_offDiag_and_exchange_rate`).

### 3.9 The λ-ring of the scaling surface (`TheLambdaRingOfTheScalingSurface`)

29. **Adams operations, Hecke cycles and the pole-plane splitting.** `polarPart` and `prim` are
    orthogonal idempotents splitting any polar surface into the pole plane and the primitive
    complement with pairing `−defect` (`polarPart_add_prim`, `pair_orthog_split`). The Newton–Witt
    exponential `sigmaSeries` is a `λ`-ring exponential splitting any trace `(1 + q^j) + g_prim(j)`
    into the pole factors times `sigmaSeries g_prim` (`sigmaSeries_pole_split`); over `𝔽_q` this is
    `zetaSeries = poleZeta · hOnePoly` (`CurveDatum.sigmaSeries_pointCount_split`). Over `ℚ` the
    normalized Adams operators `adamsOp q` are exact intersection, polar and defect isometries
    commuting with the splitting (`pair_adamsOp`, `defect_adamsOp`, `prim_adamsOp`). The Hecke
    correspondences `T_a = √a · adamsOp a` satisfy `T_a H = aH`, `T_a V = V`, and the Hecke cycles
    obey `Γ_a(g) · Γ_b(g) = b · L(Δ_g, a/b)` (`pair_heckeCycle`), `p^{min(k,l)} L(Δ_g, p^{|k−l|})` on a
    prime tower (`pair_heckeCycle_pow`). The arithmetic Lefschetz number splits as
    `(a + 1)(x·H)(x·V) − √a · defect(adamsOp a x, x)` (`arithLefschetz_split`); narrow bumps at
    integer scales read the prime comb as the Hecke incidence
    (`weightedPrimeComb_scaleShift_eq_heckeIncidence`); `scaleShift (log q)` multiplies the readout
    at `ρ` by `q^{ρ − 1/2}` (`paperFT_scaleShift_gammaOf`). Frobenius, graphs and Lefschetz numbers
    exist on the scaling surface; Riemann–Roch does not follow from them, and the golden datum obeys
    the same identities (`goldenDatum_lambdaRing_and_not_unitary`).

### 3.10 The odd-sector ledger and the degree floor (`RiemannRochForZAndTheReflectedPrimePolarLedger`)

30. **Lorentz–polar identity.** `2 B(F) A(F) = 2 evenPoleMoment(F)² − poleCharge(F)`
    (`two_mul_poleB_mul_poleA_eq_lorentz_moments`); on odd tests the pole charge `2 A(F)²` is the
    negative self-intersection of the polar projection `A(F)(H − V)`
    (`poleCharge_eq_two_mul_poleA_sq_of_odd`).
31. **Exact ledgers on the odd degree-`r` subsurface.** For every `r > 0` and plateau radius
    `R > r`, the defect of a cycle with odd test `f` supported in `[−r, r]` is a sum of nonnegative
    plateau-gauge terms plus a bounded remainder, minus the reflected-prime/polar cost
    (`scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger`). In that cost the `e^r` main
    terms of the prime comb and the pole charge cancel, leaving the two-pole Chebyshev remainder
    `E(s) = e^s + s − 1 − ψ(e^s)` on `(0, 2r]` against the lag correlations of `f`
    (`scalingSubsurface_odd_defect_eq_chebyshevDefectLedger`), or its second-order prefix form
    (`scalingSubsurface_odd_defect_eq_criticalScalePrefixLedger`). These are identities: the explicit
    formula rewritten on the odd subsurface.
32. **The degree floor measures the zero width.** Unconditionally
    `δ(x, x) ≥ −((8 + ε) e^r + C) ∫ f²` at every degree (`exists_scalingSubsurface_odd_defect_ge_neg_eight_add_eps_mul_exp`;
    coarse form `−78 e^r ∫ f²`). A floor `−C e^{2σ r} ∫ f²` at all degrees forces
    `|Re ρ − ½| ≤ σ` for every zero (`zetaZeroWidth_le_of_scalingSubsurface_odd_defect_floor`), so
    RH is equivalent to a subexponential floor and to a bounded floor
    (`rightZeros_zeta_eq_empty_iff_subexponential_scalingSubsurface_odd_defect_floor`,
    `rightZeros_zeta_eq_empty_iff_bddBelow_scalingSubsurface_odd_defect`). This is the classical
    dictionary between error exponents and zero-free strips, read as the growth rate of the defect
    floor in the degree: the unconditional floor has rate `σ = ½`, any power saving would be a
    zero-free strip. Through degree `181/500` the odd floor is `0`
    (`strictCoupledArithmeticCone_odd_riemannRoch_of_le_threeHundredSixtyTwoThousandths`).

---

## 4. Mechanisms

* **Compute the pairing, then read the sign.** Every positivity statement is a term of an exact
  identity: polar decomposition, Toeplitz law, signature law, Lévy jump form, odd-sector ledger.
* **Count squares.** The pole plane has one positive and one negative square; every other
  positive square of the intersection form is a zero right of the line.
* **Interpolate at the zeros.** Negative squares are built by tests whose transforms are `1` at a
  right zero, `−1` at its reflection and small elsewhere (Lagrange over `𝔽_q`, density in `ℓ²` over
  `ℚ`).
* **Localize on one orbit.** Translates of one generic test are already dense on the zero side;
  uniqueness of exponential sums replaces the choice of tests.
* **Polarize the archimedean form.** Cross terms of the collar come from the Lévy–Khintchine
  splitting applied to `f ± g`.
* **Keep the pole with the primes.** On odd tests the pole charge and the prime comb share their
  `e^r` main term; only together do they leave the Chebyshev remainder.
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
| `riemannHypothesis_iff_exists_effectivity` is progress | It is a reformulation; progress is an effectivity defined without the sign of the form, with ampleness and Riemann–Roch supply proved from that definition. |
| The open positive cone settles ampleness | Its ample axiom is vacuous (`x·(H + V) > 0` on the cone) and its membership uses the sign of `x²`; its Riemann–Roch axiom is the Hodge index. Likewise for the closed cone with the axioms exchanged. |
| A subexponential defect floor is a reduction of RH | It is equivalent to RH (§3.10): the floor rate is the zero width. A power saving in the floor is a zero-free strip, as hard as quasi-RH. |
| The odd-sector ledger is a positivity mechanism | It is the explicit formula rewritten; the sign is still carried by `E(s) = e^s + s − 1 − ψ(e^s)`. |
| The cyclic law is a positivity statement | It localizes the defect on one Hecke orbit; it does not bound it. |
| Multiplicities count | The defect counts distinct right zeros; depth and multiplicity are invisible. |
| A finite degree certifies positivity | No degree works for all configurations over `ℚ`; over `𝔽_q` the window `2g` does. |
| The comb aggregate is an intersection number | On resonators the prime intersection has no cross-prime terms; the aggregate is a mean-field shadow. |
| The pronic weight is the successor intersection | It is the pole mass of the cell; the intersection is the collar `ω(log(1 + 1/k)) ≍ k/2`. |
| The three-quarters modules prove that 75% of the zeros are on the line | They prove `(3/4)N` *conditionally*: on a zero-side slack `S(T) ≥ N/12`, or on `PrimeSurplusFourThirds`. The unconditional content is `(2/3 − ε)N + S(T) ≤ N₀*` with the slack retained, the `43/36` diagonal constant and the `O(T^{5/6}log²T)` cross term. |
| Adams operations make the scaling surface a Weil surface | They give Frobenius, graphs and Lefschetz numbers; the golden datum has them too. Riemann–Roch is still missing. |
| The rank–trace form is capped at `2/3` | The form has capacity `2 − κ` (reaching `1` at `κ = 1`); `2/3` is `2 − κ(1)` from stopping pair correlation at `λ = 1`. |

---

## 6. Questions the programme answers and the tools it builds

### 6.1 Questions

1. **Which ingredients of Weil's proof exist for `ℤ`?** The pairing, the fibres, Lefschetz,
   adjunction, Bézout positivity, Adams operations and Hecke graphs: all exact. Riemann–Roch: absent,
   and its existence with ample degrees is RH.
2. **What does the failure of the Hodge index measure?** The number of distinct zeros right of the
   line, filtered by degree, split by reflection sector, and carried by the Hecke orbit of any one
   generic test; never depth or multiplicity. The growth of the defect floor in the degree is the
   zero width.
3. **Which arithmetic data force the sign?** Not span data, integrality, functional equation or
   positive Euler data — the golden datum has all of them and fails. A forcing input must be
   violated by such fake data.
4. **What can a Gram functional certify without effectivity?** A proportion `2 − κ`, capped at `2/3`
   below pair correlation at `λ = 1`, with two named inputs that would reach `3/4`.
5. **What would an effectivity for `ℤ` have to be?** A cone defined without the sign of the form,
   with Riemann–Roch supply and ample degrees proved from that definition, reducing over `𝔽_q` to
   Weil's. Cones read off the form are tautological (§3.5, item 20).

### 6.2 Tools

Built and reusable:

- *Polar surfaces*: defect, primitive projection, four forms of the Hodge index, realizability.
- *The `𝔽_q` calibration*: curve data, span Toeplitz forms, the Pontryagin law, fake curves, Witt and
  Beurling structure.
- *The scaling surface* with its signature law and the Pontryagin law over tempered configurations,
  reflection sectors and the degree filtration.
- *Visibility calculus* of right zeros from on-line mass, local and logarithmic density.
- *The Kronecker-rank dichotomy* and exponential-polynomial recurrence.
- *Cyclic density*: spectrally generic tests, density of one Hecke orbit on the zero side, the
  cyclic Pontryagin law, inertia under rectangular congruence.
- *Bézout positivity* through the Lévy jump form of the collar.
- *Hecke incidence*: the Cartesian law, resonators, the successor cell.
- *Rank–trace inertia* with spectral slack.
- *The `λ`-ring*: Adams operations, Hecke correspondences and cycles, arithmetic Lefschetz numbers.
- *The odd-sector ledger*: Lorentz–polar identity, reflected-prime/polar and Chebyshev ledgers,
  degree floors and the zero width.

To be built:

- a notion of section on the scaling surface with Riemann–Roch supply and an ampleness proof that does
  not use the sign of the form;
- an effectivity stable under the Hecke correspondences;
- the near-radical count of Landau–Widom type;
- a bound on the coupling of prime towers through the collar on rank-`P` boxes.

---

## 7. Open problems

1. **Riemann–Roch for `ℤ` — the open core.** A notion of section on the scaling surface whose
   effective classes have nonnegative ample degree by definition and which supplies effective
   cycles in every class of positive square. Bézout is available (21); the supply is RH-equivalent
   (18) and cannot come from positive tests (19), from cones read off the form (20), or from exact
   annihilators among compact tests (22). Of the routes to Wall 14 this is the only one whose
   removal criterion is a construction, not an estimate. The constraints on a construction are
   known: the cone must contain the open positive cone, be Bézout-closed and Hecke-stable, and use
   a constraint the golden datum violates, which means the additive structure of `ℤ`. One
   candidate is a count. Take for `h⁰` the dimension of aperture-`A`, height-`T` tests vanishing
   on the prime-power nodes of the box, and seek `h⁰ ≥ (degrees of freedom) − (node count)` with
   the error identified as the Chebyshev defect `E(s)`. The corpus already proves Landau-density
   statements of this kind: prime-blind tests, whose autocorrelation vanishes at every `log n`,
   with vanishing even pole moment have spectral second moment above `99/4` times their mass
   (`ninety_nine_fourths_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero`). The
   classical shadow of such a count is the `T + N`
   term of the mean value theorem, with diagonal at the square-root threshold. A section count
   that is no stronger than the large sieve at the diagonal would only relabel Dirichlet
   polynomials; a useful one must be selective against the golden datum and the shifted pair.
2. **Near-radical count (Landau–Widom).** The two-sided law for `h⁰_ε(L)`, the dimension of
   aperture-`L` tests with `|W| ≤ ε‖f‖²`, unconditionally in its upper half, and the rate
   `−log μ(L) ≍ 2π² N(T*)/log N(T*)` for configurations on the line. Known: lower bounds
   (`zeta_weil_near_radical_dimension_smooth`, `RHTower.zeta_weil_near_radical_sharp_count`).
3. **Aperture over `ℚ`.** The degree at which `n` right zeros become visible is explicit in terms
   of on-line mass, local density and logarithmic density (item 15); no degree works uniformly over
   all configurations. Under a uniform window count `N(t, t + 1] ≤ D`, separated right zeros at
   arbitrary heights become visible at the height-uniform degree `0 < uniformVisibleMargin D a δ R`
   (`card_le_hodgeDefectAt_of_uniform_window_count`). For `ζ`, under the local off-line density
   `OffLineCopiesLocallyBounded M` of Square-Root Threshold, the companion count around any near-top
   record is `≤ M` and the core mass bound is `2 M (e^{w/2} B_w)²` uniformly in height
   (`zeta_near_top_cluster_collapse_of_offLineCopiesLocallyBounded`,
   `zeta_near_top_visible_of_offLineCopiesLocallyBounded`), and the Castelnuovo–Severi degree-defect
   rate on `scalingSubsurface (oddRealTestsAt r)` equals `zetaZeroWidth` unless off-line copies
   cluster without bound (`scalingSurface_defectRate_eq_zetaZeroWidth_or_offLine_cluster`). Open for
   `ζ`: eliminating the residual `log γ₀` factor in the Riemann–von Mangoldt tail of the Turán
   inequality without bounded on-line density.
4. **The collar between towers.** On rank-`P` boxes the towers couple through the collar and the
   pole only; bound this coupling against `Σ_p E_p` and decide positivity of the
   finite-Euler-product form on lattice tests.
5. **Effectivity from the `λ`-ring.** The Adams operations, Hecke correspondences and the pole-plane
   splitting exist (§3.9). Open: a cone of cycles stable under the Hecke correspondences, with
   nonnegative ample degree and Riemann–Roch supply, built from them. The second question — whether
   the Lefschetz identity constrains the defect beyond the signature law — is answered by the cyclic
   law: the defect is generated by the Hecke orbit of any spectrally generic cycle (item 17).
6. **Beyond `2/3`.** The constant is explained: capacity `2 − κ` at `λ = 1` (§3.8). Open: either input
   that gives `3/4` — a zero-side spectral slack `S(T) ≥ N(T, 2T)/12`, or the prime surplus
   `RHTower.PrimeSurplusFourThirds` at bandwidth `4/3` — or pair correlation beyond `λ = 1`.
7. **One prime against two.** Two primes carry the whole defect; one prime carries the visible
   outer eigenvalues `p^{ρ − ½}` when these are finitely many, and with finitely many right zeros
   every non-resonant prime carries all of it (item 17). Open: the tower defect when infinitely many
   outer eigenvalues accumulate in the annulus `1 < |β| < √p`, where the moment separation of
   classes fails.

---

## 8. Success criteria and contributions

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

## 9. Principles

1. **Compute, then bound.**
2. **Audit the hypotheses**: every positivity argument must use a constraint that fake data violate.
3. **Fix the source, not the sign**: the weight is `Λ`, the pole has weight one.
4. **Calibrate over `𝔽_q`.**
5. **Separate metrology from geometry**: what a degree can see versus what a cycle is.
6. **Do not mistake a reformulation for a reduction**: an RH-equivalent condition is a target, not
   progress, unless it is proved from an independent input.
7. **Search the corpus first**: `scripts/formal_tools.py research "<query>"`.

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
| `TheVisibilityDegreeOfRightZeros` | visibility degree of `n` right zeros from on-line mass, local density, and logarithmic density |
| `HeightUniformVisibilityAndOffLineDensity` | height-uniform visibility degree under bounded local count (`uniformVisibleMargin`), off-line companion count `M` and near-top visibility under `OffLineCopiesLocallyBounded M`, Castelnuovo–Severi defect-floor equivalence and clustering alternative |
| `TheKroneckerRankDichotomy` | recurrent configurations have defect `0` or `∞` |
| `TheZerosOfAnExponentialPolynomialRecur` | recurrence of zeros of exponential polynomials |
| `TheHodgeDefectIsCyclic` | Hecke translates, spectrally generic tests, cyclic density, cyclic Pontryagin law, RH on the rational and two-prime Hecke orbits of one test |
| `TheHeckeTowerOfAPrimeIsThePeriodQuotient` | Frobenius eigenvalues `p^{ρ − ½}`, Toeplitz tower Gram, class separation by annihilating polynomials and Cesàro means, Frobenius weights, the tower Pontryagin law |
| `AlmostEveryPrimeSeesEveryRightZero` | coincidence of Frobenius eigenvalues, at most one resonant prime per pair of zeros, finitely many resonant primes, one prime tower carries the whole defect |
| `ResonatorKroneckerLaw` | Kronecker law of resonators, additive envelopes |
| `HeckeIncidenceCartesianLaw` | Cartesian law: the prime part is a product of towers |
| `TheResonatorRemainderIsNegative` | cross-prime remainder on resonators is negative definite |
| `TheAdjunctionConjectureMeanField` | mean-field law; no polynomial adjunction bound |
| `ThePronicWeightIsThePoleMassOfTheSuccessorCell` | pronic weight = pole mass of the successor cell |
| `TheSuccessorCollar` | collar bounds; consecutive Hecke cycles meet through the collar alone |
| `TheTwoThirdsConstantIsPairCorrelation` | `2 − κ` capacity of rank–trace inertia, coalescence indistinguishability, `2/3` from `λ = 1` pair correlation |
| `BreakingTheCoalescenceBlindSpotAndThreeQuarters` | unsplit `(P, Q)` spectral slack, `(7 − 3κ)/4 = 3/4` at `κ = 4/3`, prime-surplus and double-window routes to `75%` |
| `SpectralSlackConservationAndTheHyperbolicDisplacementThreshold` | exact spectral-slack conservation and prime-side cancellation, unconditional grid-dimension ceiling `zeroSideSlack ≤ (λ − H(λ) + ε)N` and refutation on `(0, 3/4)`, Cauchy–Schwarz off-line slack amplification, hyperbolic displaced-pair counterexample and the three exact macroscopic thresholds at `κ = 4/3` |
| `TheLambdaRingOfTheScalingSurface` | `λ`-ring series, Adams operations `adamsOp q`, Hecke cycles `heckeCycle a g`, pole-plane splitting, Lefschetz splitting, zero-side eigenlaw |
| `RiemannRochForZAndTheReflectedPrimePolarLedger` | tautological cones, Lorentz–polar identity, odd-sector reflected-prime/polar and Chebyshev ledgers, `(8 + ε) e^r` floor, degree floor ⟺ zero width |
