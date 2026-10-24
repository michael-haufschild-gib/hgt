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
failure (right zeros), its localization on one Hecke orbit and on one prime tower, the calibration
over `𝔽_q`, and the fake data any forcing argument must exclude. Read §§1–2 for the dictionary, §3
for the pillar theorems, §5 for the traps and §§6–7 for the questions and open problems.

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
| Frobenius eigenvalues `α_i/√q` | `p^{ρ − ½}` on the tower of the prime `p` | `tower_pontryagin_law` |
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
| Prime tower, Frobenius eigenvalue | translates `g(· − k log p)`, `k ∈ ℤ`; `p^{ρ − ½}` | `towerGram`, `frobEig` |
| Effectivity | a set of cycles with the Riemann–Roch and ample axioms | `RiemannRochAxiom`, `AmpleAxiom` |
| Effective cycle | nonnegative real test; without common component: disjoint supports | `localPair` |
| Source section cone | cycles whose pole degrees pay a source energy: `0 ≤ x·H`, `0 ≤ x·V`, `Φ(x) ≤ 2(x·H)(x·V)` (and graded / Sobolev / compensated variants) | `sourceCone`, `gradedSourceCone`, `l2SourceCone`, `sobolevSourceCone`, `l2CompensatedScalingSubsurface` |
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
* **Resonant prime.** A prime at which two distinct right zeros share a Frobenius eigenvalue.
* **Collar.** The archimedean part of the pairing of two cycles; in jump form an integral against
  the Lévy density `ω(x) = e^{−x/2}/(1 − e^{−2x})`.
* **Zero width.** `sup |Re ρ − ½|` over the zeros of `ζ` (`zetaZeroWidth`); RH is width `0`.

---

## 3. How: the pillar theorems

### 3.1 The polar surface and Weil's step (`PolarSurfaceHodgeIndex`, `AdjunctionThresholdLaw`)

1. `x·y = (x·H)(y·V) + (x·V)(y·H) + x°·y°`; four equivalent forms of Hodge index; under it the
   defect obeys Cauchy–Schwarz, the only inequality of Weil's proof (`hodgeIndex_tfae`,
   `defect_sq_le_of_hodgeIndex`).
2. **Adjunction carries the bound.** A configuration of `Γ, Δ` is realizable on a Hodge surface iff
   its defect Gram is positive semidefinite; with `Γ² = q(2 − 2g)` this is Hasse–Weil, with `Γ²` free
   it bounds nothing, and only `Γ² ≥ q(2 − 2g)` is used (`realizable_adjunction_iff`,
   `realizable_of_free_selfIntersection`).

### 3.2 Calibration over `𝔽_q`

3. **The span defect is Weil's form**, a Toeplitz form in the power sums
   (`spanDefect_eq_toeplitz`); genus zero makes it vanish.
4. **Hodge index on the span is RH for the datum** (`hodgeIndexOnSpan_iff_unitary`).
5. **Pontryagin law over `𝔽_q`.** The span defect is the number of distinct eigenvalues outside
   the unit circle, reached once the window holds the spectrum (`≤ 2g`); Hodge index on the window
   `2g` is RH (`pontryagin_law_curve`). The span Gram is the reflected evaluation form
   `Σ_i conj E_x(β_i) E_y(1/β̄_i)` (`spanGram_sesq`).
6. **Three Hodge index theorems coincide.** For a curve datum in the strip the zeros
   `q^{ρ−½} = β_i` form a periodic tempered configuration, and RH for the datum, span Hodge index at
   window `2g`, and Hodge index of its scaling surface are equivalent (`curve_hodgeIndex_tfae`). The
   defects differ: the span counts each outer eigenvalue once, the scaling surface once per period.
   The span is the quotient of the scaling surface by the period, as an identity: Poisson summation
   along each tilted lattice of zeros writes Weil's form as `Σ_i log q · Σ_m (f ⋆ g̃)(m log q) β_i^m`,
   so the `q`-tower of a test supported in an interval shorter than `log q` has Gram matrix
   `log q · ‖g‖² · spanGram`, and tower defect = span defect (`curve_tower_pontryagin_law`).
7. **Contact law.** For unitary data the window of `n` graphs is positive definite iff `n ≤ #{β}`;
   beyond, the radical is the multiples of the reduced characteristic polynomial
   (`toeplitz_pos_on_window_iff`).
8. **Fake curves.** The golden datum has integral point counts, a rational zeta function with
   functional equation, and Hodge defect exactly `1` (`goldenDatum_negIndex_spanGram`). Its zeta
   series is integral (Witt integrality is not purity, `witt_integral_not_pure`), and its point
   counts come from nonnegative integral prime counts of a subshift (`goldenDatum_beurling_not_pure`):
   a rank-one Beurling system can satisfy every listed arithmetic constraint and fail the Hodge index.
9. **Window law.** Finitely many windows cannot see a deep eigenvalue unless the genus is
   exponential in the window (`two_mul_genus_ge_of_window`, `exists_hidden_on_window`).

### 3.3 The scaling surface (`TheScalingSurface`, `ArithmeticHodgeIndexSignatureLaw`)

10. The scaling surface is a polar surface with defect Weil's form; its Hodge index is RH
    (`scalingSurface_hodgeIndex_iff`).
11. **Signature law.** `#positive squares(H, V, f₁ … f_n) = 1 + #negative squares(W(f_i, f_j))`
    (`posIndex_intersectionGram`); RH iff one positive square on every family
    (`riemannHypothesis_iff_one_positive_square`). For a general prime weight the signature is
    correct iff RH holds and the weight is `Λ` (`one_positive_square_iff_vonMangoldt`).

### 3.4 The Pontryagin law: the Hodge defect counts the right zeros

12. **Exact law.** For every tempered configuration the largest number of negative squares of
    Weil's form on a finite family of tests is `#{distinct ρ : Re ρ > ½}` in `ℕ∞` (`pontryagin_law`).
    For `ζ`: the Hodge defect of the scaling surface is the number of zeros right of the line
    (`zeta_hodgeDefect_iff`). The negative squares are built by interpolation — tests whose
    transforms are `1` at a right zero, `−1` at its reflection and small elsewhere — and the upper
    bound is inertia of the zero-side Gram.
13. **Reflection sectors.** On configurations symmetric under `ρ ↦ 1 − ρ` the even and odd tests are
    `W`-orthogonal; the even sector carries the right zeros with `Im ρ > 0`, the odd sector those with
    `Im ρ ≥ 0`, the two add up to the whole count, and for `ζ` each carries half
    (`rightZeros_encard_eq_sectorZeros_add`, `zeta_sector_hodgeDefect_iff`).
14. **Degree filtration and sector additivity.** The defect at degree `a` is monotone, exhausts the
    right zeros (`iSup_hodgeDefectAt`), and vanishes iff Weil's form is nonnegative at aperture `a`.
    At every degree it is the exact sum of its even- and odd-sector parts
    (`hodgeDefectAt_eq_sectorHodgeDefectAt_add`, by inertia sub- and superadditivity). For `ζ` it is
    `0` through degree `3/10` (`zeta_hodgeDefectAt_eq_zero`) and `0` in the odd sector through
    `181/500`, so any defect of `ζ` below `181/500` is purely even
    (`zeta_hodgeDefectAt_eq_even_sectorHodgeDefectAt_of_le`). The defect is invariant under changes
    of multiplicity and under horizontal depth deformations inside `(½, 1)`
    (`multiPairConfig_depth_invariance`), while the raw `L²` floor scales with the multiplicity
    (`offLineClusterConfig_hodgeDefect_vs_l2_floor`): the defect is a count, the floor a mass.
15. **Visibility and hiding.** Over `𝔽_q` the window `n_0 + 2n_+ ≤ 2g` sees all `n_+` outer
    eigenvalues. Over `ℚ` an isolated pair `½ ± δ + iγ₀` in an on-line lattice of density `L` is seen
    exactly from the degree where `sinh(2δa)/δ = 2L + 2a` (`hodgeDefectAt_isolatedPair`); for `n`
    pairs, any subset whose complement has total pair energy at most `L` bounds the defect by its
    size (`exists_n_hidden_at_degree`); conversely all right zeros are visible once the on-line mass
    near them is below an explicit `cosh` threshold (`hodgeDefectAt_eq_of_onLineMass`), with explicit
    masses under lattice, unit-window and logarithmic densities. Under a uniform unit-window count
    `N(t, t + 1] ≤ D` the visibility degree no longer depends on the heights
    (`card_le_hodgeDefectAt_of_uniform_window_count`). For `ζ`, the local off-line bound
    `OffLineCopiesLocallyBounded M` of Square-Root Threshold makes the near-top visibility constants
    height-uniform and gives the alternative: the degree-defect floor rate equals the zero width
    unless off-line zeros cluster without bound
    (`scalingSurface_defectRate_eq_zetaZeroWidth_or_offLine_cluster`). Over `𝔽_q` the window `2g`
    sees everything; over `ℚ` no degree does (`exists_hidden_at_degree`). On a lag lattice
    (`W(f, f) = ℓ Σ_m k_f(mℓ) D(m)`) the degree filtration *is* the window filtration: the Toeplitz
    law of Square-Root Threshold (`weil_nonneg_iff_toeplitz_of_lagFormula`) decides positivity at
    degree `a` by the window of size `⌈2a/ℓ⌉`, and the failure is never partial — the defect jumps
    from `0` to `∞` (`hodgeDefectAt_lagFormula`, by `W`-orthogonal block tests on separated offsets).
    The scaling surface of a curve is a lag lattice (`W_curveConfig_lagFormula`), so every curve
    has Hodge index up to degree `log q/2`, its defect is `0` or `∞` by purity from the window `2g`
    on, and the golden datum jumps at `log 5/2` (`hodgeDefectAt_curveConfig`,
    `goldenDatum_hodgeDefectAt`); the off-line lattice jumps at its Nyquist degree `L/2`
    (`hodgeDefectAt_offLineLattice`). Over `𝔽_q` the lag family of Square-Root Threshold decides
    purity on its own: the test `g + s·g(· − n log q)` reads only the `n`-th point count,
    `Re W = log q ‖g‖² ((1 + s²)·2g + 2s tₙ)`, so it is never negative on a pure curve and is negative
    at some lag in every window `[M + 1, M + 2g]` past a threshold set by the depth, by Turán's
    power-sum theorem (`re_W_curveConfig_lagTest`, `exists_negative_lagTest_of_window`,
    `exists_negative_lagTest`; golden datum at lag `log 5`). Windows see an impure curve by degree
    `(2g − 1) log q/2` whatever the depth; lags are located only depth-dependently.
16. **Kronecker-rank dichotomy.** Vertically recurrent configurations have defect `0` or `∞`
    (`recurrent_pontryagin_dichotomy`); periodic configurations and zero sets of exponential
    polynomials of any finite rank recur (`expPoly_pontryagin_dichotomy`). A finite nonzero number
    of off-line zeros needs infinite rank.
17. **The defect is cyclic, and one prime nearly suffices.** For a spectrally generic test (one
    exists, `exists_spectrallyGeneric`), the translates by any shifts dense in `[0, ∞)` carry the
    whole defect (`cyclic_pontryagin_law`): an exponential sum `Σ q_τ e^{(τ̄ − ½)v}` vanishing on a
    dense set of `v ≥ 0` vanishes identically. For `ζ` the rational Hecke orbit `log ℚ_{>0}`, and
    already `ℤ log p + ℤ log q`, suffice: RH iff the Weil Gram matrices of these translates of one
    test are positive semidefinite (`riemannHypothesis_iff_twoPrime_negIndex_eq_zero`), and
    symmetrized translates carry each reflection sector separately (`cyclic_sector_pontryagin_law`).
    A single prime tower `g(· − k log p)` is the period quotient: its Gram matrix is Toeplitz,
    `T_{p^k}` multiplies the zero-side coordinate at `ρ` by the Frobenius eigenvalue `p^{ρ − ½}`,
    and when the outer eigenvalues are finitely many the tower defect is exactly the number of
    them with nonzero Frobenius weight (`tower_pontryagin_law`), in general at most the number of
    distinct outer eigenvalues. Zeros differing by `2πi/log p` share an eigenvalue and their weights
    can cancel, as over `𝔽_q`. Over `ℚ` this is rare: two distinct zeros resonate at no more than one
    prime, since two would make `log q / log p` rational. So with finitely many right zeros all but
    finitely many primes separate them, and at each such prime one tower of one generic test
    carries the whole defect (`almost_every_prime_tower_sees_every_right_zero`); weights need not be
    assumed, since one modulated bump has nonzero Frobenius weight at every class of every prime
    (`exists_test_tower_defect_eq_card_frobEig`). Finiteness is not needed: orthogonality to the
    tower is the vanishing of all Laurent moments, and the classes can be extracted from the top
    down by Cesàro means as long as the moduli above them contain no increasing sequence. So if the
    real parts of the right zeros contain no strictly increasing sequence, at every prime the tower
    defect is the number of visible outer eigenvalues, finite or infinite, however they accumulate
    in the annulus (`tower_pontryagin_law_of_wellFounded`, `tower_defect_eq_encard_of_injOn`). An
    attained top is always seen: its visible classes are seen by every prime tower, and a finite
    top level by one generic tower at all but finitely many primes
    (`card_le_towerDefect_of_top`, `almost_every_prime_sees_the_top`); for `ζ` this is the
    `AttainedTop` case of the single-base lag analysis (`RHTower.WeilLagSingleBaseLowerSide`).

### 3.5 Effectivity and Bézout (`HodgeIndexFromEffectivity`, `DistinctEffectiveCyclesMeetNonnegatively`, `SourceDeterminantalSectionsAndArithmeticRiemannRoch`, `AllApertureSourceRiemannRochAndCoercivityLaws`)

18. **Hodge index ⟺ an effectivity with the Riemann–Roch and ample axioms**
    (`exists_effectivity_iff_hodgeIndex`); for `ℤ` this is RH
    (`riemannHypothesis_iff_exists_effectivity`). Under the Hodge index the effectivities are
    classified (`effectivity_iff`), and every Riemann–Roch effectivity with nonnegative degrees
    contains the open positive cone.
19. **Positivity is not effectivity.** The pole quadrant times any scaling-closed proper set of
    tests fails Riemann–Roch (`posTestCone_not_riemannRoch`): `H + V + εg` has positive square for
    small `ε`, and a sign-changing `g` keeps it and its negative out of the cone.
20. **Cones defined by the form are tautological; cones defined by the source are not, and their
    all-aperture structure is completely classified.** The closed positive cone satisfies the
    Riemann–Roch axiom and the open positive cone the ample axiom on every polar surface; the other
    axiom of each is the Hodge index (`positiveCone_ample_iff_hodgeIndex`,
    `openPositiveCone_riemannRoch_iff_hodgeIndex`). Membership in either cone already uses the sign
    of `x²`. A cone can instead be defined from the source alone: `x` is effective when its two pole
    degrees pay a source energy, `Φ(x) ≤ 2(x·H)(x·V)` with `x·H, x·V ≥ 0` — a `2 × 2` determinantal
    condition (`sourceCone`), or in the ample half-space `0 ≤ x·(H + V)` (`gradedSourceCone`).
    * *Universal ampleness rigidity and exact Riemann–Roch equivalence on polar surfaces:* For any
      even fibre-invariant `Φ`, `RiemannRochAxiom (gradedSourceCone Φ) ↔ ∀ x, Φ(x) ≤ defect(x, x)`
      (`gradedSourceCone_riemannRoch_iff_le_defect`, `sourceCone_riemannRoch_iff_le_defect`), while
      strict ampleness (`x ∈ E ∧ x·(H + V) = 0 ⟹ x = 0`) holds on `gradedSourceCone Φ` (or
      `sourceCone Φ`) iff `0 < Φ(x)` on every nonzero primitive cycle, in which case `0 ≤ Φ` and
      `gradedSourceCone Φ = sourceCone Φ` identically (`strictAmple_gradedSourceCone_iff_pos_on_primitive`,
      `gradedSourceCone_eq_sourceCone_of_strictAmple`).
    * *Ampleness vs. coercivity dichotomy for `L²` source cones:* With `Φ = c∫f²`, `l2SourceCone c V`
      is convex, contains `0, H, V, H + V`, is stable under every Adams operation and Hecke
      correspondence (`heckeCorrespondence_mem_l2SourceCone`), satisfies `AmpleAxiom` iff `c > 0`
      (`l2SourceCone_ampleAxiom_iff_pos`, `gradedL2SourceCone_ampleAxiom_iff_pos`), and satisfies
      `RiemannRochAxiom` on `gradedL2SourceCone c V` for all `c ∈ ℝ` iff `c∫f² ≤ W(f, f)`
      (`gradedL2SourceCone_riemannRoch_iff_weilPair_ge`, `l2SourceCone_effectivity_iff`).
    * *Unconditional positive Riemann–Roch past the first prime and graded/compensated Riemann–Roch
      at all apertures:* Uncompensated positive `l2SourceCone` Riemann–Roch holds with `c = 1/200` on
      the ample-orthogonal hyperplane `∫f cosh(u/2) = 0` (mixed parity) through aperture
      `½(log 2 + 1/50)`, past the first prime (`l2SourceCone_primitiveSmooth_riemannRoch_primeTwo`).
      At **all** apertures `r > 0`, because the spectral symbol identity
      `markovEnergy f = Re ∫ |f̂(τ)|² (μ(τ) + P_{e^{2r}}(τ)) dτ` holds for arbitrary `C²` compactly
      supported tests (`markovEnergy_eq_integral_mu_add_PX`) and `2 evenPoleMoment(f)² ≥ 0` enters
      `fullZeroForm` positively, `gradedL2SourceCone` satisfies `RiemannRochAxiom` unconditionally on
      the **entire unrestricted `realTestsAt r`** at `c = -(10 + 72 e^r)`
      (`realTestsAt_scalingSubsurface_defect_ge_neg_ten_add_seventy_two_exp`,
      `gradedL2SourceCone_realTestsAt_all_apertures_riemannRoch`), on `evenRealTestsAt r` and
      `polarFreeSmoothRealTestsAt r` at `-(10 + 68 e^r)`, on `primitiveSmoothRealTestsAt r` at
      `-(10 + 78 e^r)`, and on `oddRealTestsAt r` at `-78 e^r`
      (`gradedL2SourceCone_all_apertures_riemannRoch`; plus the `r = 23/40` two-prime strip-surplus
      allocation `scalingSubsurface_odd_defect_twentyThreeFortieths_stripSurplus_floor` and the
      all-aperture de la Vallée Poussin Sobolev floor
      `exists_scalingSubsurface_odd_defect_deLaValleePoussin_sobolev_floor`). Equivalently, on the
      **compensated polar surface** `l2CompensatedScalingSubsurface κ V` (`compensatedSurface`),
      which preserves `H, V, H + V`, fibre degrees, `polar`, `prim`, and the cones `l2SourceCone c V`
      and `strictL2SourceCone c V` as identical sets of cycles while shifting the pairing by the
      reserve `κ∫fg`, the unmodified cone `l2SourceCone c (realTestsAt r)` (`c > 0`,
      `κ = 10 + 72 e^r + c`) satisfies `RiemannRochAxiom`, non-vacuous `AmpleAxiom`,
      `SurfaceRiemannRochAxiom 0 0`, `BezoutAxiom`, and `HodgeIndex` unconditionally at all
      apertures `r > 0` (`l2CompensatedScalingSubsurface_realTestsAt_all_apertures`,
      `compensatedSurface_hodgeIndex_iff`).
    * *Aperture-dependent coercivity laws, no-Hardy-weight law, doubly-exponential ceiling, and
      strict-monotonicity self-upgrade:* On the uncompensated surface, no aperture-independent
      weighted `L²` cone `∫ W(u)f(u)² du ≤ 2(x·H)(x·V)` (`W ≥ 0` positive on a set of positive
      measure) satisfies `RiemannRochAxiom` at all apertures (`not_forall_aperture_weightedL2SourceCone_riemannRoch`),
      and any `L²` coercivity constant at `r ≥ 3` obeys the unconditional Gaussian ceiling
      `c ≤ K exp((11/2)r − π e^{2(r−2)})` (`exists_l2SourceCone_realTestsAt_coercivity_le_doubleExp`,
      `not_forall_aperture_l2SourceCone_realTestsAt_riemannRoch`,
      `exists_le_floorLoss_of_l2SourceCone_riemannRoch`). On `polarFreeSmoothRealTestsAt r`,
      `RiemannRochAxiom` holds iff `c ≤ μ₀(r) := ccmRestrictedWeilPolarGroundEnergy ⟨r, hr⟩`
      (`polarFreeSmooth_l2SourceCone_riemannRoch_iff`), and because `r ↦ μ₀(r)` is strictly
      decreasing (`strictAnti_ccmRestrictedWeilPolarGroundEnergy`), all-aperture `HodgeIndex`
      (`0 ≤ μ₀(r)`) **unconditionally self-upgrades** to strict positivity `0 < μ₀(r)` and
      simultaneous `RiemannRochAxiom` + non-vacuous `AmpleAxiom` + `SurfaceRiemannRochAxiom 0 0` +
      `BezoutAxiom` for `l2SourceCone (μ₀(r)) (polarFreeSmoothRealTestsAt r)` at every aperture
      (`all_aperture_polarFreeSmooth_hodgeIndex_iff_ample_l2SourceCone`). For the `H¹` Sobolev
      source cones (`sobolevSourceCone`, `gradedSobolevSourceCone`), `zetaZeroWidth ≤ σ` (`σ ≥ 0`)
      holds iff `gradedSobolevSourceCone (-Ce^{2βr})` satisfies `RiemannRochAxiom` at all apertures
      `r > 0` for every `β > σ` (`zetaZeroWidth_le_iff_gradedSobolevSourceCone_riemannRoch`).
21. **Bézout positivity holds.** The collar of two cycles has the jump form
    `A(0)∫fg + ∫_0^∞ ω(x)∫(f(u) − f(u+x))(g(u) − g(u+x))` (`re_archCross_eq`); for effective cycles
    without common component the intersection is prime incidence plus collar, both positive, hence
    `≥ 0` (`localPair_nonneg`). Self-intersections carry the negative genus term `A(0)‖f‖²`. Bézout
    together with Riemann–Roch gives the Hodge index on any polar surface
    (`exists_bezout_effectivity_iff_hodgeIndex`).

### 3.6 Infinite genus (`InfiniteGenusLaw`)

22. No nonzero compact test has a transform vanishing at all but finitely many simple critical
    zeros (`eq_zero_of_paperFT_vanish`); RH iff Weil's form is positive definite
    (`riemannHypothesis_iff_weil_positive_definite`). The finite-field radical has no exact
    counterpart among compact tests; near-radicals remain.

### 3.7 Hecke incidence and the successor cell

23. **Cartesian law.** Two Hecke cycles meet through the primes only when their exponent vectors
    differ in one coordinate `p`, with weight `τ_p(|v_p(a) − v_p(b)|)`: the prime part is a product
    of one tower per prime (`heckeIncidence_eq_towerWeight`).
24. **Resonators.** On `{p, q}`-boxes the cross-prime remainder against the Euler envelopes is
    negative definite (`resonatorRemainder_neg`); positivity there comes from the collar and the
    pole.
25. **Mean field.** The cross-prime aggregate of wide odd tests is a mean field of size `≍ N`, and
    no polynomial adjunction bound holds (`not_exists_polynomial_adjunction_bound`).
26. **The successor cell `[log k, log(k+1)]`.** Its pole mass is the pronic weight `1/(k(k+1))`
    (`integral_successorCell`); its two Hecke cycles have no prime incidence and meet through the
    collar alone, `≈ ω(log(1 + 1/k)) = (k+1)√(k(k+1))/(2k+1)` per unit mass
    (`successor_localPair_bounds`). Over `𝔽_q[T]` the cell is degenerate.

### 3.8 Rank–trace inertia: what a Gram functional can certify

Without Riemann–Roch effectivity the intersection form still certifies a *proportion* of zeros,
through rank–trace inertia on the real evaluation Gram `Â = P + Q` of hat-unit tests — `P` from the
critical-line zeros, `Q` from the off-line pairs — with `tr Â = N` and `‖Â‖_F² = κN`. Inertia
replaces the Hodge index `p = 0` by `n₊(Q) ≤ p`.

27. **Capacity `2 − κ` and the coalescence blind spot.** At `c = 2` a double critical zero and a
    coalescing off-line pair produce the same rank-one matrix `2vvᵀ`, so no functional of `(Â, N)`
    can tell them apart. For a normalized Gram (`tr Â ≥ N`, `‖Â‖_F² ≤ κN`) the rank–trace laws at
    `c = 2` and `c = 3` certify at once at least `(2 − κ)N` simple critical zeros (plus twice the
    multiplicity excess), at least `((3 − κ)/2)N` distinct zeros, and the exclusion law
    `2a₂ + 5a₃ + 2p ≤ (κ − 1)N` for double zeros `a₂`, zeros of multiplicity `≥ 3` `a₃` and off-line
    pairs `p` (`exclusion_of_normalized_gram`); on one shared diagonal witness these are the exact
    universal limits of every functional of `(Â, N)` (`universal_gram_certification_classification`).
    Over `𝔽_q` `κ = 1` (all zeros simple and critical); on fake curves `κ ≥ 2`. Below the square-root
    threshold `λ ≤ 1` a flat-top prime window has `κ(λ) = 1/λ + λ/3`, capping the certificate at
    `2/3`; the optimal profile `cos(√2 λs)` at `λ = 1` lowers `κ` to at most `3319/2500` and
    certifies more than `1681/2500 > 2/3` simple critical zeros, more than `4181/5000 > 5/6`
    distinct zeros and at most `(819/5000 + ε)N` right zeros (`two_thirds_lt_HD_one`,
    `five_sixths_lt_GD_one`), yet stays below `3/4` (`HD_one_lt_three_quarters`): no profile supported
    below `λ = 1` reaches `3/4`. Beyond `λ = 1`, a flat-top window under a pair-correlation bound
    `F ≤ B` gives `2/3 + 1/(3(3B − 2))`, and a two-window mixture of bandwidths `1` and `4/3` reaches
    `3/4` iff `B ≤ 117/41` (at mixing weight `7/16`) and beats `2/3` for every `B < 181/18`.
28. **Two routes past the blind spot, each with one unproved input.** The pair `(P, Q)` remembers
    what `Â` forgets. Adding the full spectral slack to the rank–trace functional cancels its
    prime-side part identically and leaves `(c²/4) rank P` minus a coupling defect
    (`rank_trace_add_totalSlack_eq`). Unconditionally the zero-side slack is at most
    `(λ − H(λ) + ε)N`, which refutes the slack route for every `λ < 3/4`
    (`not_three_quarters_zeroSideSlack_of_lt_three_quarters`). On `λ ∈ [3/4, 1]` a slack
    `≥ (3/4 − H(λ))N` gives three-quarters of the zeros on the line (`zeta_three_quarters_of_spectralSlack`);
    in the displaced-pair model this needs macroscopic hyperbolic displacement `(1 + 2η)² ≥ 4/3`,
    and non-coalescence alone is not enough (`macroscopic_displacedPair_counterexample_at_four_thirds`).
    The other route is `RHTower.PrimeSurplusFourThirds`, filling the margin `1/18` above the
    diagonal constant `43/36` at bandwidth `4/3` (`zeta_three_quarters_from_prime_surplus`); its
    analytic decomposition is the subject of Trans-Threshold Pair Correlation. The certified
    proportions feed back into the corpus unconditionally: the dyadic off-line moment improves from
    `(67/1000)T` to `(66/1000)T` (`eventually_dyadicWindowTail_le_sixtySix_thousandths`; `57/1000`
    under the prime surplus), and the double-exponential uniqueness threshold for even functions
    vanishing at the simple critical zeros drops from `b > 3` to `b > 5000/1681`
    (`ae_eq_zero_of_doubleExp_simpleCritical_montgomeryTaylor`; `b > 8/3` under the surplus).

### 3.9 The λ-ring of the scaling surface (`TheLambdaRingOfTheScalingSurface`)

29. **Adams operations, Hecke cycles and the pole-plane splitting.** `polarPart` and `prim` are
    orthogonal idempotents splitting any polar surface into the pole plane and the primitive
    complement with pairing `−defect`. The Newton–Witt exponential splits any trace
    `(1 + q^j) + g_prim(j)` into the pole factors times the primitive part (`sigmaSeries_pole_split`);
    over `𝔽_q` this is `zeta = poleZeta · P₁`. Over `ℚ` the normalized Adams operators are exact
    intersection, polar and defect isometries commuting with the splitting (`pair_adamsOp`,
    `defect_adamsOp`). The Hecke correspondences `T_a = √a · adamsOp a` satisfy `T_a H = aH`,
    `T_a V = V`, the Hecke cycles obey `Γ_a(g)·Γ_b(g) = b · L(Δ_g, a/b)` (`pair_heckeCycle`), and the
    arithmetic Lefschetz number splits as `(a + 1)(x·H)(x·V) − √a · defect(adamsOp a x, x)`
    (`arithLefschetz_split`). Frobenius, graphs and Lefschetz numbers exist on the scaling surface;
    Riemann–Roch does not follow from them, and the golden datum obeys the same identities
    (`goldenDatum_lambdaRing_and_not_unitary`).

### 3.10 The odd-sector ledger, the degree floor, and section counts

30. **Lorentz–polar identity.** `2B(F)A(F) = 2 evenPoleMoment(F)² − poleCharge(F)`; on odd tests
    the pole charge `2A(F)²` is the negative self-intersection of the polar projection `A(F)(H − V)`
    (`poleCharge_eq_two_mul_poleA_sq_of_odd`).
31. **Exact ledgers on the odd degree-`r` subsurface.** For every `r > 0` and plateau radius
    `R > r`, the defect of a cycle with odd test `f` supported in `[−r, r]` is a sum of nonnegative
    plateau-gauge terms plus a bounded remainder, minus the reflected-prime/polar cost
    (`scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger`). In that cost the `e^r` main
    terms of the prime comb and the pole charge cancel, leaving the two-pole Chebyshev remainder
    `E(s) = e^s + s − 1 − ψ(e^s)` on `(0, 2r]` against the lag correlations of `f`
    (`scalingSubsurface_odd_defect_eq_chebyshevDefectLedger`). These are identities: the explicit
    formula rewritten on the odd subsurface.
32. **The degree floor measures the zero width.** Unconditionally
    `δ(x, x) ≥ −75e^r∫f²` and `δ(x, x) ≥ −((3 + ε)e^r + C)∫f²` at every degree
    (`scalingSubsurface_odd_defect_ge_neg_seventy_five_mul_exp`,
    `exists_scalingSubsurface_odd_defect_ge_neg_three_add_eps_mul_exp`, lowered from `78` and `8 + ε`
    by bipartite high-lag halving and the Cauchy–Schwarz pole-charge bound), and in Sobolev norms
    both the first-order (`∫f² + ½∫(f')²`) and second-order pole-tilted (`¼∫f² + ∫(f')²`)
    de la Vallée Poussin lower bounds `−K e^r e^{−c√r}` hold across all degrees
    (`exists_scalingSubsurface_odd_defect_ge_neg_deLaValleePoussin_sobolev`,
    `exists_scalingSubsurface_odd_defect_ge_neg_poleTilted_deLaValleePoussin_sobolev`). A floor `−Ce^{2σr}∫f²` at
    all degrees forces `|Re ρ − ½| ≤ σ` for every zero, so RH is equivalent to a subexponential floor
    and to a bounded floor (`rightZeros_zeta_eq_empty_iff_subexponential_scalingSubsurface_odd_defect_floor`,
    `rightZeros_zeta_eq_empty_iff_bddBelow_scalingSubsurface_odd_defect`). Normalized by the Sobolev
    energy `∫f² + ∫(f′)²`, which absorbs the Riemann–von Mangoldt `log T`, the converse holds
    unconditionally at every width with no clustering hypothesis: `zetaZeroWidth ≤ σ` iff the defect
    is at least `−Ce^{2βr}(∫f² + ∫(f′)²)` for every `β > σ`, and the infimum of admissible floor
    rates is the zero width (`zetaZeroWidth_le_iff_scalingSubsurface_odd_sobolev_defect_floor`,
    `oddDefectFloorRate_eq_zetaZeroWidth`). The unconditional floor has rate `½`; any power saving
    would be a zero-free strip. Through degree `181/500` the odd floor is `0`.
33. **Hecke-stable ampleness, section counts, and selectivity**
    (`SectionCountRiemannRochAndPrimeBlindSelectivity`). Hecke correspondences act on the pole plane
    with weights `(a, 1)`, so a cycle keeps nonnegative ample degree under all `T_a` iff it lies in the
    double-null nef quadrant `{x·H ≥ 0, x·V ≥ 0}`; on every polar surface Hodge index holds iff the
    open positive cone lies in that quadrant, and over `ℚ` a single scale decides: RH iff `T_2` maps
    the open positive cone into the ample half-space
    (`scalingSurface_hodgeIndex_iff_heckeCorrespondence_openPositiveCone_ample`). On the section-count
    side, the two-pole degrees of freedom of the logarithmic box `[0, s]`, `∫_0^s(e^u + 1)du`, minus
    the prime-power node count `ψ(e^s)`, is exactly `E(s)`
    (`polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect`), and the shifted pair inflates the
    node count (`generalizedTwoPoleDefect_shiftedPair_lt`). A prime-blind test (autocorrelation zero
    at every relevant `log n`) pays only its pole charge, and a prime-blind subspace with vanishing
    even pole moment and spectral second moment `≤ (69/2)∫f²` is zero
    (`finrank_primeBlind_subspace_eq_zero`). Rank counts alone do not select: multiplying a Dirichlet
    sampling operator by a nowhere-vanishing diagonal weight — the shifted pair's `(n^a + n^{−a})/2`
    against `Λ` — leaves its kernel and `h⁰` unchanged
    (`h0_weightedDirichletSampling_shiftedPair_eq_vonMangoldt`). A section count is selective only
    when coupled to a norm such as `Σ w(n)²` or to `E(s)`.

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
  uniqueness of exponential sums replaces the choice of tests. On one prime tower the moments
  `Σ_τ q_τ β_τ^k` separate eigenvalue classes, by annihilating polynomials and Cesàro means.
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
| A source-defined cone escapes the estimate | The `L²` source cone is defined without the form and is ample non-vacuously, but its Riemann–Roch axiom is exactly the coercive floor `c∫f² ≤ W(f, f)`. Defining the cone well moves the problem into the floor; it does not remove it. |
| A subexponential defect floor is a reduction of RH | It is equivalent to RH (§3.10): the floor rate is the zero width. A power saving in the floor is a zero-free strip, as hard as quasi-RH. |
| The odd-sector ledger is a positivity mechanism | It is the explicit formula rewritten; the sign is still carried by `E(s) = e^s + s − 1 − ψ(e^s)`. |
| The cyclic law is a positivity statement | It localizes the defect on one Hecke orbit; it does not bound it. |
| One prime always sees everything | Resonant primes, where two right zeros share `p^{ρ − ½}`, can hide classes; with finitely many right zeros there are only finitely many of them, with infinitely many the eigenvalues may accumulate. |
| Multiplicities count | The defect counts distinct right zeros; depth and multiplicity are invisible. |
| A finite degree certifies positivity | No degree works for all configurations over `ℚ`; over `𝔽_q` the window `2g` does. |
| The comb aggregate is an intersection number | On resonators the prime intersection has no cross-prime terms; the aggregate is a mean-field shadow. |
| The pronic weight is the successor intersection | It is the pole mass of the cell; the intersection is the collar `ω(log(1 + 1/k)) ≍ k/2`. |
| The three-quarters modules prove that 75% of the zeros are on the line | They prove `(3/4)N` *conditionally*: on a zero-side slack `S(T) ≥ N/12`, or on `PrimeSurplusFourThirds`. The unconditional content is `(2/3 − ε)N + S(T) ≤ N₀*` with the slack retained, the `43/36` diagonal constant and the `O(T^{5/6}log²T)` cross term. |
| Adams operations make the scaling surface a Weil surface | They give Frobenius, graphs and Lefschetz numbers; the golden datum has them too. Riemann–Roch is still missing. |
| The rank–trace form is capped at `2/3` | The form has capacity `2 − κ` (reaching `1` at `κ = 1`); `2/3` is `2 − κ(1)` from stopping pair correlation at `λ = 1`. |
| A rank-based section count is selective | Diagonal reweighting leaves kernels and `h⁰` unchanged; the shifted pair and `Λ` have the same counts. Selectivity needs a norm or the defect `E(s)`. |

---

## 6. Questions the programme answers and the tools it builds

### 6.1 Questions

1. **Which ingredients of Weil's proof exist for `ℤ`?** The pairing, the fibres, Lefschetz,
   adjunction, Bézout positivity, Adams operations and Hecke graphs: all exact. Riemann–Roch: absent,
   and its existence with ample degrees is RH.
2. **What does the failure of the Hodge index measure?** The number of distinct zeros right of the
   line — never depth or multiplicity — filtered by degree, split additively into reflection
   sectors at every degree, and carried by the Hecke orbit of any one spectrally generic test, and
   for all but finitely many primes by one prime tower when the right zeros are finite in number
   (§3.4). The growth rate of the Sobolev-normalized defect floor in the degree is the zero width,
   unconditionally (item 32).
3. **Which arithmetic data force the sign?** Not span data, integrality, functional equation or
   positive Euler data: the golden datum has all of them and fails (`WhichArithmeticDataForceTheSign`).
   Positivity of point counts only tests `trace k ≤ q^{k/2} + q^{−k/2}`, because the polar pairing
   `q^j + q^k` swamps the `H¹` trace throughout the critical strip. The Toeplitz defect splits
   universally as a sum of squares minus a Rosati reflection defect,
   `toeplitz = Σ_i ‖P_e(β_i)‖² − ½Σ_i‖P_e(β_i) − P_e(1/β̄_i)‖²`
   (`toeplitz_eq_frobSquareMass_sub_frobReflectionDefect`). Over `𝔽_q` the data that force the sign
   are equivalent to each other (`forcing_arithmetic_data_tfae`): pointwise Rosati invariance of the
   eigenvalues; pole-subtracted Hasse–Weil bounds `|N_k − (q^k + 1)| = O(q^{k/2})`; forward
   light-cone Bézout positivity, or ambient Bézout plus Riemann–Roch. Over `ℤ` the counterparts are
   coupled odd-cone Bézout and all-aperture payment of the pole-cancelled Chebyshev remainder `E(s)`.
4. **What can a Gram functional certify without effectivity?** A proportion: `(2 − κ)N` simple
   critical zeros and the exclusion laws of item 27, exactly and no more for any functional of
   `(Â, N)`; more than `2/3` below pair correlation, never `3/4` there; `3/4` on one of two
   unproved inputs (item 28).
5. **What would an effectivity for `ℤ` have to be?** A cone defined without the sign of the form,
   with Riemann–Roch supply and ample degrees proved from that definition, reducing over `𝔽_q` to
   Weil's. Cones read off the form are tautological; the source cones are not, and their
   Riemann–Roch is a coercive floor (item 20).

### 6.2 Tools

Built and reusable:

- *Polar surfaces*: defect, primitive projection, four forms of the Hodge index, realizability.
- *The `𝔽_q` calibration*: curve data, span Toeplitz forms, the Pontryagin law, fake curves, Witt and
  Beurling structure, the period quotient.
- *The scaling surface* with its signature law and the Pontryagin law over tempered configurations,
  reflection sectors and the degree filtration.
- *Visibility calculus* of right zeros from on-line mass, local and logarithmic density.
- *The Kronecker-rank dichotomy* and exponential-polynomial recurrence.
- *Cyclic density and prime towers*: spectrally generic tests, density of one Hecke orbit on the zero
  side, Frobenius eigenvalues and weights, resonant primes.
- *Bézout positivity* through the Lévy jump form of the collar.
- *Source section cones*: determinantal effectivity defined from source data, Hecke-stable and ample.
- *Hecke incidence*: the Cartesian law, resonators, the successor cell.
- *Rank–trace inertia* with spectral slack.
- *The `λ`-ring*: Adams operations, Hecke correspondences and cycles, arithmetic Lefschetz numbers.
- *The odd-sector ledger*: Lorentz–polar identity, reflected-prime/polar and Chebyshev ledgers,
  degree floors and the zero width.

To be built:

- a notion of section on the scaling surface with Riemann–Roch supply and an ampleness proof that does
  not use the sign of the form, whose Riemann–Roch axiom is *not* equivalent to the floor it should
  prove;
- an effectivity stable under the Hecke correspondences that the golden datum violates;
- the near-radical count of Landau–Widom type;
- a bound on the coupling of prime towers through the collar on rank-`P` boxes.

---

## 7. Open problems

1. **Riemann–Roch for `ℤ` — the open core.** A notion of section on the scaling surface whose
   effective classes have nonnegative ample degree by definition and which supplies effective
   cycles in every class of positive square. Bézout is available (21); the supply is RH-equivalent
   (18) and cannot come from positive tests (19), from cones read off the form (20), or from exact
   annihilators among compact tests (22); source-defined cones exist but their supply is a
   coercive floor (20). Of the routes to Wall 14 this is the only one whose removal criterion is a
   construction, not an estimate. The constraints on a construction are known: the cone must
   contain the open positive cone, be Bézout-closed and Hecke-stable, and use a constraint the
   golden datum violates, which means the additive structure of `ℤ`. One candidate is a count. Take
   for `h⁰` the dimension of aperture-`A`, height-`T` tests vanishing on the prime-power nodes of the
   box, and seek `h⁰ ≥ (degrees of freedom) − (node count)` with the error identified as the
   Chebyshev defect `E(s)` — the identity `DoF − node count = E(s)` of item 33 is its exact skeleton.
   The corpus already proves Landau-density statements of this kind (prime-blind tests have large
   spectral second moment). The classical shadow of such a count is the `T + N` term of the mean
   value theorem, with diagonal at the square-root threshold. A section count no stronger than the
   large sieve at the diagonal would only relabel Dirichlet polynomials (item 33); a useful one must
   be selective against the golden datum and the shifted pair.
2. **Near-radical count (Landau–Widom).** The two-sided law for `h⁰_ε(L)`, the dimension of
   aperture-`L` tests with `|W| ≤ ε‖f‖²`, unconditionally in its upper half, and the rate
   `−log μ(L) ≍ 2π² N(T*)/log N(T*)` for configurations on the line. Known: lower bounds
   (`zeta_weil_near_radical_dimension_smooth`, `RHTower.zeta_weil_near_radical_sharp_count`).
3. **Aperture over `ℚ`.** The degree at which `n` right zeros become visible is explicit in terms
   of on-line mass, local density and logarithmic density, and height-uniform under a uniform
   window count (item 15); no degree works uniformly over all configurations. Open for `ζ`:
   eliminating the residual `log γ₀` factor in the Riemann–von Mangoldt tail of the Turán inequality
   without a bounded on-line density.
4. **The collar between towers.** On rank-`P` boxes the towers couple through the collar and the
   pole only; bound this coupling against `Σ_p E_p` and decide positivity of the
   finite-Euler-product form on lattice tests.
5. **Effectivity from the `λ`-ring.** The Adams operations, Hecke correspondences and the pole-plane
   splitting exist (§3.9), and the source cones are stable under them (item 20). Open: a
   Hecke-stable cone with nonnegative ample degree and Riemann–Roch supply whose supply is proved
   from the `λ`-ring structure rather than from a coercive floor. Whether the Lefschetz identity
   constrains the defect beyond the signature law is answered by the cyclic law: the defect is
   generated by the Hecke orbit of any spectrally generic cycle (item 17).
6. **Beyond `2/3` and `HD(1)`.** The flat-top cap `2/3` and the variational sub-threshold profile
   are explained, and no sub-threshold profile reaches `3/4` (§3.8). Open: either input that gives
   `3/4` — a zero-side spectral slack `S(T) ≥ N(T, 2T)/12` near `λ = 1` (requiring macroscopic
   hyperbolic pair displacement), or trans-threshold pair correlation beyond `λ = 1`
   (`RHTower.PrimeSurplusFourThirds` at bandwidth `4/3`, or `F ≤ B` with `B ≤ 117/41` through the
   two-window mixture).
7. **One prime against two.** Two primes carry the whole defect; one prime carries every visible
   outer eigenvalue `p^{ρ − ½}` whenever the real parts of the right zeros contain no strictly
   increasing sequence, however the eigenvalues accumulate, and every visible class on an attained
   top (item 17). Open: real parts increasing to their supremum. There the closure argument cannot
   work: the difference of two positive Wolff measures of equal mass on disjoint annuli
   (`HTGeometry.PositiveWolffMeasure.exists_positive_wolff_annulus`, atoms accumulating at the outer
   radius) kills every Laurent moment, so negative vectors can leave the closed span of the tower.
   Whether the tower's negative index nevertheless counts the visible classes is the question.

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
| `FrobeniusSpanCalibration`, `FrobeniusSpanHodgeIndexIsRH` | curve data, Lefschetz and adjunction, span defect = Toeplitz form, Hodge index on the span ⟺ unitarity |
| `FakeCurvesAndTheWindowLaw`, `WittIntegralityIsNotPurity`, `TheGoldenCurveIsABeurlingSystem` | the golden datum; window visibility and hiding; integrality versus purity; the golden curve as a Beurling system |
| `SpanContactLaw`, `TheFrobeniusSpanDefectCountsTheOuterEigenvalues` | contact window; Pontryagin law over `𝔽_q` |
| `TheScalingSurfaceOfACurve`, `TheFrobeniusSpanIsTheTowerOfTheScalingSurface`, `TheDegreeFiltrationOfACurveIsItsWindowFiltration`, `TheFirstNegativeLagOfACurve` | the scaling surface of a curve; three Hodge index theorems; the span as period quotient; degree filtration = window filtration; lag tests read point counts, purity = lag positivity, Turán-located first negative lag |
| `HodgeIndexFromEffectivity`, `BezoutEffectivityAndTheBeurlingObstruction`, `DistinctEffectiveCyclesMeetNonnegatively` | effectivity axioms ⟺ Hodge index; Bézout positivity through the collar |
| `TheScalingSurface`, `ArithmeticHodgeIndexSignatureLaw`, `InfiniteGenusLaw` | the scaling surface of `ℤ`; signature law and selection of `Λ`; no exact annihilators |
| `FiniteConfigurationPontryaginLaw`, `TemperedConfigurationPontryaginLaw`, `TheHodgeDefectCountsTheRightZeros` | the Pontryagin law, finite, tempered and general |
| `TheReflectionSectorsOfTheHodgeDefect`, `TheDegreeFiltrationOfTheHodgeDefect`, `SchurLendingOddHodgeIndexPastFirstPrime`, `WhatTheFailureOfTheHodgeIndexMeasures` | sectors and degrees; `ζ` below `3/10` and the odd sector through `181/500`; multiplicity and depth invariance; Sobolev floor rate = width |
| `TheVisibilityDegreeOfAnIsolatedPair`, `TheVisibilityDegreeOfRightZeros`, `HeightUniformVisibilityAndOffLineDensity` | visibility degrees from on-line mass and densities; height-uniform visibility; the clustering alternative |
| `TheKroneckerRankDichotomy`, `TheZerosOfAnExponentialPolynomialRecur` | recurrent configurations have defect `0` or `∞` |
| `TheHodgeDefectIsCyclic`, `TheHeckeTowerOfAPrimeIsThePeriodQuotient`, `AlmostEveryPrimeSeesEveryRightZero`, `TheTowerDefectCountsTheFrobeniusEigenvalues`, `OnePrimeSeesEveryWellFoundedLevel` | cyclic Pontryagin law; prime towers, Frobenius eigenvalues and weights; resonant primes; top-down class extraction, the tower law without finiteness, attained tops |
| `ResonatorKroneckerLaw`, `HeckeIncidenceCartesianLaw`, `TheResonatorRemainderIsNegative`, `TheAdjunctionConjectureMeanField` | Hecke incidence: Cartesian law, resonators, mean field |
| `ThePronicWeightIsThePoleMassOfTheSuccessorCell`, `TheSuccessorCollar` | the successor cell |
| `TheTwoThirdsConstantIsPairCorrelation`, `BreakingTheCoalescenceBlindSpotAndThreeQuarters`, `SpectralSlackConservationAndTheHyperbolicDisplacementThreshold`, `WhatAGramFunctionalCertifiesWithoutEffectivity` | rank–trace inertia, the coalescence blind spot, spectral slack, routes to `3/4`, corpus upgrades |
| `TheLambdaRingOfTheScalingSurface` | `λ`-ring, Adams operations, Hecke cycles, Lefschetz splitting |
| `RiemannRochForZAndTheReflectedPrimePolarLedger` | tautological cones, Lorentz–polar identity, odd-sector ledgers, `75e^r` and `(3 + ε)e^r` floors, first- and second-order de la Vallée Poussin Sobolev floors, shared derivative payment bootstrap, degree floor ⟺ zero width |
| `WhichArithmeticDataForceTheSign` | Toeplitz–Rosati reflection identity, pole masking of point counts, forcing equivalences over `𝔽_q` and on the scaling surface |
| `SectionCountRiemannRochAndPrimeBlindSelectivity` | nef quadrant and Hecke-stable ampleness, `DoF − node count = E(s)`, prime-blind section vanishing, diagonal relabeling invariance |
| `SourceDeterminantalSectionsAndArithmeticRiemannRoch` | source section cones, non-vacuous ampleness, Hecke stability, Riemann–Roch ⟺ coercive floor, Riemann–Roch past the first prime, all-aperture Chebyshev and de la Vallée Poussin floors |
| `AllApertureSourceRiemannRochAndCoercivityLaws` | universal strict-ampleness rigidity, compensated polar surfaces and all-aperture ample source cones, no-Hardy-weight law, doubly-exponential Gaussian ceiling, closed-aperture polar ground-energy equivalence and strict-monotonicity self-upgrade, Sobolev source cones and zero-width equivalence |
