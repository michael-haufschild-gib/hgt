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

**The open core.** Disjoint nonnegative tests have nonnegative local intersection
(`localPair_nonneg`). This does not establish `BezoutAxiom`, which includes self-intersections,
for a cone carrying Riemann–Roch. Graded source cones already have unconditional all-aperture
RR; what remains is an independent source construction carrying RR together with the full
Bézout or ample axiom. Existence of such a cone is equivalent to RH
(`exists_bezout_effectivity_iff_hodgeIndex`, `riemannHypothesis_iff_exists_effectivity`). This
existential criterion does not assert Bézout for every selected RR cone. The failure of the
Hodge index is measured exactly: its defect
is the number of distinct zeros right of the critical line (`zeta_hodgeDefect_iff`), and the whole
defect already lives on the Hecke orbit of a single test (`cyclic_pontryagin_law`), as over `𝔽_q`
it lives on the Frobenius orbit of the diagonal.

**Source-boundary rigidity.** For a nonnegative even reserve `Φ` invariant under fibre
translations, source-cone Bézout is exactly the mixed bound
`defect(x,y)² ≤ Φ(x)Φ(y)`. RR and Bézout together force `Φ(x)=defect(x,x)`; the strict cone
has the same requirement. Graded Bézout itself forces `Φ≥0`, so signed reserves cannot evade
this equality (`SourceConeBoundaryRigidity`, `GradedSourceConeBoundaryRigidity`). A coercive
lower floor supplies RR but does not supply Bézout. At every positive aperture the Weil
Rayleigh quotient is unbounded above in the kernel of every finite-dimensional linear reading.
Hence every finite scalar L² reserve, and every reserve obtained by arbitrary postprocessing
of finitely many linear source readings, fails Bézout on the full aperture source space
(`WeilEnergyIsUnboundedAtEveryAperture`).

The classification also allows signed, asymmetric reserves: closed and strict cones depend
only on `max(Φ,0)`, and RR plus Bézout forces that positive part to equal the diagonal defect.
Their asymmetric Bézout condition is `max(defect(x,y),0)² ≤ max(Φ(x),0)max(Φ(y),0)`
(`SourceRiemannRochWithoutSymmetry`). Ampleness has its own exact condition: every source
with `Φ≤0` must lie in the mixed-defect radical (`SourceConePrimitiveFaithfulness`). On the
full compact scaling surface that radical is precisely the fibre plane, while the full
intersection pairing is nondegenerate. Thus compact numerical equivalence is equality
(`NumericalEquivalenceOnTheScalingSurface`); genuine nonzero principal representatives need
a larger source carrier.

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
| [Arithmetic Orientation Geometry](../ArithmeticOrientationGeometry/README.md) and [Arithmetic Local Divisor Geometry](../ArithmeticLocalDivisorGeometry/README.md) | Refine the geometric target into exact reflection transport and source-defined local divisor tests; finite jets and local sections still need analytic recovery. |
| [Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md) | The analytic engine of the second route to `3/4` in §3.8: it decomposes `RHTower.PrimeSurplusFourThirds` into a Dirichlet mean value and a close-pair kernel. |

`RHTower` supplies the explicit formula, the Weil criterion, the Lévy–Khintchine form of the
archimedean symbol and the matrix inertia calculus.

On the RH frontier ACS is a live route: source-defined sections, all-aperture Riemann–Roch with
ampleness, the scaling Hodge index, RH. Its proved part is the receiver (item 18), the
low-frequency-blind subsurfaces with Riemann–Roch and ampleness (item 20), the local floors and the
finite-model classifications (items 23–24); its open estimate is source Riemann–Roch on a
Hecke-stable cone of nonnegative degree at every aperture (§7.1). Trans-Threshold Pair Correlation
supplies the analytic engine of its route to `3/4`, and Arithmetic Orientation Theory takes the
scaling surface as its geometric core.

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
    For `ζ` the defect is finite at every degree, unconditionally:
    `hodgeDefectAt ζ a ≤ 1 + 4aT(a)/π` with `T(a) = 4(e^{2E} − 1)`, `E = 10 + 68e^a`
    (`hodgeDefectAt_zeta_le_shannon`, sharpening `1 + 2T(a)(2a + 2)/π` of `hodgeDefectAt_zeta_le` via
    `δ`-transition cut-off characters and `δ → 0⁺`, `hodgeDefectAt_zeta_lt_top`). Below the pole the form is the symbol
    integral `∫|h_F|²(μ + P_X)`; the archimedean symbol grows like `log|τ|` and the Euler product
    bounds the prime symbol by `68√X`, so a Weil-negative test carries more than half its spectral
    mass below the horizon `T(a)`, and Bessel's inequality against the cut-off characters bounds
    the dimension of such tests by `4aT(a)/π` (`finrank_mul_le_four_mul_of_band_concentrated`,
    `negIndex_zeroGram_zeta_le_shannon`). Lag
    lattices and curves have no archimedean place: their defect is `0` or `∞` at every degree. So
    at each degree only finitely many right zeros of `ζ` are visible, and the degree at which `n`
    of them become visible grows at least like `log log n`. The failure is confined to explicit low
    frequencies: Weil's form is nonnegative on every aperture-`a` test whose transform vanishes at
    the pole and on the grid `{j h(a) : |j| ≤ J(a)}` in `[−T(a), T(a)]`
    (`re_W_zeta_nonneg_of_lowGrid`; the cut-off characters are Lipschitz in `L²`, so a transform
    vanishing on a fine grid has small low-frequency mass). Over `𝔽_q` no finite set of frequencies
    does this: beyond `log 5/2` every finite set is avoided by a negative test of the golden curve
    (`goldenDatum_no_finite_divisor`, `exists_neg_of_hodgeDefectAt_eq_top`). With a margin
    `Re W ≤ −ε‖f‖²` the negative spaces are carried by the off-line pairs below a height
    `exp(O(e^a + log(1/ε)))` (`RHTower.zeta_weil_negative_index_le`).
15. **Visibility and hiding.** Over `𝔽_q` the window `n_0 + 2n_+ ≤ 2g` sees all `n_+` outer
    eigenvalues. Over `ℚ` an isolated pair `½ ± δ + iγ₀` in an on-line lattice of density `L` is seen
    exactly from the degree where `sinh(2δa)/δ = 2L + 2a` (`hodgeDefectAt_isolatedPair`); for `n`
    pairs, any subset whose complement has total pair energy at most `L` bounds the defect by its
    size (`exists_n_hidden_at_degree`); conversely all right zeros are visible once the on-line mass
    near them is below an explicit `cosh` threshold (`hodgeDefectAt_eq_of_onLineMass`), with explicit
    masses under lattice, unit-window and logarithmic densities. Under a uniform unit-window count
    `N(t, t + 1] ≤ D` the visibility degree no longer depends on the heights
    (`card_le_hodgeDefectAt_of_uniform_window_count`). For `ζ`, the local off-line bound
    `OffLineCopiesLocallyBounded M` of Square-Root Threshold (which bounds only off-line zeros in
    unit windows and places no bound on on-line density) makes the near-top visibility constants
    height-uniform, eliminates the `log γ₀` factor in the Riemann–von Mangoldt cubic potential tail
    of the Turán inequality (`zeta_powCluster_le_of_offLineCopiesLocallyBounded`,
    `zeta_full_cluster_collapse_of_offLineCopiesLocallyBounded`,
    `zeta_partial_elimination_le_of_offLineCopiesLocallyBounded`: at the shifted evaluation point
    `s = σ + i Im z₁` with `σ = Re z₁ − κ/V > 0`, every on-line zero has `e^{(Re z − σ)V} = e^{−σV} ≤ 1`
    and contributes `0` to the amplified `‖D(z₁)‖ e^κ` cubic potential tail, which runs exclusively
    over off-line right zeros and is bounded by `24 M / r³`), completely removes `recordHeightOf` and
    `oneParamRecordHeight` from the one-parameter (`c = 0`) visibility and contact-aperture laws
    (`one_param_record_visible_at_explicit_lag_of_offLineCopiesLocallyBounded`,
    `one_param_near_top_visible_at_explicit_lag_of_offLineCopiesLocallyBounded`,
    `sqrt_mul_recordScaleOffLine_inv_eq`,
    `zetaContactAperture_le_of_near_top_zero_of_offLineCopiesLocallyBounded`), isolates the on-line
    mass `onLineEvenMass w γ₀` (where on-line coefficients are nonnegative real numbers and never
    cancel, `evenCoeff_modScaledBump_onLine_eq_norm`,
    `two_re_lagStructure_zero_eq_onLineEvenMass_add_offLine`) as the sole height-dependent datum in
    modulated visibility (`zeta_near_top_visible_at_explicit_onLineMass_lag`), reduces the modulated
    visibility lag from `O_w((log γ₀)² log log γ₀ / δ₀)` to the doubly-logarithmic scale
    `nearTopLogLogLagOffLine M w γ₀ δ₀ = O_{w, M}((1 + log log γ₀) / δ₀)`
    (`zeta_near_top_visible_at_loglog_lag_of_offLineCopiesLocallyBounded`), and gives the
    unconditional dichotomy: either every near-top zero is visible at the doubly-logarithmic lag and
    the degree-defect floor rate equals the zero width, or off-line zeros cluster without bound
    (`near_top_visible_at_loglog_lag_or_offLine_cluster`,
    `scalingSurface_defectRate_eq_zetaZeroWidth_or_offLine_cluster`). Moreover
    (`DoublyLogarithmicVisibilityAndExcludedDepthLaw`), under `OffLineCopiesLocallyBounded M` the
    Riemann–von Mangoldt bounded-window lower bound `exists_xiZeroCount_window_ge_log` forces at
    least `log c − (2⌈h⌉₊ + 1)M` on-line zero copies in `(c − h, c + h]`, so `onLineEvenMass w c` and
    `2 Re S(0)` obey the unconditional two-sided logarithmic law `c_w log c ≤ onLineEvenMass w c ≤ C_w (C_ξ + log(|c| + 4))`
    (`exists_onLineEvenMass_two_sided_log_of_offLineCopiesLocallyBounded`); the off-line visibility
    lags obey two-sided bounds (`recordLagOffLine_two_sided`, `nearTopLagOffLine_two_sided`,
    `nearTopLogLogLagOffLine_two_sided`) with `nearTopLogLogLagOffLine M w γ₀ δ₀ = Θ_{M,w}((1 + log log(|γ₀| + 4))/δ₀)`;
    the doubly-logarithmic aperture is intrinsic both for `θ`-decoherent difference tests
    (`re_W_twoBump_modScaledBump_nonneg_of_lag_le_log_ratio`) and across all `C²_c([−a, a])` tests on
    `isolatedPairConfig` at the Riemann–von Mangoldt density `L = (1/2π)log(γ₀/2π)`
    (`hodgeDefectAt_isolatedPair_rvmDensity_eq_zero`, `hodgeDefectAt_isolatedPair_rvmDensity_eq_one`);
    and exact affine inversion in `1/δ₀` gives the doubly-logarithmic contact-aperture and
    excluded-depth laws `zetaContactAperture ≤ V/2 + w` and
    `z₀.re < nearTopLogLogExcludedDepthOffLine M w z₀.im V = O_{M,w}((1 + log log(|z₀.im| + 4))/(V − Drift))`
    (`zetaContactAperture_le_of_near_top_loglog_of_offLineCopiesLocallyBounded`,
    `re_lt_nearTopLogLogExcludedDepthOffLine_of_pos_on_Icc`,
    `re_lt_nearTopLogLogExcludedDepthOffLine_of_lt_contactAperture`). Over `𝔽_q` the window `2g`
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
    * *Laurent-moment Toeplitz rigidity, single-prime Wolff blindness at non-attained tops, and the
      well-founded visible locus (`OnePrimeAgainstTwoAndWolffTowerObstruction`):* On any finite
      window `K ⊂ ℤ`, `towerGram Z g ℓ K j k = towerMoment Z g ℓ (j − k)` where
      `towerMoment Z g ℓ m = Σ'_τ zeroCoord Z g τ · conj(zeroCoord Z g (reflectCarrier Z τ)) · (frobEig ℓ τ)^m`
      (`towerGram_apply_eq_towerMoment`), so `towerGram` and its `hermNegIndex` depend on `(Z, g)`
      exclusively through the two-sided Laurent moments (`towerGram_eq_of_towerMoment_eq`). Without
      `(· > ·)`-well-foundedness, the difference of normalized positive Wolff measures on disjoint
      annuli `0 < r₁ < R₁ ≤ r₂ < R₂` (`exists_normalized_positive_wolff_annulus`) has vanishing
      Laurent moments for *all* `m ∈ ℤ` while every class sum is nonzero
      (`exists_counterexample_to_laurent_class_extraction_without_wellFounded`), and on every strip
      `1/2 < Re ρ < 1/2 + Θ` the symmetric Wolff configuration has locally finite ordinates,
      infinitely many outer Frobenius eigenvalues, strictly increasing real parts failing
      `(· > ·)`-well-foundedness, and vanishing off-diagonal symmetric Laurent moments (`M(m) = 0`
      for `m ≠ 0`, `M(0) = 4 Σ'_i c_i > 0`), so on *every* finite window `K` its Toeplitz matrix is
      `(4 Σ'_i c_i) • 1` with `hermNegIndex = 0` and adding it to any nonnegative Toeplitz matrix
      `H₀` preserves `hermNegIndex (H₀ + T_K) = 0`
      (`exists_symmetric_wolff_toeplitz_blind_configuration`). Conversely, in any `ZeroConfig Z`
      every bounded-ordinate slice `{τ ∈ rightZeros Z | |Im τ| ≤ T}` is finite and its upper levels
      are `(· > ·)`-well-founded (`finite_rightZeros_of_abs_im_le`,
      `upperLevels_wellFounded_of_bounded_im`, `not_wellFounded_upperLevels_imp_unbounded_im`), the
      well-founded visible locus `wfVisibleSet Z g ℓ` unconditionally lower-bounds
      `sup_K hermNegIndex (towerGram Z g ℓ K)` (`wfVisibleSet_sandwich_and_infinite_law`,
      `visibleFrobSet_above_subset_wfVisibleSet_of_finite`), and two distinct primes `p ≠ q`
      eliminate both resonant-prime collisions and Wolff annulus cancellation to recover the full
      defect `(rightZeros Z).encard` (`one_prime_vs_two_primes_complete_law`).

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
      at all apertures:* Uncompensated positive `l2SourceCone` Riemann–Roch holds with `c = 1/1000` on
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
      `SurfaceRiemannRochAxiom 0 0`, and `HodgeIndex` unconditionally at all
      apertures `r > 0` (`l2CompensatedScalingSubsurface_realTestsAt_all_apertures`,
      `compensatedSurface_hodgeIndex_iff`).
    * *Riemann–Roch for `ℤ` away from the low-frequency divisor, uncompensated, at every degree:*
      on the subsurface of real aperture-`a` tests whose transforms vanish at the pole `i/2` and on
      the grid `D_a` of item 14 (`lowBlindTests`), Weil's form is coercive with
      `c_a = E(a)(1 − 1/π)`, `E(a) = 10 + 68e^a` (`re_W_zeta_ge_of_lowGrid`: the band inequality
      `Re W ≥ E‖f‖² − (E/π)∫_{−T}^{T}|h_f|²` plus the grid bound), so `l2SourceCone c_a` satisfies
      `RiemannRochAxiom` and `AmpleAxiom`, the subsurface has the Hodge index, and it is not trivial
      (`lowBlindTests_effectivity`, `exists_ne_zero_mem_lowBlindTests`). The coercivity constant
      grows like `e^a`; the Gaussian ceiling on all tests comes from the finitely many directions
      read by `D_a` and the pole.
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
      simultaneous `RiemannRochAxiom` + non-vacuous `AmpleAxiom` + `SurfaceRiemannRochAxiom 0 0`
      for `l2SourceCone (μ₀(r)) (polarFreeSmoothRealTestsAt r)` at every aperture
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

### 3.6 Infinite genus and the Landau–Widom near-radical law (`InfiniteGenusLaw`, `LandauWidomNearRadicalLaw`)

22. No nonzero compact test has a transform vanishing at all but finitely many simple critical
    zeros (`eq_zero_of_paperFT_vanish`); RH iff Weil's form is positive definite
    (`riemannHypothesis_iff_weil_positive_definite`). The finite-field radical has no exact
    counterpart among compact tests; near-radicals remain. Over `𝔽_q` the counterpart exists and
    its aperture is the genus: on the scaling surface of a curve with `d` distinct eigenvalues the
    Frobenius polynomial acting on the `q`-tower, `P(T_q) g`, has transform `P(e^{iz log q}) ĝ(z)`
    and lies in the radical (Cayley–Hamilton, `W_frobPolyTest_left`), and a nonzero compact test
    of aperture `a` with transform vanishing at every zero exists iff `a > d log q/2`
    (`exists_radical_test_iff`; Poisson along each eigenvalue's period and a Vandermonde count of
    the samples). Finite genus is a finite radical aperture; `ℚ` has radical aperture `∞`. The
    radical is exactly the Frobenius ideal: a compact test is numerically trivial iff it is
    `P(T_q) g` (`radical_iff_eq_frobPolyTest`, by division one factor `T_q − b` at a time with a
    smooth cutoff), the scaling-surface form of Weil's relation `P(F) ≡ 0` on the Frobenius span.
    Beyond the genus aperture the radical of a curve has every finite dimension (translates of one
    radical test, `curve_radical_finrank_ge`); over `ℚ` even the near radical is finite: every space
    of pole-free aperture-`a` tests with `Re W ≤ ε‖f‖²` has dimension at most `4a T_ε(a)/π = 2·Shannon(a, T_ε(a))`
    with `T_ε(a) = 4(e^{2E + 4πε} − 1)` (`zeta_near_radical_finrank_le_shannon`, removing the
    `T_ε(a)^{3/2}(a + 1)^{3/2}` Lipschitz-grid overhead of `zeta_near_radical_finrank_le`).
    * *Two-sided Landau–Widom near-radical count `(2 ∓ η)e^{2L}` and rate `2π² N(T*)/log N(T*)`
      (`LandauWidomNearRadicalLaw`):* Dyadic summation of the Riemann–von Mangoldt formula yields
      the unconditional two-sided cumulative zero count `|N(0, T) − (T/2π)log(T/2πe)| ≤ C log²T`
      (`zeroCount_lower`, `zeroCount_twoSided`). Consequently, for every bandwidth `T = u · 2πe^{2L}`
      the Shannon–zero surplus satisfies the exact variational identity
      `2TL/π − 2 zeroCountMain T = 2e^{2L} − 2e^{2L}(u log u − u + 1) ≤ 2e^{2L}`
      (`shannonZeroSurplus_eq_landau_deficit`, `shannonZeroSurplus_le_two_mul_exp`), attaining its
      unique global maximum `2e^{2L}` at the Landau height `T* = 2πe^{2L}` (`u = 1`,
      `shannonZeroSurplus_eq_two_mul_exp_iff`), turning negative above `2πe^{2L+1}`, and giving the
      uniform unconditional upper bound `2TL/π − 2 N(0, T) ≤ (2 + η)e^{2L}` across *all* bandwidths
      `T ≥ 0` (`eventually_shannon_sub_zetaZeroCount_le`). Together with the Bessel–projection
      law on constraint kernels (`finrank_mul_le_sub_of_concentrated_ker`) and the lower bound
      `(2 − η)e^{2L}`, this establishes the unconditional two-sided `(2 ∓ η)e^{2L}` dimension law
      for the near-radical of `ζ` (`zeta_landau_widom_two_sided_dimension_law`), the two-sided
      Landau–Widom rate `−log μ(L) ≍ 2π² N(T*)/log N(T*)` via
      `N(0, T*)/log N(0, T*) = (1/2 + o(1))e^{2L}` (`eventually_zetaZeroCount_edgeRate_div_log_bounds`,
      `exists_twoSided_truncKernel_log_energy_landauRate`,
      `eventually_near_radical_subspace_landauRate`), and critical-line zero-side coercivity
      `∑_{ρ ∈ S} m_ρ |f̂(γ_ρ)|² ≤ Re W_Z(f, f)` (`sum_norm_sq_paperFT_le_re_W_of_criticalLine`).

### 3.7 Hecke incidence, the collar between towers, and the successor cell

23. **Cartesian law and rank-`P` Kronecker splitting.** Two Hecke cycles meet through the primes only
    when their exponent vectors differ in one coordinate `p`, with weight `τ_p(|v_p(a) − v_p(b)|)`: the
    prime part is a product of one tower per prime (`heckeIncidence_eq_towerWeight`). Off-`p`
    valuation agreement is equality of the prime-to-`p` cofactor `primeCofactor p a = a / p^{v_p(a)}`
    (`primeCofactor_eq_iff_factorization_eq_off`), so on any `P`-smooth support `S` the Hecke form
    splits as `heckeFormOn S c = Σ_{p ∈ P} primeSliceForm p S c` with zero cross-prime prime coupling
    (`heckeFormOn_eq_sum_primeSliceForm`), each slice is bounded by `E_p Σ_{a ∈ S} c(a)²`
    (`abs_primeSliceForm_le`), and the total prime self-intersection obeys
    `|heckeFormOn S c| ≤ (Σ_{p ∈ P} E_p) Σ_{a ∈ S} c(a)²` (`abs_heckeFormOn_le_sum_eulerEnvelope`).
    On inductive rank-`P` product boxes `towerProductBox B p M`, the slices reduce to single-prime
    tower forms (`primeSliceForm_towerProductBox_self`), and the resonant train `c ≡ 1` attains
    `Σ_{p ∈ P} E_p` asymptotically (`exists_towerForm_one_gt_of_lt_eulerEnvelope`,
    `exists_heckeForm_box_one_gt_of_lt_add_eulerEnvelope`).
24. **Resonators, the collar between towers, and positivity of the finite-Euler-product form.** On
    `{p, q}`-boxes the cross-prime remainder against the Euler envelopes is negative definite
    (`resonatorRemainder_neg`), and on any `P`-smooth support `S` each cross-lag form obeys
    `|crossLagOn p q S c| ≤ Σ_{a ∈ S} c(a)²` (`abs_crossLagOn_le`), so `rankPResonatorRemainder P S c`
    is bounded by `−(Σ_{p ∈ P} (E_p − (|P| − 1) w_p²)) Σ_{a ∈ S} c(a)²` (`rankPResonatorRemainder_le`,
    `rankPResonatorRemainder_le_card`); since `2 w_r² < E_r` for all `r ≥ 2`
    (`two_mul_resonatorWeight_sq_lt_eulerEnvelope`), it is negative definite for every `1 ≤ |P| ≤ 3`
    (`rankPResonatorRemainder_neg_of_card_le_three`). Between any `1 ≤ a < b`, the narrow archimedean
    collar density is `ω(log(b/a)) = b√(ab)/(b² − a²)` (`archLevyDensity_log_div_nat`), and on `S` the
    collar form splits into `intraTowerCollarForm P S c + crossTowerCollarForm P S c`
    (`collarFormOn_eq_intra_add_cross`). Along each prime `p`,
    `τ_p(k)/log p < ω(k log p) ≤ (p²/((p² − 1)log p)) τ_p(k)` (`archLevyDensity_mul_log_prime_bounds`),
    bounding the intra-tower collar against the Euler envelopes by
    `(Σ_{p ∈ P} (p²/((p² − 1)log p)) E_p) Σ_{a ∈ S} c(a)²` (`abs_intraTowerCollarForm_le`); across
    towers (`heckeIncidence a b = 0`), `collarWeight a b ≤ (b/4)(√(b/a) + √(a/b))` against the pole
    pairing (`collarWeight_le_polarWeight_mul`), `collarWeight a b ≤ (4/3)√(a/b)` when `2a ≤ b`
    (`collarWeight_le_of_two_mul_le`), and for any disjointly supported bump family `{g_a}_{a ∈ S}`
    the continuum collar coupling is bounded by the diagonal shift-jump self-energy
    (`disjoint_family_shift_sq_eq`, `disjoint_lattice_collar_le_selfJump`). Consequently,
    `finiteEulerLatticeForm S κ c = κ Σ_{a ∈ S} c(a)² − heckeFormOn S c` is positive semidefinite
    whenever `κ ≥ Σ_{p ∈ P} E_p` (`finiteEulerLatticeForm_nonneg_of_sum_eulerEnvelope_le`) and on
    `{p, q}`-boxes across all dimensions iff `κ ≥ E_p + E_q` (`box_finiteEulerForm_nonneg_forall_iff`),
    while `collarCoupledEulerLatticeForm` and its pole-compensated form (`λ_pole ≥ B_max/4` on
    `c ≥ 0`) are nonnegative at their exact envelope thresholds (`collarCoupledEulerLatticeForm_nonneg`,
    `poleCompensatedCollarLatticeForm_nonneg`).
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
    `five_sixths_lt_GD_one`), yet satisfies `HD(1) < 254/375 < 3/4`
    (`HD_one_lt_twoHundredFiftyFour_div_threeHundredSeventyFive`, `HD_one_lt_three_quarters`): no
    profile supported below `λ = 1` reaches `3/4`. Beyond `λ = 1`, a flat-top window under a
    pair-correlation bound `F ≤ B` gives `2/3 + 1/(3(3B − 2))`. A two-window mixture of bandwidths
    `1` and `4/3` has the exact optimal envelope `2/3 + (181 − 18B)²/(1728(91 + 9B))` at mixing
    weight `(1 + 36B)/(2(91 + 9B))`, which lies in `(0, 1)` and beats `2/3` for `−1/36 < B < 181/18`;
    it reaches `3/4` at weight `4/9` iff `B ≤ 2954/1035` (slightly past `117/41`, the threshold at
    weight `7/16`), and beats `HD(1)` (`180433/266112 > 254/375 > HD(1)`) up to `B = 7`
    (`two_sub_mixQ_le_mixOpt_and_eq_at_weight`, `mixOpt_values_and_three_quarters_criterion`).
28. **Two routes past the blind spot, each with one unproved input.** The pair `(P, Q)` remembers
    what `Â` forgets. Adding the full spectral slack to the rank–trace functional cancels its
    prime-side part identically and leaves `(c²/4) rank P` minus a coupling defect
    (`rank_trace_add_totalSlack_eq`). Unconditionally the zero-side slack is at most
    `(λ − H(λ) + ε)N`, which refutes the slack route to `HD(1)` for every `λ < HD(1)` and to `3/4`
    for every `λ < 3/4` (`not_HD_one_zeroSideSlack_of_lt_HD_one`,
    `not_three_quarters_zeroSideSlack_of_lt_three_quarters`). On `λ ∈ [3/4, 1]` a slack
    `≥ (3/4 − H(λ))N` gives three-quarters of the zeros on the line (`zeta_three_quarters_of_spectralSlack`);
    in the displaced-pair model reaching target `q` needs `3(1 − q)(1 + 2η) ≥ 1` (`η ≥ 2/121` for
    `q = 254/375 > HD(1)` vs. `η ≥ 1/6` for `q = 3/4`, `hyperbolic_displacedPair_general_target_iff`),
    and non-coalescence alone is not enough (`macroscopic_displacedPair_counterexample_at_four_thirds`).
    The other route is `RHTower.PrimeSurplusFourThirds`, filling the margin `1/18` above the
    diagonal constant `43/36` at bandwidth `4/3` (`zeta_three_quarters_from_prime_surplus`); its
    analytic decomposition is the subject of Trans-Threshold Pair Correlation. There the smooth-window
    certificate removes, unconditionally, every channel except the coalescent prime pairs
    `0 < |log(n/m)| ≤ T^{−1+η}`: `N₀*(T, 2T) ≥ (29/36 − ε)N(T, 2T) − coalescentSurplus`
    (`TransThresholdPairCorrelation.zeta_coalescent_certificate`). So the second route is one
    number, the normalised coalescent surplus `β`: `29/36 − β` beats `2/3` iff `β < 5/36`, beats
    `HD(1)` once `β ≤ 577/4500`, and reaches `3/4` iff `β ≤ 1/18`
    (`zeta_N0star_and_offLineMoment_of_coalescentSurplus`,
    `coalescent_budget_thresholds_for_two_thirds_HD_one_and_three_quarters`). The affine models of
    the trans-threshold form factor calibrate `β`: an unsigned additive sieve at its factor-two
    parity limit gives `49/72 > 254/375 > HD(1)` but reaches `3/4` only below `Υ = 8/9`, so `3/4`
    needs signed cancellation in the coalescent band; the spectral sieve beats `HD(1)` up to
    `Υ ≤ 1186/375` (`11/16 > HD(1)` at `Υ = 3`) and reaches `3/4` exactly at the parity limit
    `Υ = 2`; the Hardy–Littlewood (GUE) model has negative surplus and gives `13/16`
    (`five_model_separation_of_HD_one_and_three_quarters`). No bound on the coalescent surplus is
    proved. The proportions transfer without a simplicity hypothesis, through the reflection bound
    `2R(T₁, T₂) + N₀*(T₁, T₂) ≤ N(T₁, T₂)` for the right-zero multiplicity `R`
    (`two_mul_sum_right_add_N0star_le`, `cumulative_N0star_of_dyadic_N0star`,
    `eventually_dyadicWindowTail_le_selberg_upper_of_N0star`,
    `eventually_offLineMoment_le_of_zetaGateFrom_N0star`). The certified proportions feed back into
    the corpus unconditionally: both the dyadic window off-line moment and the cumulative
    `offLineMoment V` improve from `67/1000` to `66/1000`
    (`eventually_dyadicWindowTail_le_sixtySix_thousandths`,
    `eventually_offLineMoment_le_sixtySix_thousandths`; `57/1000` under either route to `3/4`), and
    the double-exponential uniqueness threshold for even functions vanishing at the simple critical
    zeros drops from `b > 3` to `b > 5000/1681`
    (`ae_eq_zero_of_doubleExp_simpleCritical_montgomeryTaylor`; `b > 8/3` under the surplus).

### 3.9 The λ-ring of the scaling surface and Hecke–Lefschetz rigidity (`TheLambdaRingOfTheScalingSurface`, `LambdaRingEffectivityAndHeckeLefschetzRigidity`)

29. **Adams operations, Hecke cycles, the pole-plane splitting, and Hecke–Riemann–Roch rigidity.**
    `polarPart` and `prim` are orthogonal idempotents splitting any polar surface into the pole
    plane and the primitive complement with pairing `−defect`. The Newton–Witt exponential splits
    any trace `(1 + q^j) + g_prim(j)` into the pole factors times the primitive part
    (`sigmaSeries_pole_split`); over `𝔽_q` this is `zeta = poleZeta · P₁`. Over `ℚ` the normalized
    Adams operators are exact intersection, polar and defect isometries commuting with the splitting
    (`pair_adamsOp`, `defect_adamsOp`). The Hecke correspondences `T_a = √a · adamsOp a` satisfy
    `T_a H = aH`, `T_a V = V`, the Hecke cycles obey `Γ_a(g)·Γ_b(g) = b · L(Δ_g, a/b)`
    (`pair_heckeCycle`), and the arithmetic Lefschetz number splits as
    `(a + 1)(x·H)(x·V) − √a · defect(adamsOp a x, x)` (`arithLefschetz_split`). Frobenius, graphs
    and Lefschetz numbers exist on the scaling surface; Riemann–Roch does not follow from them, and
    the golden datum obeys the same identities (`goldenDatum_lambdaRing_and_not_unitary`).
    * *Why Hecke stability eliminates `AmpleAxiom` and forces the coercive floor:* Without `λ`-ring
      invariance, the ample half-space `ampleHalfSpace = {x | 0 ≤ x·(H + V)}` satisfies
      `RiemannRochAxiom` unconditionally on every polar surface (`ampleHalfSpace_riemannRoch`),
      failing only `AmpleAxiom`. Once `S` carries even a single correspondence `T` scaling
      `(x·H, x·V)` by `(1, a)` or `(a, 1)` (`a > 1`), `T`-invariance substitutes for `AmpleAxiom`
      completely: for *every* `T`-invariant subset `E ⊆ ampleHalfSpace` — **without assuming
      `AmpleAxiom E`** — `RiemannRochAxiom E ↔ openPositiveCone ⊆ E ∧ ∀ x, 0 ≤ defect(x, x)`
      (`hodgeIndex_iff_tilted_openPositiveCone`,
      `riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg_of_hecke`,
      `scalingSurface_hecke_riemannRoch_iff`, `scalingSurface_adams_riemannRoch_iff`).
    * *Calibration over `𝔽_q` and the Rosati–Frobenius source cone violated by `goldenDatum`:* On any
      `CurveDatum D`, `D.spanHecke m` scales `x·H` by `q^m`, preserves `x·V`, and scales pairings and
      defects by `q^m` (`windowSurface_hodgeIndex_iff_spanHecke_ample`); on `goldenDatum` at
      `{0, 1}`, `goldenHeckeEscape = 3H − V + 2 goldenCounterexample` lies in `openPositiveCone`
      (`x² = 2, x·(H + V) = 2`) yet `spanHecke 1` maps it outside `ampleHalfSpace`
      (`(spanHecke 1 x)·(H + V) = −2`, `goldenHeckeEscape_violates_spanHecke_ample`). The Rosati
      square-sampling energy `D.rosatiSourceEnergy S x = D.frobSquareMass S (fun k => x.2.2 k * q^{k/2})`
      defines `D.rosatiSourceCone S`, which satisfies `defect ≤ rosatiSourceEnergy` and
      `rosatiSourceCone S ⊆ positiveCone` unconditionally on every `CurveDatum D`, is invariant
      under `spanAdams m` and `spanHecke m` and satisfies `RiemannRochAxiom` and `BezoutAxiom` on
      every unitary curve (`spanAdams_and_spanHecke_mem_rosatiSourceCone_of_unitary`), and **is
      violated by `goldenDatum` at `S = {1}`** (`rosatiSourceCone_riemannRoch_iff_unitary`,
      `goldenDatum_not_rosatiSourceCone_riemannRoch`).
    * *The universal arithmetic Lefschetz–adjunction identity and the Hecke–Lefschetz envelope cone:*
      The Adams coboundary `adamsVar a x = ψ^a x − x` reverses the sign of `polar` on the nef
      quadrant (`polar_adamsVar_self`: `polar(ψ^a x − x, ψ^a x − x) = −((√a − 1)²/√a) polar(x, x) ≤ 0`),
      giving the pole-cancelled Lefschetz–adjunction identity
      `arithLefschetz x a − ((a + 1)/2)(x·x) = ((√a − 1)²/2) defect(x, x) + (√a/2) defect(ψ^a x − x, ψ^a x − x)`
      (`arithLefschetz_eq_selfPair_add_defect_add_adamsVar`,
      `hodgeIndex_iff_abs_arithLefschetz_sub_polar_le`). The cone `lefschetzEnvelopeCone` of cycles
      in `nefQuadrant` obeying `|arithLefschetz x a − ((a + 1)/2) polar(x, x)| ≤ √a polar(x, x)` across
      all `a > 0` contains `0, H, V, H + V`, is unconditionally Adams- and Hecke-stable
      (`adamsOp_and_heckeCorrespondence_mem_lefschetzEnvelopeCone`), is self-isotropic on `x·(H + V) ≤ 0`
      (`lefschetzEnvelopeCone_selfPair_eq_zero_of_pair_ample_nonpos`), and satisfies
      `RiemannRochAxiom` (without assuming `AmpleAxiom`) iff `RiemannHypothesis` holds
      (`lefschetzEnvelopeCone_riemannRoch_tfae`); on any `heckeSpanCycle cH cV S d g`, the Hodge
      defect is the negative quadratic form in `b · arithLefschetz (prim (diagCycle g)) (a/b)`
      (`defect_heckeSpanCycle_eq_sum_arithLefschetz_prim`).

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
    unconditionally at the endpoint with no clustering hypothesis: for `σ ≥ 0`,
    `zetaZeroWidth ≤ σ` iff the defect is at least
    `−Ce^{2σr}(∫f² + ∫(f′)²)` at every aperture, for one aperture-independent `C`.
    Both the all-parity and odd floor-rate sets are exactly `[zetaZeroWidth, ∞)`;
    the least exponent is attained (`fullDefectFloorRates_eq_Ici`,
    `oddDefectFloorRates_eq_Ici`). The unconditional floor has rate `½`; any power saving
    would be a zero-free strip. Through degree `181/500` the odd floor is `0`. Over `𝔽_q` the law
    holds in `L²` with no Sobolev correction, since the zeros of a curve have bounded local count:
    `Re W(f, f) ≥ −2N log q·n·e^{2δa}‖f‖²` at aperture `a` with `δ = log R/log q`, and Turán's
    power-sum theorem gives two-bump tests at aperture `≈ νlog q/2` with
    `Re W ≤ log q (N − R^ν/C_M)‖f‖²`, `C_M` polynomial (`re_W_curveConfig_ge_floor`,
    `exists_lagTest_le`): the `L²` floor rate of a curve is exactly twice its zero width, the
    unclustered case of Square-Root Threshold's width–floor alternative.
33. **Hecke-stable ampleness, section counts, and the universal floor law**
    (`SectionCountRiemannRochAndPrimeBlindSelectivity`, `SectionEffectivityAndTheUniversalFloorLaw`).
    * *Universal floor law for ample cones:* On any polar surface, every cone `E` of nonnegative
      ample degree (`0 ≤ x·(H + V)` on `E`) that satisfies `AmpleAxiom` obeys
      `RiemannRochAxiom E ↔ openPositiveCone ⊆ E ∧ ∀ x, 0 ≤ defect(x, x)`
      (`riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg`,
      `ampleHalfSpace_ample_riemannRoch_dichotomy`). No cone of nonnegative ample degree with
      `AmpleAxiom` — however constructed from sections, node counts or additive structure — can have
      a `RiemannRochAxiom` that escapes equivalence to the defect floor `∀ x, 0 ≤ δ(x, x)`.
    * *Sign-free Bézout positivity from source section readings:* By hyperbolic AM–GM
      (`polar_sq_sub_polar_mul_polar`) and Cauchy–Schwarz, `sourceCone Φ` (and `sourceSectionCone Φ`)
      satisfies `BezoutAxiom` without reading `x²` whenever `0 ≤ Φ` and `δ(x, y)² ≤ Φ(x)Φ(y)`
      (`sourceCone_bezout_of_defect_sq_le`, `sourceCone_bezout_of_source_nonneg`), and supplies
      positive section readings `sourceSectionH0 ≥ 1` on `polar(x, x) > Φ(x)`.
    * *Hecke-stable ampleness:* Hecke correspondences act on the pole plane with weights `(a, 1)`, so
      a cycle keeps nonnegative ample degree under all `T_a` iff it lies in the double-null nef
      quadrant `{x·H ≥ 0, x·V ≥ 0}`; on every polar surface Hodge index holds iff the open positive
      cone lies in that quadrant, and over `ℚ` a single scale decides: RH iff `T_2` maps the open
      positive cone into the ample half-space
      (`scalingSurface_hodgeIndex_iff_heckeCorrespondence_openPositiveCone_ample`).
    * *Prime-power node section counts, Chebyshev bridge, and odd pole-charge cancellation:* On the
      odd degree-`r` subsurface, the pole charge `2A(F)²` cancels identically between `polar(x, x)`
      and `defect(x, x)`, leaving the pole-free self-intersection
      `x² = 2ab + 2(b − a)A(F) + primeNodeCorrelationObstruction r F − archGaugeBudget r R F`
      (`scalingSubsurface_odd_pair_self_eq_poleFreeLedger`,
      `localPair_self_eq_primeNodeObstruction_sub_archGaugeBudget_of_odd`). The prime-node
      obstruction is supported purely on `primePowerNodes r = (relevantShifts r).filter IsPrimePow`
      (`primeNodeCorrelationObstruction_eq_sum_primePowerNodes`), the prime-node section count obeys
      `primeNodeH0 r W − primeNodeH1 r W = dim W − #(primePowerNodes r)` and
      `dim W − ψ(e^{2r})/log 2 ≤ dim W − #(primePowerNodes r) ≤ primeNodeH0 r W`
      (`finrank_sub_card_le_primeNodeH0`, `finrank_sub_primeNodeCount_div_log_two_le_primeNodeH0`),
      and `∫_0^s(e^u + 1)du − ψ(e^s) = E(s)`
      (`polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect`). Prime-blind tests pay only their
      pole charge (`finrank_primeBlind_subspace_eq_zero`), and while bare rank counts are invariant
      under nowhere-vanishing diagonal reweighting (`h0_weightedDirichletSampling_shiftedPair_eq_vonMangoldt`),
      the Frobenius norm strictly separates `Λ` from the shifted pair by a factor `> 4`
      (`frobeniusMass_weightedDirichletSampling_shiftedPair_gt`).

### 3.11 The all-parity critical-deficit identity

The odd ledger extends to every real `C²` compactly supported test without
imposing parity or vanishing pole moments. Put `a_F(t)=∫F(x)F(x+t)dx`,
`D=(d/dt−½)²`, `I(t)=e^{−t/2}∫₀ᵗ(e^u−ψ(e^u))du`, and let `J(F)` be the
nonnegative horizon-resolvent energy of Arithmetic Compensation Theory. For
support in `[-A,A]`,

`fullZeroForm F = (gammaBracket 0−2)‖F‖² + biScaleLevyEnergy F + 4J(F)
                 + 2∫₀^{2A} I(t) D a_F(t) dt`.

The polar autocorrelation integral is exactly `2J(F)`, so it contributes a
nonnegative term instead of an aperture-sized error. The pole-tilted
factorization gives `|D a_F(t)| ≤ ¼‖F‖²+‖F′‖²`. Together with the integrated
deficit bounds this yields, for every `0<α<3/5`,

`fullZeroForm F ≥ −C exp(A−κ A^α)(‖F‖²+‖F′‖²)`

uniformly in aperture and parity. It also gives the attained endpoint in
item 32 and the corresponding graded source Riemann–Roch law. An
aperture-independent Sobolev floor self-improves to Hodge index and RH; its
existence remains an arithmetic estimate. The derivative norm cannot be
dropped on unrestricted tests. See
[AllParityCriticalDeficitAndEndpointSobolevLaws.lean](AllParityCriticalDeficitAndEndpointSobolevLaws.lean).

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
| One prime always sees everything | Resonant primes, where two right zeros share `p^{ρ − ½}`, can hide classes; with finitely many right zeros there are only finitely many of them, while at a non-attained top with real parts strictly increasing to their supremum (`|Im ρ| → ∞`) the symmetric Wolff configuration has Toeplitz matrix `(4 Σ c_i) • 1` and `hermNegIndex = 0` on every finite window (`OnePrimeAgainstTwoAndWolffTowerObstruction`). Two primes eliminate both obstructions. |
| Multiplicities count | The defect counts distinct right zeros; depth and multiplicity are invisible. |
| A finite degree certifies positivity | No degree works for all configurations over `ℚ`; over `𝔽_q` the window `2g` does. |
| The comb aggregate is an intersection number | On resonators the prime intersection has no cross-prime terms; the aggregate is a mean-field shadow. |
| The pronic weight is the successor intersection | It is the pole mass of the cell; the intersection is the collar `ω(log(1 + 1/k)) ≍ k/2`. |
| The three-quarters modules prove that 75% of the zeros are on the line | They prove `(3/4)N` *conditionally*: on a zero-side slack `S(T) ≥ N/12`, or on `PrimeSurplusFourThirds`. The unconditional content is `(2/3 − ε)N + S(T) ≤ N₀*` with the slack retained, the `43/36` diagonal constant, the `O(T^{5/6}log²T)` cross term, and `N₀* ≥ (29/36 − ε)N − coalescentSurplus` with the surplus unbounded. |
| Adams operations make the scaling surface a Weil surface | They give Frobenius, graphs and Lefschetz numbers; the golden datum has them too. Riemann–Roch is still missing. |
| The rank–trace form is capped at `2/3` | The form has capacity `2 − κ` (reaching `1` at `κ = 1`); `2/3` is `2 − κ(1)` from stopping pair correlation at `λ = 1`. |
| A rank-based section count is selective | Diagonal reweighting leaves kernels and `h⁰` unchanged; the shifted pair and `Λ` have the same counts. Selectivity needs a norm or the defect `E(s)`. |

---

## 6. Questions the programme answers and the tools it builds

### 6.1 Questions

1. **Which ingredients of Weil's proof exist for `ℤ`?** The pairing, the fibres, Lefschetz,
   adjunction, Adams operations and Hecke graphs: all exact. Graded source cones have RR at
   every aperture. What remains is an independent source construction carrying RR together
   with the full Bézout or ample axiom; existence of such a cone is equivalent to RH.
2. **What does the failure of the Hodge index measure?** The number of distinct zeros right of the
   line — never depth or multiplicity — filtered by degree, split additively into reflection
   sectors at every degree, and carried by the Hecke orbit of any one spectrally generic test, and
   for all but finitely many primes by one prime tower when the right zeros are finite in number
   (§3.4). For `ζ` it is finite at every degree (item 14), where every curve and lag lattice has
   `0` or `∞`. The growth rate of the Sobolev-normalized defect floor in the degree is the zero width,
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
   One side suffices, with one exception. A lower bound `N_k ≥ q^k + 1 − Cq^{k/2}` forces purity;
   an upper bound `N_k ≤ q^k + 1 + Cq^{k/2}` (Bombieri's shape) forces it unless a top outer
   eigenvalue is a positive real, i.e. a real zero (`oneSided_forcing_tfae`; cause: unimodular
   power sums change sign infinitely often). The golden datum is such a real-zero fake: it obeys
   every upper bound with `C = 0`. On the scaling surface difference lag tests detect every impure
   curve, sum lag tests every impure curve without a real zero (`differenceLagTests_nonneg_iff_unitary`,
   `sumLagTests_nonneg_iff_unitary`). `ζ` has no real zeros in `(0, 1)`, so the upper-bound route
   over `ℤ` has no real-zero exception.
   In genus one the Hodge index on the window `{Δ, Γ_F}` is a linear degree law: the isotropic graph
   class of `m − nF` with `x · V = 1` has defect `2 deg(m − nF)`, so Hasse is degree positivity of
   the ring `ℤ[F]` (`genusOne_hasse_tfae`; golden: `deg(2 − F) = −1`). It uses the theorem of the
   square (`graphCycle_square`); distinct Hecke scales of `ℤ` satisfy no such relation even up to
   fibres (`heckeCorrespondence_no_square_relation`): the scaling surface has graphs of the Hecke
   monoid, not of a ring of correspondences.
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
  side, Frobenius eigenvalues and weights, resonant primes, the Laurent-moment Toeplitz identity,
  the well-founded visible locus `wfVisibleSet`, and the Wolff annulus counterexamples to
  non-well-founded single-prime class extraction.
- *Bézout positivity* through the Lévy jump form of the collar.
- *Source section cones*: determinantal effectivity defined from source data, Hecke-stable and ample.
- *Hecke incidence and the multi-tower collar*: the Cartesian and rank-`P` Kronecker laws, rank-`P`
  resonator remainders, intra- and cross-tower collar bounds against `Σ_p E_p` and the pole pairing,
  positivity decision for the finite-Euler-product form on lattice tests, and the successor cell.
- *Rank–trace inertia* with spectral slack.
- *The `λ`-ring and Hecke–Lefschetz rigidity*: Adams operations, Hecke correspondences and cycles,
  arithmetic Lefschetz numbers, the pole-cancelled Lefschetz–adjunction identity, Hecke–Riemann–Roch
  rigidity without `AmpleAxiom`, the Rosati–Frobenius source cone over `𝔽_q` violated by
  `goldenDatum`, and the Hecke–Lefschetz envelope cone.
- *The odd-sector ledger and section counts*: Lorentz–polar identity, reflected-prime/polar and
  Chebyshev ledgers, degree floors and the zero width, the universal floor law for ample cones,
  sign-free Bézout positivity from source section readings, prime-power node section counts
  `h⁰ ≥ DoF − node count`, and exact pole-charge cancellation on odd cycles.
- *The Landau–Widom near-radical calculus*: two-sided Riemann–von Mangoldt zero counts, the exact
  Shannon–zero variational identity `2TL/π − 2N(0, T) ≤ (2 + η)e^{2L}`, sharp Bessel–Shannon
  concentration bounds `dim V ≤ 4LT_ε(L)/π`, the two-sided `(2 ∓ η)e^{2L}` near-radical dimension
  law, and the Landau–Widom rate `−log μ(L) ≍ 2π² N(T*)/log N(T*)`.

---

## 7. Research boundaries and open questions

1. **Riemann–Roch for `ℤ` — the open core.** The structure is settled: every cone of nonnegative
   ample degree with the ample axiom, and every Hecke-stable cone in the ample half-space, has
   Riemann–Roch exactly when the open positive cone lies in it and the defect is nonnegative
   (items 29, 33); source section readings give Bézout positivity without reading `x²`; prime-power
   node vanishing gives `h⁰ ≥ dim W − #(prime-power nodes)` with the deficit equal to `E(s)`; and away
   from the low-frequency divisor `D_a` and the pole the Hodge index, Riemann–Roch and ampleness
   hold unconditionally at every degree (item 20). Open: close the finitely many low-frequency
   directions read by `D_a` and the pole, at every degree, by an effectivity defined without the
   sign of the form. Equivalently, prove `0 ≤ δ(x, x)` on those directions.
2. **An arithmetic section law.** The source cones are well defined, ample and Hecke-stable, and
   their Riemann–Roch is a coercive floor (item 20); the Rosati source cone over `𝔽_q` has
   Riemann–Roch exactly on unitary data and the golden datum violates it (item 29). Open: a
   source-defined cone over `ℤ` whose Riemann–Roch follows from a law of its sections — a count, a
   vanishing, a Riemann–Roch-type inequality — rather than from the floor, and which reduces over
   `𝔽_q` to Weil's.
3. **The degree floor at a rate below one half.** The Sobolev-normalised floor rate is the zero
   width, with the endpoint attained for all parities (§3.11); unconditional
   Vinogradov–Korobov savings still leave exponential rate `½`. Any rate below `½` is a
   zero-free strip. Which effectivity input, if any, lowers the rate before it reaches the sign?
4. **Beyond `2/3` and `HD(1)`.** No profile supported below `λ = 1` reaches `3/4` (item 27). Open:
   either input that gives `3/4` — a zero-side spectral slack `S(T) ≥ N(T, 2T)/12` near `λ = 1`, which
   needs macroscopic hyperbolic pair displacement, or a bound `β ≤ 1/18` on the coalescent prime
   surplus at bandwidth `4/3` (item 28), or `F ≤ B` with `B ≤ 2954/1035` through the two-window
   mixture. The sieve calibration says the coalescent bound needs signed cancellation among
   coalescent prime pairs; any `β < 5/36` already beats `2/3`. Trans-Threshold Pair Correlation owns
   the trans-threshold inputs.
5. **One prime against two.** Two primes carry the whole defect (`one_prime_vs_two_primes_complete_law`),
   while on one prime tower `towerGram Z g ℓ K j k = towerMoment Z g ℓ (j − k)` depends exclusively on
   the two-sided Laurent moments (`towerGram_apply_eq_towerMoment`), so the tower defect counts at
   least the well-founded visible locus `wfVisibleSet Z g ℓ` (including every bounded-ordinate region
   and any threshold with finitely many zeros above it, `wfVisibleSet_sandwich_and_infinite_law`,
   `upperLevels_wellFounded_of_bounded_im`). At a non-attained top where real parts strictly increase
   toward `1/2 + Θ` with `|Im ρ| → ∞`, the two-annulus Wolff difference kills all Laurent moments
   `m ∈ ℤ` (`exists_counterexample_to_laurent_class_extraction_without_wellFounded`) and the
   symmetric Wolff configuration has Toeplitz matrix `(4 Σ'_i c_i) • 1` and `hermNegIndex = 0` on
   every finite window (`exists_symmetric_wolff_toeplitz_blind_configuration`). Open: rule out
   vertical Wolff accumulation for `ζ` on a single prime tower without invoking a second prime.
6. **Visibility when off-line zeros cluster.** Unconditionally, either every near-top zero is
   visible at the doubly-logarithmic lag and the degree-defect floor rate equals the zero width, or
   off-line zeros cluster without bound in unit windows (item 15,
   `scalingSurface_defectRate_eq_zetaZeroWidth_or_offLine_cluster`). Open: the clustering branch —
   either exclude it, or prove the corresponding visibility and unrestricted `L²` rate law
   inside it. The all-parity Sobolev rate law is already unconditional; its derivative
   normalization must not be confused with this `L²` question.
7. **From lattice forms to the form of `ζ`.** On finite `P`-smooth supports the prime incidence, the
   resonator remainders and the finite-Euler-product form are decided exactly (items 23–24), but
   cross-tower collar positivity uses a bound premise, the pole-compensated form needs `c ≥ 0` and
   a pole weight at least `max S/4`, and no lattice form is identified with the complete form of
   `ζ`. Open: a lattice-to-continuum identification that carries these positivity laws to Weil's
   form, with the archimedean collar and signed coefficients.

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
| `TheScalingSurfaceOfACurve`, `TheFrobeniusSpanIsTheTowerOfTheScalingSurface`, `TheDegreeFiltrationOfACurveIsItsWindowFiltration`, `TheFirstNegativeLagOfACurve`, `TheWeilFloorOfACurveIsItsZeroWidth` | the scaling surface of a curve; three Hodge index theorems; the span as period quotient; degree filtration = window filtration; lag tests read point counts, purity = lag positivity, Turán-located first negative lag; `L²` floor rate = twice the zero width |
| `HodgeIndexFromEffectivity`, `BezoutEffectivityAndTheBeurlingObstruction`, `DistinctEffectiveCyclesMeetNonnegatively` | effectivity axioms ⟺ Hodge index; Bézout positivity through the collar |
| `TheScalingSurface`, `ArithmeticHodgeIndexSignatureLaw`, `InfiniteGenusLaw`, `TheGenusIsTheApertureOfTheRadical`, `NumericalEquivalenceOnACurveIsTheFrobeniusIdeal`, `TheNearRadicalOfZetaIsFiniteDimensional`, `LandauWidomNearRadicalLaw` | the scaling surface of `ℤ`; signature law and selection of `Λ`; no exact annihilators; over `𝔽_q` the radical is exactly `P(T_q)`(tests), opens at aperture `d log q/2` and is then infinite-dimensional; over `ℚ` the near radical is finite-dimensional (`≤ 4LT_ε(L)/π`) and obeys the two-sided `(2 ∓ η)e^{2L}` Landau–Widom count and rate `−log μ(L) ≍ 2π² N(T*)/log N(T*)` |
| `FiniteConfigurationPontryaginLaw`, `TemperedConfigurationPontryaginLaw`, `TheHodgeDefectCountsTheRightZeros` | the Pontryagin law, finite, tempered and general |
| `TheReflectionSectorsOfTheHodgeDefect`, `TheDegreeFiltrationOfTheHodgeDefect`, `SchurLendingOddHodgeIndexPastFirstPrime`, `WhatTheFailureOfTheHodgeIndexMeasures`, `TheHodgeDefectOfZetaIsFiniteAtEveryDegree`, `TheHodgeIndexOfZetaHoldsAwayFromLowFrequencies` | sectors and degrees; `ζ` below `3/10` and the odd sector through `181/500`; multiplicity and depth invariance; Sobolev floor rate = width; the degree defect of `ζ` is finite (archimedean horizon and Bessel count) and lives on an explicit low-frequency grid |
| `TheVisibilityDegreeOfAnIsolatedPair`, `TheVisibilityDegreeOfRightZeros`, `HeightUniformVisibilityAndOffLineDensity`, `TuransInequalityWithoutBoundedOnLineDensity`, `DoublyLogarithmicVisibilityAndExcludedDepthLaw` | visibility degrees from on-line mass and densities; height-uniform visibility; eliminating the `log γ₀` Turán tail without bounded on-line density, two-sided `Θ_w(log γ₀)` law for `onLineEvenMass`, two-sided `Θ_{M,w}((1 + log log γ₀)/δ₀)` visibility lag, intrinsic on-line mass and Hodge-defect barriers, doubly-logarithmic contact-aperture and excluded-depth laws, and the clustering dichotomy |
| `TheKroneckerRankDichotomy`, `TheZerosOfAnExponentialPolynomialRecur` | recurrent configurations have defect `0` or `∞` |
| `TheHodgeDefectIsCyclic`, `TheHeckeTowerOfAPrimeIsThePeriodQuotient`, `AlmostEveryPrimeSeesEveryRightZero`, `TheTowerDefectCountsTheFrobeniusEigenvalues`, `OnePrimeSeesEveryWellFoundedLevel`, `OnePrimeAgainstTwoAndWolffTowerObstruction` | cyclic Pontryagin law; prime towers, Frobenius eigenvalues and weights; resonant primes; top-down class extraction, the tower law without finiteness, attained tops; Laurent-moment Toeplitz formula, two-annulus and symmetric Wolff single-prime Toeplitz blindness at non-attained tops, the well-founded visible locus `wfVisibleSet`, and two-prime completeness |
| `ResonatorKroneckerLaw`, `HeckeIncidenceCartesianLaw`, `TheResonatorRemainderIsNegative`, `TheAdjunctionConjectureMeanField`, `CrossTowerCollarAndFiniteEulerLatticePositivity` | Hecke incidence: Cartesian and rank-`P` Kronecker laws, rank-`P` resonator remainders, intra- and cross-tower collar bounds against `Σ_p E_p` and the pole pairing, positivity decision for the finite-Euler-product form on lattice tests, mean field |
| `ThePronicWeightIsThePoleMassOfTheSuccessorCell`, `TheSuccessorCollar` | the successor cell |
| `TheTwoThirdsConstantIsPairCorrelation`, `BreakingTheCoalescenceBlindSpotAndThreeQuarters`, `SpectralSlackConservationAndTheHyperbolicDisplacementThreshold`, `WhatAGramFunctionalCertifiesWithoutEffectivity`, `CoalescentSurplusAndTransThresholdProportionLaws` | rank–trace inertia, the coalescence blind spot, spectral slack, routes to `3/4`, corpus upgrades; coalescent-band budgets, sieve calibration of the surplus, the exact two-window envelope, the `N₀*` reflection bound |
| `TheLambdaRingOfTheScalingSurface`, `LambdaRingEffectivityAndHeckeLefschetzRigidity` | `λ`-ring, Adams operations, Hecke cycles, Lefschetz splitting, Adams–Hecke and Rosati source-cone Riemann–Roch rigidity, primitive arithmetic Lefschetz traces |
| `AllParityCriticalDeficitAndEndpointSobolevLaws` | positive horizon term, all-parity critical-deficit identity, Vinogradov–Korobov Sobolev floors, attained width endpoint and graded source Riemann–Roch |
| `RiemannRochForZAndTheReflectedPrimePolarLedger` | tautological cones, Lorentz–polar identity, odd-sector ledgers, `75e^r` and `(3 + ε)e^r` floors, first- and second-order de la Vallée Poussin Sobolev floors, shared derivative payment bootstrap, degree floor ⟺ zero width |
| `WhichArithmeticDataForceTheSign` | Toeplitz–Rosati reflection identity, pole masking of point counts, forcing equivalences over `𝔽_q` and on the scaling surface |
| `UpperLefschetzBoundsAreBlindOnlyToRealZeros` | one-sided power-sum sign law; lower Lefschetz bounds force purity, upper bounds force it except at real zeros; golden datum as real-zero fake; difference vs. sum lag tests |
| `TheDefectOfAGraphIsTwiceItsDegree` | isotropic unit-degree classes have linear defect; genus-one graph defect `= 2 deg`, Hasse as degree positivity, golden `deg(2 − F) = −1`; theorem of the square vs. numerically free Hecke scales |
| `SectionCountRiemannRochAndPrimeBlindSelectivity`, `SectionEffectivityAndTheUniversalFloorLaw` | nef quadrant and Hecke-stable ampleness, universal floor law `RiemannRochAxiom E ↔ openPositiveCone ⊆ E ∧ ∀ x, 0 ≤ defect(x, x)` for ample cones, sign-free Bézout positivity from source section readings, prime-power node section counts `h⁰ ≥ DoF − node count`, `DoF − node count = E(s)`, exact odd pole-charge cancellation, prime-blind section vanishing, diagonal relabeling invariance vs. Frobenius selectivity |
| `SourceDeterminantalSectionsAndArithmeticRiemannRoch` | source section cones, non-vacuous ampleness, Hecke stability, Riemann–Roch ⟺ coercive floor, Riemann–Roch past the first prime, all-aperture Chebyshev and de la Vallée Poussin floors |
| `SourceRiemannRochAwayFromTheLowFrequencyDivisor` | source effectivity (Riemann–Roch, ampleness, Hodge index) at every degree on the tests blind to the low-frequency divisor, coercivity `E(a)(1 − 1/π)` |
| `AllApertureSourceRiemannRochAndCoercivityLaws` | universal strict-ampleness rigidity, compensated polar surfaces and all-aperture ample source cones, no-Hardy-weight law, doubly-exponential Gaussian ceiling, closed-aperture polar ground-energy equivalence and strict-monotonicity self-upgrade, Sobolev source cones and zero-width equivalence |
| `ExactArithmeticSourceEffectivity` | literal Gamma–Lévy–horizon–prime-deficit source reserve, exact RR at every aperture and on the full compact surface, additive closure and one-scale Adams stability iff Hodge index |
| `FiniteDegreeConesCannotSatisfyBezout`, `ExactSourceEffectivityRequiresInfinitelyManyDegrees` | arbitrarily negative squares in every finite-reading fibre, with both degrees fixed and arbitrarily small L² source change; exact arithmetic effectivity has no finite-dimensional linear reading description |
| `PoissonPrincipalCyclesOnTheScalingSurface` | nonzero genuine Poisson principal representatives on the larger Meyer carrier, descended linear trace degree, exact compact smooth comparison with both pole moments retained, and rigidity of compact principal sources |
| `HeckeClassesDoNotMoveNumerically` | scaling eigenvectors lie in the fibre plane; nonidentity Adams fixed space is zero, Hecke fixed space is the vertical fibre line; every finite distinct-scale orbit of a nonzero compact source is linearly independent and has no nonzero numerical relation |
| `ArithmeticMajorantsSupplyBezout` | an explicit arithmetic quadratic reserve gives Bézout and ampleness on the original pairing at every positive aperture; its positive mass floor forces ample-zero effective classes to vanish, and its extra reserve obstructs Riemann–Roch |
| `OriginDegreeDoesNotDescendThroughPoissonBoundaries` | origin evaluation of an actual sharp square is strictly positive exponential mass; a genuine Poisson boundary has positive origin degree, so this positive linear source degree cannot descend to cohomology |
| `MeyerNumericalRadicalAndMultiplicity` | ordinary trace radical is exactly vanishing of Xi values; genuine Poisson boundaries require all lower jets; equality of numerical and principal equivalence, and absence of square-zero quotient classes, are each equivalent to simplicity; trace positivity alone is equivalent to RH |
| `FiniteReadingsAndMassCannotSupplyBezout` | unit-mass Weil energy is unbounded in every finite linear reading kernel; every nonlinear reserve depending on those readings and exact L² mass admits a strict effective negative square |
| `PositiveQuadraticSourceCones` | positive quadratic reserves give additive convex source cones closed under nonnegative scaling; every finite fibre-invariant threshold containing the fibre quadrant generates the whole cycle space |
| `ExponentialSourceMassControlsTheFullPrimeSum` | exponentially decaying source-correlation bound and one full prime-sum bound by exponential position mass, uniformly across all compact supports |
| `BezoutCostsTwiceTheNegativeReserve` | exact factor-two law: original-pairing Bézout for threshold `δ+2R` iff the compensated defect `δ+R` is nonnegative; both RR criteria and scalar-coefficient corollaries |
| `PoleBlindPoissonBoundariesHavePositiveOriginDegree` | an explicit nonzero pure-source principal cycle has positive origin degree and vanishing pole and intersection readings; no nonlinear correction using the two pole values repairs origin-degree descent |
| `MeyerHilbertSchmidtSource` | actual resolvent admission to Hilbert–Schmidt class, factorial bounds for every lower Xi jet, and exact centered character and affine-shear jet transport |
| `MeyerBoundedCenteredOrbits` | bounded full-Hasse Hilbert–Schmidt orbits, bounded individual jet readings, critical highest-jet support and norm isometry are equivalent; global boundedness, or boundedness of the fixed Xi-avoiding source, holds iff RH plus Xi simplicity |
| `MeyerCriticalTopAlgebra` | bounded-orbit sources and genuine classes form nontrivial sharp-stable convolution subspaces; products vanish in off-line and multiple blocks; ordinary trace is positive and its value-zero radical annihilates this algebra |
| `MeyerSharpConvolutionAlgebra` | arithmetic sharp descends as a conjugate-linear convolution involution; positive Hermitian degree null squares annihilate all complex mixed readings |
| `GlobalArithmeticMajorantsSupplyBezout` | one aperture-independent arithmetic reserve gives a pointed generating convex cone with Bézout and strict ampleness on the original compact surface; its positive added reserve forces RR to fail |
| `MeyerSourceIntersectionSurface` | actual Poisson source surface and descended linear trace degree: RR is unconditional; Bézout, ampleness, and additive closure each hold iff RH; numerical and principal equivalence agree iff Xi zeros are simple |
| `FaithfulPositiveMeyerDegrees` | a faithful positive linear degree on genuine cohomology exists iff RH and Xi simplicity; a single jet has principal sharp square exactly when its reflected block is distinct or twice its order reaches multiplicity |
| `ArithmeticSharpAndTheHilbertAdjoint` | arithmetic sharp equals the actual full-Hasse Hilbert adjoint iff RH and Xi simplicity, equivalently iff a faithful positive linear degree exists on genuine cohomology |
| `FaithfulHilbertSchmidtSourceReserves` | a faithful descended Hilbert–Schmidt reserve gives Bézout, ampleness, convexity and generation unconditionally; its excess is half the squared adjoint defect, and RR or exact representation by a linear sharp-square degree holds iff RH plus Xi simplicity |
| `PositiveMeyerDegreesCanForgetClasses` | critical Xi evaluation gives an unconditional positive multiplicative degree on genuine cohomology, normalized on one sharp square and zero on the sharp square of an explicit nonprincipal source |
| `FlowInvariantMeyerMajorantsForceCriticality` | invariant nonnegative majorants of the original mixed trace exist iff RH; two point sources give evaluation control, and centered flow preserves the literal mixed sharp product |
| `CriticalMeyerTraceDegree` | the full critical-value trace is a positive descended linear degree with exact critical-value kernel; its invariant square energy dominates the original mixed trace iff RH and is faithful iff RH plus Xi simplicity |
| `MeyerQuasiInverseRadical` | actual quasi-inversion is equivalent to avoiding value −1 at every Xi point; universal product quasi-invertibility is exactly the ordinary trace radical, and this radical vanishes iff Xi zeros are simple |
