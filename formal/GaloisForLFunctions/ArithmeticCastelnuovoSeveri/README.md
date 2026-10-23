# Arithmetic Castelnuovo–Severi Theory (`GaloisForLFunctions.ArithmeticCastelnuovoSeveri`)

**One question.** Weil proved the Riemann hypothesis for curves over finite fields by reading the
zeta function as an intersection theory on the surface `C × C` and the positivity of its
explicit formula as the Hodge index theorem of that surface. Which ingredients of that proof exist
for `ℤ`, which are provably absent, and what exactly would a proof of the missing ones have to
produce?

Arithmetic Castelnuovo–Severi theory (ACS) is the intersection theory of the **scaling surface**
of `ℤ`. Its cycles are the pole plane `⟨H, V⟩` (the directions `e^{∓u/2}`, met by a test in its
transform at `± i/2`) together with the Weil tests; its pairing is the local side of the explicit
formula; its Castelnuovo–Severi defect is Weil's form; its Hodge index theorem is the Riemann
hypothesis. These identities and equivalences are theorems (`scalingSurface`,
`scalingSurface_hodgeIndex_iff`); the scaling surface is a vector space with a pairing, not a
constructed arithmetic scheme with divisors and sections. The programme's object is the gap between this surface and the
surface `C × C` of a curve, measured ingredient by ingredient, calibrated over `𝔽_q`, with every
statement unconditional.

The local pairing and its archimedean diagonal term are explicit. The missing input is an
independent reason for their Hodge index property. Fake curve data show that the specified
Frobenius-span identities, integral point counts and functional equation do not force that sign.
Weil's geometric proof supplies additional information through effective divisors on the ambient
surface. ACS asks what arithmetic structure could play that role; the counterexamples do not rule
out every analytic proof or prove that all possible constructions must enlarge the cycle space.

**The open core, stated plainly.** The Hodge index theorem of the scaling surface is
RH-equivalent (`scalingSurface_hodgeIndex_iff`, `riemannHypothesis_iff_one_positive_square`,
`riemannHypothesis_iff_exists_effectivity`), and **no independent arithmetic effectivity theory
supplies it**. These equivalences are reformulations, not proofs: the positive cone, which is
defined from local data alone (prime comb, archimedean collar, pole), satisfies the Riemann–Roch
axiom by construction, and its ample axiom *is* RH. Any effectivity with the Riemann–Roch axiom and
nonnegative degrees contains the open positive cone (`openPositiveCone_subset_of_effectivity`), so
a proposed effectivity cannot avoid those positive-square classes merely by choosing a smaller set. What Weil has and `ℤ` lacks is the mechanism that
proves ampleness independently: an effective divisor is the zero set of a section, so its degree is
nonnegative, and vanishing ample degree forces numerical triviality. The programme's results locate this gap exactly; they do not close it.

---

## Place in the research

ACS gives the critical Weil form an intersection-theoretic language: cycles, a hyperbolic pole
plane, primitive classes, defects and inertia. The purpose is to distinguish the numerical data of
an intersection pairing from a mechanism that forces its signature. Finite-field curve data are
both the calibration and the source of explicit counterexamples to insufficient axioms.

| Programme | Connection |
|---|---|
| [Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md) | Supplies the full Weil–Markov–pole form whose positivity becomes the Hodge index property. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Supplies adversarial models; ACS's fake curves separate finite span data from unitarity. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Distinguishes exact finite identities from critical-norm estimates and preserves successor boundaries. |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Carries the additive and valuation structure beyond the prime incidence graph: consecutive integers have no prime Hecke intersection for `k ≥ 2`. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) | Reads the same sign through ground energies; ACS counts negative directions through the intersection signature. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Relates aperture and zero width. Its visibility questions are distinct from ACS's unrestricted finite-configuration index formula. |
| [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | Ratio atoms give the Hecke incidence matrix; crossing product atoms belong to its reflected geometry. The Kronecker law computes the prime matrix on resonators. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Seeks quantitative transport of positivity; a geometric reformulation still needs a mechanism that supplies the bound. |
| [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | Studies which cycles a bounded reading can detect; the finite-field window law supplies a calibrated hiding example. |
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | Identifies the comb's mean-field translation and resolvent, explaining why a squared comb majorant is larger than the signed pairing. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Retains the Möbius source and its residue kernel when passing from arithmetic incidence to quadratic forms. |

Read polar decomposition and adjunction first, then the Frobenius-span, fake-curve and contact
laws. The scaling surface and signature law transfer this language to `ζ`; effectivity specifies
the missing geometric input. The finite and tempered Pontryagin laws and the Cartesian
prime-incidence law are
concrete tools that can be used without assuming RH. `RHTower` supplies the explicit formula,
Weil criterion, zero-count input and matrix inertia calculus.

---

## 1. Why: motivation

**Weil's proof has five ingredients.** On `C × C` over `𝔽_q`: (i) an intersection pairing; (ii) the
fibre classes `H, V` with `H² = V² = 0`, `H·V = 1`, spanning a hyperbolic plane of signature `(1,1)`; (iii) the
Frobenius graph `Γ` with `Γ·Δ = #C(𝔽_q)` (Lefschetz); (iv) its exact self-intersection
`Γ² = q(2 − 2g)` (adjunction); (v) a dimension count — Riemann–Roch for divisors of the surface —
which forces the Hodge index theorem: the pairing is negative semidefinite on primitive classes
(negative definite after the appropriate numerical quotient). The Hodge index
theorem gives the Castelnuovo–Severi inequality `D² ≤ 2(D·H)(D·V)`, and on `D = mΓ + nΔ` that is the
bound `|N − q − 1| ≤ 2g√q`.

**The arithmetic counterpart is an exact pairing.** The pole evaluations form a hyperbolic
plane; subtracting the local prime–archimedean pairing produces Weil's form. This identifies the
sign problem precisely but does not solve it. Countermodels exclude particular proposed inputs,
such as finite windows or the stated span identities; they do not exclude all estimates.

**The geometric opening is effectivity.** A section theory could force the sign through a
Riemann–Roch argument and positivity of ample degree. The abstract effectivity theorem specifies
these obligations. Its converse constructs a cone from the desired sign, so existence of that
cone is an equivalent criterion, not an independent producer.

**Calibration separates the ingredients.** Pairing, fibres, Lefschetz and adjunction are available
on the formal Frobenius span. Hodge index on that span is equivalent to unitarity for every curve
datum, including fake data. The missing dimension-count mechanism is therefore not a consequence
of those identities. Over `ℚ`, no nonzero compact test can have its transform vanish at almost all
simple critical zeros; this rules out copying the finite-field span radical as a section model.
It motivates approximate sections or a different arithmetic object, without proving that every
possible section theory must use near-radicals.

---

## 2. What: objects and language

### 2.1 The dictionary

| Weil's proof over `𝔽_q` | The scaling surface of `ℤ` | Lean |
|---|---|---|
| surface `C × C`, pairing | cycles `aH + bV + f`, pairing from the explicit formula | `scalingSurface`, `scalingPair` |
| fibres `H, V`: `H² = V² = 0`, `H·V = 1` | pole plane `e^{∓u/2}`; `f·H = ∫ f e^{−u/2}`, `f·V = ∫ f e^{u/2}` | `PolarSurface`, `poleB`, `poleA` |
| defect `2(D·H)(D·V) − D²` | Weil's form `W(f, f)` | `scalingSurface_defect_self` |
| Hodge index on `⟨H, V⟩^⊥` | Weil positivity = RH | `scalingSurface_hodgeIndex_iff` |
| Frobenius graphs `Γ_k` | scaling (Hecke) cycles: lattice tests `Σ c_a g(· − log a)` | `heckeIncidence` |
| Lefschetz `Γ_k·Γ_l = q^{min} N_{\|k−l\|}` | prime side `Λ(n) n^{−1/2}` at `log n` | `graphPair`, `localGram_apply` |
| adjunction `Γ_k² = q^k(2 − 2g)` | archimedean lag-zero term (Gamma factor) | `graphPair_self`, `localGram_apply` |
| genus `2g = Σ_i β_i^0` | zero count (infinite) | `trace_zero`, `eq_zero_of_paperFT_vanish` |
| Riemann–Roch ⇒ Hodge index | effectivity with RR and ample axioms | `exists_effectivity_iff_hodgeIndex` |
| positive index `1` | one positive square on every family | `riemannHypothesis_iff_one_positive_square` |

### 2.2 Objects

| Object | Meaning | Lean |
|---|---|---|
| Polar surface | real cycles with symmetric pairing, isotropic `H, V`, `H·V = 1` | `PolarSurface` |
| Defect | `δ(x, y) = (x·H)(y·V) + (x·V)(y·H) − x·y` | `PolarSurface.defect` |
| Primitive part | `x° = x − (x·V)H − (x·H)V` | `PolarSurface.prim` |
| Ample class | `H + V`, `(H + V)² = 2` | `PolarSurface.ample` |
| Hodge index (four forms) | primitive, Castelnuovo–Severi, defect, ample | `HodgeIndex`, `CastelnuovoSeveri`, `AmpleHodgeIndex` |
| Weil configuration | `(q, g, N, s)`: numbers of `Γ, Δ` on a Hodge surface | `WeilRealizable` |
| Curve datum | `q > 1`, normalized eigenvalues `β`, closed under conjugation and `β ↦ β⁻¹` | `CurveDatum` |
| Lefschetz number | `N_j = q^j + 1 − q^{j/2} Σ β_i^j`, `N_0 = 2 − 2g` | `CurveDatum.pointCount` |
| Span defect, Toeplitz form | defect of `Σ d_k Γ_k`; `Σ e_k e_l Re Σ_i β_i^{\|k−l\|}` | `spanDefect`, `toeplitz` |
| Golden datum | fake elliptic curve over `𝔽₅`, `β = φ, φ⁻¹` | `goldenDatum` |
| Hiding datum | the pair `2, 1/2` with `2N` roots of unity | `hidingDatum` |
| Spectrum, reduced char. polynomial | distinct `β`; `Π (X − β)` | `spectrum`, `reducedCharPoly` |
| Effectivity, axioms | a set of cycles; Riemann–Roch and ample axioms | `RiemannRochAxiom`, `AmpleAxiom` |
| Real tests, scaling cycles | `C²` compactly supported real tests; `ℝ × ℝ × tests` | `realTests`, `ScalingCycle` |
| Weil and local pairing | `Re W(f, g)`; `B(f)A(g) + A(f)B(g) − Re W(f, g)` | `weilPair`, `localPair` |
| Intersection Gram | Gram of `H, V, f₁…f_n`: `[[J, B], [Bᴴ, BᴴJB − W]]` | `intersectionGram`, `polePlane`, `poleRow` |
| Hecke incidence, tower form | `ratioIncidence a b + ratioIncidence b a` (AIP's ratio atoms); `Σ x_i x_{i'} τ_p(\|i − i'\|)` | `heckeIncidence`, `ratioIncidence`, `primeAtom`, `towerForm`, `towerWeight` |
| Cross-prime aggregate | `Σ_{p ≠ q ≤ N} w_p w_q A(log(q/p))`, `w_p = log p/√p` | `crossAggregate`, `combWeight`, `autoCorrelation` |
| Wide odd test | odd smooth plateau test of aperture `3W + 2` | `wideOddTest` |

### 2.3 Words

* **Cycle, degree, aperture.** A cycle is a pole-plane class plus a test. Its **ample degree** is
  its pairing with `H + V`; the two fibre degrees are its pairings with `H` and `V`.
  **Aperture** is a support bound for the test, analogous to the length of a Frobenius window.
  Aperture is not ample degree; effectivity axioms concern the latter.
* **Primitive, defect.** The primitive part is the projection off the pole plane; the defect of a
  cycle is minus the square of its primitive part. Positivity of the defect is Hodge index.
* **Span.** The span of the Frobenius graphs (over `ℚ`: of the Hecke cycles); its intersection
  numbers are Lefschetz numbers and the adjunction term.
* **Unitary, fake.** A curve datum is unitary when `|β_i| = 1` (RH for the datum); a fake datum has
  the span data of a curve (point counts, functional equation) but is not unitary.
* **Genus, contact window.** The lag-zero trace is `2g`, and the lag-zero Lefschetz number is
  `2−2g`. The first degenerate window has length `s+1`, where `s` counts distinct normalized
  eigenvalues; this need not equal `2g+1` when eigenvalues repeat.
* **Effectivity.** A set of cycles playing the role of effective divisors; it must satisfy the
  Riemann–Roch axiom (positive square ⇒ effective up to sign) and the ample axiom (effective and
  orthogonal to `H + V` ⇒ numerically trivial).
* **Resonator.** A `{p, q}`-smooth box `{p^i q^j}`, the support of the bi-lattice train.
* **Mean field.** The part of a prime-sum quantity carried by the mean `Σ_p w_p ≍ √N` of the comb —
  the pole read at PNT level.

### 2.4 Source and selectivity

* **The source is fixed.** The scaling surface uses `Λ` and a pole of weight one. For a general
  weight `λ`, having exactly one positive square on every finite test family is equivalent to
  `RH ∧ (∀ n ≥ 2, λ(n)=Λ(n))` (`one_positive_square_iff_vonMangoldt`). Choosing the actual
  source does not assume or prove its Hodge index property.
* **Span identities are insufficient.** Fake data satisfy the specified algebraic symmetries and
  point-count properties but fail Hodge index. A new argument must use an additional constraint
  that those data violate; it need not be described as a change of type or an enlarged space.
* **Signed tests and effective cycles are different.** The pole quadrant with nonnegative tests
  fails the Riemann–Roch axiom (`posTestCone_not_riemannRoch`). The quadratic positive cone used
  in the converse effectivity theorem is a different set.

---

## 3. How: the foundational theorems

### 3.1 The polar surface (`PolarSurfaceHodgeIndex`)

1. **Orthogonal decomposition.** `x·y = (x·H)(y·V) + (x·V)(y·H) + x°·y°`
   (`pair_eq_polar_add_prim`); the defect only sees the primitive part (`defect_prim`,
   `pair_prim_prim`: `x°·y° = −δ(x, y)`).
2. **Four forms of Hodge index.** Negative semidefinite on primitives ⟺ `x² ≤ 2(x·H)(x·V)` ⟺
   `δ(x, x) ≥ 0` ⟺ negative semidefinite on `(H + V)^⊥` (`hodgeIndex_tfae`).
3. **Weil's step.** Under Hodge index the defect obeys Cauchy–Schwarz, `δ(x, y)² ≤ δ(x, x)δ(y, y)`
   (`defect_sq_le_of_hodgeIndex`) — the only inequality of Weil's proof.
4. **One positive square.** Hodge index ⟺ no plane of cycles is positive definite
   (`hodgeIndex_iff_no_positive_plane`).

### 3.2 The adjunction threshold law (`AdjunctionThresholdLaw`)

5. **Classification.** A configuration `Γ·H = 1`, `Γ·V = q`, `Δ·H = Δ·V = 1`, `Δ² = 2 − 2g`,
   `Γ² = s`, `Γ·Δ = N` is realizable on a Hodge polar surface iff its defect Gram
   `[[2q − s, q + 1 − N], [q + 1 − N, 2g]]` is positive semidefinite (`realizable_iff`; the model is
   `ℝ⁴` with the hyperbolic plane and minus the defect Gram, `modelSurface`).
6. **Hasse–Weil from adjunction.** With `s = q(2 − 2g)`: realizable iff `g ≥ 0` and
   `(q + 1 − N)² ≤ 4g²q` (`realizable_adjunction_iff`); in abstract form `abs_le_of_hodgeIndex`.
7. **Adjunction carries the whole bound.** For `g > 0` every `N` is realizable for some `s`
   (`realizable_of_free_selfIntersection`): the Hodge index theorem bounds nothing without `Γ²`.
8. **Only the lower adjunction bound is used.** `Γ² ≥ q(2 − 2g) − ε` gives
   `(q + 1 − N)² ≤ 2g(2gq + ε)` (`sq_le_of_realizable_of_selfIntersection_ge`): Weil needs an upper
   bound on the self-defect `δ(Γ) = 2q − Γ²`, not its exact value.
9. **Genus zero is rigid.** `g = 0` forces `N = q + 1` (`realizable_genusZero_iff`).

### 3.3 The Frobenius span (`FrobeniusSpanCalibration`, `FrobeniusSpanHodgeIndexIsRH`)

10. **Lefschetz and adjunction are one formula.** `Γ_k·Γ_l = q^{min(k,l)} N_{|k−l|}` with
    `N_j = q^j + 1 − q^{j/2} Σ_i β_i^j`; at lag `0` the Lefschetz number is the Euler characteristic
    `2 − 2g`, which is adjunction (`graphPair_self`, `graphPair_zero`, `pointCount_zero`).
11. **The defect of the span is Weil's form.** `2(D·H)(D·V) − D² = Σ_{k,l} e_k e_l Re Σ_i β_i^{|k−l|}`,
    `e_k = q^{k/2} d_k` (`spanDefect_eq_toeplitz`); for unitary data it is `Σ_i |Σ_k e_k β_i^k|²`
    (`toeplitz_eq_sum_normSq`). Genus zero makes it vanish identically
    (`spanDefect_eq_zero_of_genusZero`): the `𝔽_q[T]` calibration.
12. **Hodge index on the span is RH for the datum** (`hodgeIndexOnSpan_iff_unitary`): the `2 × 2`
    minors at lags `0, j` bound `|Σ β_i^j| ≤ 2g` (`norm_powerSum_le`), power-sum elimination forces
    `|β_i| ≤ 1`, and the functional equation forces equality.

### 3.4 Fake curves and the window law (`FakeCurvesAndTheWindowLaw`, `WittIntegralityIsNotPurity`)

13. **A fake elliptic curve over `𝔽₅`.** `β = (φ, φ⁻¹)`: point counts `N_j = 5^j + 1 − L_j` are
    integers with `N_j ≥ 1` (`goldenDatum_pointCount_eq`, `one_le_goldenDatum_pointCount`), the
    zeta function `(1 − 5u + 5u²)/((1 − u)(1 − 5u))` is rational with functional equation, and the
    class `Δ − Γ₁/√5` has defect `4 − 2√5 < 0` (`goldenDatum_spanDefect_neg`). This is the
    Beurling wall over `𝔽_q`.
14. **Visibility needs genus `≳ r^n`.** With a real off-circle pair `r, r⁻¹` and all other
    eigenvalues unitary, Hodge index in degrees `< n` forces `r^{n−1} + r^{1−n} + 2 ≤ 4g`
    (`two_mul_genus_ge_of_window`).
15. **Hiding.** For every `n` a datum with `|β| = 2` is Hodge on every span class of degree `< n`
    (`exists_hidden_on_window`, with `hidingDatum`): the finite-window wall over `𝔽_q`.
15′. **Witt integrality is not purity** (`WittIntegralityIsNotPurity`). The zeta series
    `Z = P/((1 − X)(1 − qX))`, `P = Π(1 − α_i X)`, `α_i = √q β_i`, has the Lefschetz numbers as
    ghost components: `X Z' = Z · Σ_{j≥1} N_j X^j` (`zetaSeries_hasGhost`), and a series with
    constant term `1` is determined by its ghost components (`eq_of_hasGhost`), so
    `Z = exp(Σ N_j X^j/j)` and data with the same point counts have the same zeta series
    (`zetaSeries_eq_of_pointCount`). The ghost map is additive on products (`hasGhost_mul`): the
    pole plane splits off as `Z_{ℙ¹}` with ghost components `1 + q^j`, and `P` is the `H¹` class
    with ghost components `−Σ α_i^j`. The golden datum has `P = 1 − 5X + 5X²` and an integral
    zeta series in `1 + Xℤ⟦X⟧`, integral point counts and the functional equation, and is not
    pure (`witt_integral_not_pure`); the pure datum `q = 2, β = (1, 1)` has `N₁ = 3 − 2√2 ∉ ℤ`
    (`pureDatum_pointCount_one_not_int`). Integrality and purity are independent: the λ-ring
    structure does not carry the positivity, which enters only through the Hodge index (item 12).
15″. **The golden fake curve is a rank-one Beurling system** (`TheGoldenCurveIsABeurlingSystem`).
    Its point counts are the ghost components of nonnegative integral prime counts,
    `N_k = Σ_{d∣k} d π_d`, `π_d ∈ ℕ` (`goldenDatum_beurling`): `N_k = 1 + 5^k − tr(B^k)` with
    `B = [[3, 1], [1, 2]]`, the edge shift of `B` is a subshift of the full shift on five letters,
    and `π_d` counts (besides one extra fixed point) the primitive orbits of length `d` of the full
    shift outside the subshift. The tools are general: periodic points split by minimal period
    (`card_perSeqs_eq_sum`), primitive orbits are free (`dvd_card_of_shift_invariant`), any
    inclusion of subshifts gives nonnegative integral prime counts (`exists_primeCounts`), and the
    transfer matrix counts cyclic words (`card_perSeqs_eq_trace`). So a Beurling system of Kronecker
    rank one can have positive integral prime counts, an integral rational zeta function with the
    pole plane split off and the functional equation, and violate purity and the Hodge index
    (`goldenDatum_beurling_not_pure`): the selectivity against Beurling systems must come from the
    Bézout structure of the surface, as the review's typing requires.

### 3.5 The contact law and the Pontryagin law over `𝔽_q` (`SpanContactLaw`,
`TheFrobeniusSpanDefectCountsTheOuterEigenvalues`)

16. For unitary data the defect on the window of `n` Frobenius graphs is positive definite iff
    `n ≤ s`, the number of distinct eigenvalues (`toeplitz_pos_on_window_iff`); above it the radical
    contains the reduced characteristic polynomial, which is real (`exists_radical_of_lt`,
    `map_conj_reducedCharPoly`). The sections of the span are its multiples.
16′. **The Pontryagin law over `𝔽_q`** (`TheFrobeniusSpanDefectCountsTheOuterEigenvalues`). For
    every curve datum, unitary or not, the complexified defect Gram of the window
    `Γ₀, …, Γ_{n−1}` (`spanGram`; on real classes the Castelnuovo–Severi defect,
    `hermQuad_spanGram_ofReal`) is the reflected evaluation form
    `x*Gy = Σ_i conj(E_x(β_i)) E_y(1/β̄_i)`, `E_x = Σ_{k<n} x_k X^k` (`spanGram_sesq`): the
    zero-configuration form of item 20‴ with `ρ ↦ 1 − ρ̄` replaced by `β ↦ 1/β̄`. Its negative
    index is at most `#{distinct β : |β| > 1}` on every window, nondecreasing in the window, and
    equal to it once `n ≥ #{β}`, in particular at `n = 2g` (`pontryagin_law_curve`,
    `negIndex_spanGram_mono`); attainment interpolates `1` at `z`, `−1` at `1/z̄` and `0` on the
    rest of the spectrum. Hence Hodge index on the window `2g` is RH for the datum
    (`unitary_iff_negIndex_spanGram_eq_zero`), and the golden fake curve has Hodge defect exactly
    `1` from window `2` on (`goldenDatum_negIndex_spanGram`). As over `ℚ` the defect is blind to
    depth and multiplicity; unlike over `ℚ` its aperture is explicit: every off-circle eigenvalue,
    clustered or not, is visible on the window `#{β} ≤ 2g`, and the hiding datum (item 15) shows
    that shorter windows can miss it. Over `ℚ` the genus is infinite and no window holds the
    spectrum; the degree filtration (item 20⁗) replaces the window.

### 3.6 The scaling surface, the signature law and the Pontryagin law
(`TheScalingSurface`, `ArithmeticHodgeIndexSignatureLaw`, `FiniteConfigurationPontryaginLaw`,
`TemperedConfigurationPontryaginLaw`, `TheHodgeDefectCountsTheRightZeros`,
`TheDegreeFiltrationOfTheHodgeDefect`, `TheReflectionSectorsOfTheHodgeDefect`)

17. **The scaling surface is a polar surface whose defect is Weil's form**
    (`scalingSurface`, `scalingSurface_defect_self`), so **its Hodge index theorem is RH**
    (`scalingSurface_hodgeIndex_iff`). On two tests the defect pairing is Weil's pairing
    (`scalingSurface_defect_tests`), so Weil's discriminant step is item 3 on the scaling surface.
18. **The local intersection is prime comb minus archimedean collar** (`localGram_apply`).
19. **Signature law.** `#positive squares(H, V, f₁…f_n) = 1 + #negative squares(W(f_i, f_j))`
    and dually (`posIndex_intersectionGram`, `negIndex_intersectionGram`), by Haynsworth inertia.
    **RH ⟺ one positive square on every finite family** (`riemannHypothesis_iff_one_positive_square`);
    **one positive square for a general weight is equivalent to RH together with
    `λ(n)=Λ(n)` for `n ≥ 2`** (`one_positive_square_iff_vonMangoldt`).
20. **Pontryagin bound.** `#negative squares of W ≤ #{ρ : Re ρ > ½}` on every finite family, in
    `ℕ∞`, unconditionally (`negIndex_weilGram_le_offLineCount`); hence the intersection form has at
    most `1 + #{Re ρ > ½}` positive squares (`posIndex_intersectionGram_le`). The abstract lemma:
    a form nonnegative on the kernel of `P` functionals has at most `P` negative squares
    (`negIndex_le_card_of_nonneg_on_ker`).
20′. **Exact finite-configuration law** (`FiniteConfigurationPontryaginLaw`). For a finite
    reflection-symmetric configuration `Z`, the largest negative index over finite compact-test
    families is exactly the number of **distinct** zeros right of the line
    (`pontryagin_law_finite`). `exists_test_interpolating` prescribes transform values at finitely
    many distinct points using translates of a short bump and a Vandermonde matrix. Set the values
    to `1` at a chosen right zero, `−1` at its reflection and `0` at all other zeros: the resulting
    Gram matrix is diagonal with entries `−2m_ρ` (`exists_zeroGram_negIndex_eq`). The theorem has
    no prescribed aperture or uniform conditioning estimate; the infinite on-line tail is handled
    by item 20″.
20″. **Exact tempered law** (`TemperedConfigurationPontryaginLaw`). On a tempered configuration
    (`Σ m_ρ/(1 + |γ_ρ|²) < ∞`; the zeros of `ζ` are one) the Weil form converges absolutely on
    compact `C²` tests (`summable_Wsummand`), has at most `#{Re ρ > ½}` negative squares in `ℕ∞`
    (`negIndex_zeroGram_le_of_tempered`), and has exactly that many when they are finitely many
    (`pontryagin_law_of_tempered`). Mechanism: **dual tests** `b_ρ` with
    `h_{b_ρ}(γ_σ) = h_{b_ρ}(γ̄_σ) = δ_{ρσ}` (`exists_dual_tests`) and **translated pairs**
    `b_ρ, ω_ρ b_ρ(· − L)` with phase `ω_ρ = −e^{−i Im ρ · L}`. The pair of `ρ` contributes
    `2m_ρ|y_ρ|²(1 − e^{δ_ρ L})(1 − e^{−δ_ρ L})`, `δ_ρ = Re ρ − ½`; on the line the phases have
    modulus one, so the on-line zeros contribute at most `4|y|²A` with `A` independent of `L`
    (`re_Wsummand_pairComb_le_of_onLine`); `δ_ρ L ≥ 4A + 2` makes the form `≤ −|y|²`
    (`re_W_pairComb_le`). For `ζ` the zero-side Gram is the Weil Gram of the explicit formula
    (`weilGram_eq_zeroGram`). This construction is explicit (two tests per zero, an explicit
    aperture) but needs the right zeros to be finitely many; item 20‴ removes that restriction.
20‴. **The exact law, unconditionally** (`TheHodgeDefectCountsTheRightZeros`). For every tempered
    configuration, Weil's form has `n` negative squares on some family of `n` tests iff there are
    at least `n` zeros right of the line (`pontryagin_law`): the largest negative index is
    `#{Re ρ > ½}` in `ℕ∞`. Mechanism: the **zero-side coordinates** `X_τ(f) = √m_τ h_f(γ_τ)` map
    tests into `ℓ²(Z)` (`zeroMap`), and `W(f, g) = ⟨R X(g), X(f)⟩` with `R` the reflection
    `τ ↦ 1 − τ̄` (`W_eq_inner`), a Krein form with one hyperbolic plane per pair. The range is
    **dense** (`orthogonal_range_zeroMap`): a vector orthogonal to every probe `φ(u − v)e^{isu}`
    produces an exponential sum `Σ q_τ e^{(τ̄ − ½)v} ≡ 0`, whose coefficients vanish
    (`eq_zero_of_tsum_exp_eq_zero`: the rightmost exponent at each height would be a pole of the
    Laplace transform of `0`). Approximating `e_ρ − e_{1−ρ̄}` gives a Gram matrix within `5ε` of
    `−2·I` (`exists_zeroGram_negIndex_ge`). **For `ζ`:** the intersection form of the scaling
    surface has `1 + n` positive squares on the pole plane and some `n` tests iff `ζ` has at least
    `n` zeros with `Re ρ > ½` (`zeta_hodgeDefect_iff`); `ζ` has infinitely many zeros off the line
    iff the Hodge defect is unbounded (`zeta_rightZeros_infinite_iff`). The Hodge defect of the
    scaling surface *is* the number of zeros right of the line. **Kronecker rank one:** a
    configuration invariant under `ρ ↦ ρ + iP` (a lattice system) has Hodge defect `0` or `∞`
    (`periodic_pontryagin_dichotomy`); finitely many off-line zeros, possible a priori for `ζ`, are
    impossible in rank one. More generally every **vertically recurrent** configuration (each zero
    recurs, up to `ε` in its real part, at unbounded heights; this is how the zero sets of almost
    periodic Dirichlet series of finite Kronecker rank behave) has Hodge defect `0` or `∞`
    (`recurrent_pontryagin_dichotomy`, `TheKroneckerRankDichotomy`).
20⁗. **The degree filtration** (`TheDegreeFiltrationOfTheHodgeDefect`, `TheReflectionSectorsOfTheHodgeDefect`). The Hodge defect at degree
    `a`, `hodgeDefectAt Z a` (negative squares on tests supported in `[−a, a]`), is nondecreasing
    (`hodgeDefectAt_mono`), bounded by `#{Re ρ > ½}` (`hodgeDefectAt_le`) and exhausts it:
    `⨆_a hodgeDefectAt Z a = #{Re ρ > ½}` (`iSup_hodgeDefectAt`). For `ζ` it vanishes through
    degree `3/10` (`zeta_hodgeDefectAt_eq_zero`). The quantitative horizon of the `ε`-negative
    index at level `a` (off-line pairs below height `H` with `log H = O(e^a + log(1/ε))`, and a
    matching count for isolated visible pairs) is `RHTower.zeta_weil_inertia_law`.
20⁵. **The reflection sectors** (`TheReflectionSectorsOfTheHodgeDefect`). On a configuration
    symmetric under `ρ ↦ 1 − ρ` the reflection `u ↦ −u` of tests splits the Weil form into an even
    and an odd sector, and the Pontryagin law splits with it (`sector_pontryagin_law`): the even
    defect is `#{Re ρ > ½, Im ρ > 0}`, the odd defect `#{Re ρ > ½, Im ρ ≥ 0}`. A real zero right
    of the line has pair term `+m|h(γ)|²` on even tests and is invisible to them
    (`re_Wsummand_nonneg_of_sector`); the involution `τ ↦ 1 − τ` of the coordinates sends the
    negative vector of `ρ` to minus that of `ρ̄` (`fesVec_negVec`). For `ζ`, which has no real
    zeros, each sector carries exactly half the Hodge defect (`zeta_sector_hodgeDefect_iff`): every
    conjugate pair of zeros right of the line gives one even and one odd negative square. The odd
    sector alone detects every off-line zero (the review's selectivity test for the
    reflection-odd sector); the even sector carries in addition the ample pole direction `H + V`.

### 3.7 Hodge index from effectivity (`HodgeIndexFromEffectivity`, `TheScalingSurface`)

21. **Hodge index ⟺ an effectivity with the Riemann–Roch and ample axioms**
    (`exists_effectivity_iff_hodgeIndex`); the positive cone is the canonical witness
    (`positiveCone_axioms`). For `ℤ`: **RH ⟺ such an effectivity exists on the scaling surface**
    (`riemannHypothesis_iff_exists_effectivity`).
22. **Positivity is not effectivity.** The pole quadrant with nonnegative tests fails the
    Riemann–Roch axiom unconditionally (`posTestCone_not_riemannRoch`, via
    `not_riemannRoch_of_perturbation`). More generally the product of the pole quadrant with any
    scaling-closed set `P` of tests that misses a single test fails it
    (`productCone_not_riemannRoch`): no positivity notion on tests (pointwise, of the transform,
    of positive type) defines an effectivity. This is the no-go half of the success criterion
    (§7) for the class of product cones.
22′. **No cone avoids the positive cone.** An effectivity with the Riemann–Roch axiom and
    nonnegative degrees contains every class of positive square and positive degree
    (`openPositiveCone_subset_of_effectivity`); its ample axiom therefore contains the Hodge index
    constraint on the resulting cycle theory.
22″. **Classification of effectivities** (`effectivity_iff`). Under the Hodge index a set `E` of
    nonnegative degree satisfies both axioms iff
    `{x² > 0, x·(H+V) > 0} ⊆ E ⊆ {x·(H+V) > 0} ∪ {numerically trivial}`. A section theory is free
    only in which classes of nonpositive square and positive degree it declares effective (as for
    curves of negative self-intersection on a surface); everything else is forced. Items 21–22″
    specify the missing section count completely; none of them supplies it.

### 3.8 The infinite genus law (`InfiniteGenusLaw`)

23. **No exact transform-annihilating test at any aperture.** A test whose transform vanishes at all but finitely many simple
    critical zeros is zero (`eq_zero_of_paperFT_vanish`), and **RH ⟺ Weil's form is positive
    definite** on nonzero tests (`riemannHypothesis_iff_weil_positive_definite`). The contact window
    of the unitary finite-field span has no exact counterpart in this test class. This is strict
    positivity of each nonzero test under RH, not a uniform positive lower bound for every
    normalized test. Near-radical families remain possible.

### 3.9 The adjunction formula on resonators (`ResonatorKroneckerLaw`, `HeckeIncidenceCartesianLaw`,
`TheResonatorRemainderIsNegative`)

24. **Kronecker law.** On a `{p, q}`-box the Hecke incidence is
    `[j = j'] τ_p(|i − i'|) + [i = i'] τ_q(|j − j'|)` (`heckeIncidence_box`), so the prime
    self-intersection of a resonator is the Kronecker sum of two tower forms
    (`heckeForm_box_eq`): **no cross-prime prime coupling**. In general (**Cartesian law**) two
    Hecke cycles meet through the primes only when their exponent vectors differ in exactly one
    coordinate `p`, with weight `τ_p(|v_p(a) − v_p(b)|)` (`heckeIncidence_eq_towerWeight`,
    `heckeIncidence_eq_zero`): the prime part of the surface is the Cartesian product over all
    primes of weighted tower graphs — the Euler product on the surface. Consecutive Hecke cycles
    `Γ_k, Γ_{k+1}` (`k ≥ 2`) have no prime intersection (`heckeIncidence_succ`).
25. **The envelopes add.** `|towerForm| ≤ (2 log p/(√p − 1)) Σ x²` (`abs_towerForm_le`), hence
    `|heckeForm| ≤ (E_p + E_q) Σ c²` (`abs_heckeForm_box_le`); the resonant train attains it
    (`towerForm_one`, `heckeForm_box_one`).
25′. **The adjunction remainder is negative definite on resonators**
    (`TheResonatorRemainderIsNegative`). On a `{p, q}`-resonator with narrow bumps the cross-prime
    aggregate is `2 w_p w_q X(c)`, `X(c) = Σ c(i+1, j) c(i, j+1)` the anti-diagonal lag count, and
    the review's remainder `R(c) = 2 w_p w_q X(c) − (E_p + E_q) Σ c²` satisfies
    `R(c) ≤ −(E_p + E_q − w_p² − w_q²) Σ c²` (`resonatorRemainder_le`) with `w_r² < E_r`
    (`resonatorWeight_sq_lt_eulerEnvelope`): `R` is negative definite (`resonatorRemainder_neg`).
    This decides the review's first research topic: the cross term never pays for the envelopes on
    resonators, so Weil positivity there comes from the archimedean collar and the pole.

### 3.10 The mean-field law and the adjunction conjecture (`TheAdjunctionConjectureMeanField`)

26. **The cross-prime aggregate is a mean field.** Near pairs carry `(S² − Q)/4` and far pairs
    `|log(q/p)| > T` cost at most `2e^{−T/2}(1 + log N)² θ(N)` (`crossAggregate_ge`,
    `farPairs_le`); with Chebyshev in explicit form (`theta_ge_half_log_two`) the aggregate of a wide
    odd test is `≥ (log² 2/16) N A_F(0)` up to lower order.
27. **The quantitative clause of the review's adjunction conjecture is false**
    (`not_exists_polynomial_adjunction_bound`): no `C(1 + r)^k A_F(0) Σ w_p²` plus the full Euler
    envelope budget bounds the aggregate of all odd `C²` tests of aperture `r`. The exponential
    part is `S² ≍ N`, the pole read through the comb; Cauchy–Schwarz loses the linear prime–pole
    cancellation that the ledger keeps. The survivor is item 24.

---

## 4. How to use the geometric dictionary

1. **Adjunction.** The exact, zero-free formula exists and is classical: the lag-zero Lefschetz
   number of the span is the Euler characteristic (item 10); over `ℚ` it is the archimedean term of
   the explicit formula, part of the local intersection (item 18). Genus ↔ zero density; `q` ↔ the
   scaling `e^{log n}`; degree ↔ aperture. The comb self-pairing of the review is not this number:
   on resonators the prime self-intersection has no cross-prime terms (item 24), and the review's
   bound on the aggregate fails (item 27).
2. **Section count.** Its exact job is to supply an effectivity with the Riemann–Roch and ample
   axioms (item 21); that is equivalent to RH, and positivity of tests does not supply it (item 22).
   Over `𝔽_q` the span radical consists of multiples of the reduced characteristic polynomial
   (item 16); this exact annihilation model fails for compact tests over `ℚ` (item 23).
   A near-radical count is one candidate replacement, not a classification of all section theories.
3. **Integral Frobenius.** Integrality of span data is not positivity: the golden datum has integral
   point counts and a rational zeta function and violates the index theorem (item 13).
4. **Tail and primitive part.** On the scaling surface a cycle becomes primitive by
   projection off the pole plane. The local pairing retains the full prime distribution, although
   compact support makes each test see finitely many prime atoms. An individual prime tail is not
   automatically a primitive cycle; its two pole pairings must be checked.
5. **Why the pole pays at PNT level.** The exponential part of every Cauchy–Schwarz shadow of the
   raw comb majorant contains the mean field `S² ≍ N` on the stated wide test families (item 26).
   The pole and prime main term must be paired before squaring. Their identification does not
   bound the residual signed pairing for every test.
6. **Resonators.** The self-pairing on a resonator is exactly the Kronecker sum of the two Euler
   towers (items 24–25), and the review's prime-side remainder is negative definite there (item
   25′); the archimedean and polar terms carry the positivity and still require a sign argument.
7. **Kronecker rank.** Rank-one (lattice) systems are curve data; their span is Hodge iff unitary
   (item 12), fake data exist (item 13), hiding needs genus exponential in the degree (items
   14–15), and their Hodge defect over the scaling surface is `0` or `∞` (item 20‴); the same
   holds for every recurrent configuration, so a finite nonzero defect needs infinite rank. For tests of any Kronecker rank the prime part decouples into one tower per prime
   (item 24, Cartesian law); direct prime edges change only one exponent; archimedean and polar terms supply
   additional coupling. Coefficients and the support box still affect the tower forms.

---

## 5. Traps

| Trap | What is true instead |
|---|---|
| Treating the adjunction formula as the missing ingredient | It is the lag-zero Lefschetz number (Euler characteristic) over `𝔽_q` and the archimedean term over `ℚ`; it is present and exact. The missing ingredient is the Hodge index theorem. |
| Expecting Weil's proof to need `Γ²` exactly | Only `Γ² ≥ q(2 − 2g)` is used (item 8): an upper bound on the self-defect. Without any value of `Γ²` the Hodge index bounds nothing (item 7). |
| Proving Hodge index from span data | On the span Hodge index *is* RH for every datum, and fake data satisfy the listed algebraic and point-count constraints (items 12–13). Weil's index theorem comes from Riemann–Roch on the whole surface. |
| Reading the comb-energy aggregate as an intersection number | On resonators the prime intersection has no cross-prime terms (item 24); the aggregate is a Cauchy–Schwarz shadow of mean-field size `≍ N` (items 26–27). |
| Bounding the aggregate polynomially | False on wide odd tests (item 27); the exponential part is the pole's mean field, the correct target retains the linear prime–pole pairing and estimates its remainder. |
| Taking positive tests as effective cycles | The pole quadrant with nonnegative tests fails the Riemann–Roch axiom (item 22); it is not the quadratic positive cone. |
| Reading `riemannHypothesis_iff_exists_effectivity` as progress on RH | It is a reformulation: the positive cone satisfies the Riemann–Roch axiom by definition and its ample axiom is RH; every Riemann–Roch effectivity with nonnegative ample degrees contains its open positive-degree part (item 22′). Progress means an ampleness proof that does not use the sign of the form. |
| Expecting a radical (sections) over `ℚ` | Infinite genus: no nonzero test is Ξ-divisible on the critical line, and under RH the form is positive definite (item 23). |
| Counting multiplicities in the Pontryagin law | Negative squares are counted by the *distinct* zeros right of the line; a multiple zero contributes one hyperbolic plane, hence one negative square. |
| Expecting finitely many window conditions to see a deep pair | Over `𝔽_q` the hiding genus grows like `r^n` (items 14–15); over `ℚ` the genus is infinite. |
| Signs of the hyperbolic plane | `H·V = 1`, `H² = V² = 0`; the ample class `H + V` has square `2`, the class `H − V` square `−2`; the pole plane alone has one positive and one negative square (`posIndex_polePlane`, `negIndex_polePlane`). |

---

## 6. Open problems and the tools the programme develops

1. **An independent effectivity for `ℤ` — the open core.** The scaling-surface Hodge index is
   RH-equivalent, but no independent arithmetic effectivity theory supplies it. If one exists, it
   lies in the sandwich of item 22″, and its defect from the Hodge index is counted exactly by the
   zeros right of the line (item 20‴). Wanted: a notion of
   *section* of an arithmetic line bundle on the scaling surface, a cone `E` of classes with a
   nonzero section, a proof that `E` has nonnegative degree against `H + V` **from the definition
   of a section** (not from the sign of the form), and a dimension count giving the Riemann–Roch
   axiom. By items 21–22′ this is RH; by item 22 it cannot be the cone of positive tests; by item
   23 they cannot be identified with nonzero compact tests annihilating every zero. Approximate
   sections and a near-radical count (topic 2) are one possible architecture; any alternative must
   explain how its sections imply both axioms.
2. **The near-radical count (Landau–Widom).** Replace `h⁰` by `h⁰_ε(L)`, the largest dimension of
   a space of aperture-`L` tests on which `|W| ≤ ε‖f‖²`. The corpus has the lower bound
   `≥ e^{2L−2}/20` at `ε = exp(−e^{2L−2})` (`zeta_weil_near_radical_dimension_smooth`). A second
   unconditional construction gives dimension at least `(2−η)e^{2L}` at tolerance
   `exp(−η²e^{2L}/(300L))`, for `0<η≤1` and all sufficiently large `L`
   (`RHTower.zeta_weil_near_radical_sharp_count`). These are different dimension–tolerance
   tradeoffs, not a two-sided eigenvalue law. Wanted:
   the two-sided law, unconditionally in its upper half, and the exact rate
   `−log μ(L) ≍ 2π² N(T*)/log N(T*)` under the zeros-on-the-line hypothesis on an abstract
   configuration.
3. **The aperture of the Pontryagin law.** The exact count holds unconditionally (item 20‴) and
   its degree filtration exhausts the right zeros (item 20⁗); `RHTower.zeta_weil_inertia_law`
   gives the upper horizon and a lower count for isolated visible pairs. Open: a lower count
   without isolation, i.e. the degree at which `n` arbitrary right zeros (clustered, shallow, or
   accumulating in depth) become visible, with explicit constants. Over `𝔽_q` this is settled: the
   window `#{β} ≤ 2g` sees every outer eigenvalue (item 16′).
4. **The Kronecker law beyond the prime part.** On resonators the archimedean collar couples the
   towers through `ω(|i log p + j log q|)`; compute the full local intersection of narrow Hecke
   cycles and decide positivity of the finite-Euler-product form `ζ_p ζ_q · Γ` on lattice tests.
5. **The collar between towers.** By the Cartesian law (item 24) the prime part of every lattice
   test is a sum of tower forms; the interaction of different towers is the archimedean density
   `ω(|Σ_p (v_p(a) − v_p(b)) log p|)` and the pole. Bound this collar coupling on rank-`P` boxes
   and compare it with the sum `Σ_p E_p` of the envelopes, which is `≍ e^{r}` at aperture `r`.
6. **The pole-compensated aggregate (answered).** The survivor of item 27: subtracting the pole's
   mean field from the prime comb leaves the Chebyshev deficit, and its exponential rate is the zero
   width: `SquareRootThreshold.zetaZeroWidth_eq_sInf_deficitAbsRates` (the width is the infimum of
   the admissible rates of `|D(T)| ≤ B(1 + T)e^{(½+β)T}`). What remains open is the operator
   arrow `polarGroundEnergyRate ≤ zetaZeroWidth` recorded there.
7. **Successor structure (answered as a dictionary).** The pronic weight `1/(k(k+1))` is the pole
   mass `∫ e^{−u} du` of the successor cell `[log k, log(k+1)]` (`integral_successorCell`); the
   cells telescope to the pole mass (`sum_pronic_eq_integral`, `integral_pole_mass`). Over `ℤ`
   the successor is transverse to the norm grading (positive cell mass, coprimality, no prime
   incidence: `successorCell_integers`); over `𝔽_q[T]` it lies inside it (`f + 1` monic of the
   same degree, degenerate cell, coprime: `successorCell_functionField`). Open: the archimedean
   collar entry of two consecutive Hecke cycles, which on narrow bumps is a kernel of the form
   `e^{x/2}/sinh x` at `x = log(1 + 1/k)` rather than the pronic weight itself.
8. **Witt and λ-ring structure over `ℚ`.** Over `𝔽_q` the question is settled (item 15′): the
   pole plane splits off in the Witt ring, RH is purity of the `H¹` class, and integrality holds
   for fake data. Over `ℚ` the ghost components of `log ζ` are `Λ(n)`; the analogue of item 15′ is
   that integrality of the Euler product does not force the Hodge index, while the Hodge index
   selects `Λ` among all prime weights (`one_positive_square_iff_vonMangoldt`). Open: a λ-ring
   (Adams-operation) structure on the scaling surface whose Frobenius graphs are the Hecke cycles
   of item 24, with the pole plane splitting off as over `𝔽_q`.
9. **Spectral structure behind partial results.** *Real-rootedness* of ground states is explained
   by a positivity-preserving splitting of a non-real zero, `(w − w̄₀)(w − w₀) = (w − Re w₀)² +
   (Im w₀)²`, which divides a test into two real-rooted ones without raising its energy
   (`RHTower.CCMFullRealRootedGround.exists_realRooted_fullGround`). *Inertia gives proportions,
   not totality*: inertia counts each distinct off-line zero as one negative square, independently
   of its depth and multiplicity (items 20‴, 20⁵), and a finite compression at level `a` sees only
   the pairs below the horizon of `RHTower.zeta_weil_inertia_law`; totality needs every level
   (item 20⁗). Open: the specific constant `2/3`, which comes from the pair-correlation input of the
   rank–trace argument rather than from the form, and the Landau–Widom rate (topic 2).

---

## 7. Success criteria and criteria for contributions

**The programme succeeds when** the scaling surface carries an effectivity whose ampleness is
proved independently of the sign of the form and which satisfies the Riemann–Roch axiom (topic 1),
or when it is proved that no cone definable from a stated class of arithmetic data can have both —
in either case with the `𝔽_q` reduction to Weil's proof verbatim. The no-go half is proved for the
class of product cones of the pole quadrant with a set of tests (item 22); every effectivity is
classified once the Hodge index holds (item 22″); and the failure of the Hodge index is measured
exactly, by degree and by reflection sector, by the zeros right of the line (items 20‴–20⁵). The
effectivity half is RH-equivalent (item 21) and unsupplied.

**A contribution must:**

* be an unconditional Lean theorem in this folder, wired into the umbrella;
* state its object in the language of the polar surface (cycles, pairing, defect, primitive part,
  effectivity) and say which ingredient of Weil's proof it concerns;
* pass the selectivity tests *by typing*: say what it gives for fake curve data, for a non-unitary
  weight (`one_positive_square_iff_vonMangoldt`) and for an effectivity built from positive tests;
* run first over `𝔽_q` on the Frobenius span and reduce there to Weil's argument (items 5–16);
* separate metrology from geometry: a statement about what a degree can see belongs to the window
  law and to SSIC, a statement about what a cycle is belongs here;
* give an identity, not an estimate, wherever the corresponding step of Weil's proof is an identity;
  where a no-go is proved, record its positive survivor (items 7, 22, 27 are examples).

---

## 8. Principles

1. **Compute, then bound.** Every inequality of the theory is the positivity of a term in an
   identity whose other terms are exact (the decomposition of item 1, the Toeplitz law, the
   signature law).
2. **Audit the hypotheses.** The listed span identities admit fake data; identify the extra
   arithmetic or geometric constraint in every positivity argument.
3. **Fix the source without assuming the sign.** The weight is `Λ` and the pole has weight one;
   the one-positive-square property still requires proof.
4. **Calibrate over `𝔽_q`.** Every construction is run on curve data first.
5. **One Lorentz plane.** Count squares: the pole plane has one positive and one negative square;
   the excess positive directions of the scaling surface are counted exactly by the distinct
   zeros right of the line (item 20‴).
6. **Search the corpus before proving:** `scripts/formal_tools.py research "<query>"` (from the repository root).

---

## Source entry points

| Module | Content |
|---|---|
| `PolarSurfaceHodgeIndex` | polar surfaces, defect, four forms of Hodge index, Cauchy–Schwarz, one positive square |
| `AdjunctionThresholdLaw` | realizability classification, Hasse–Weil, free self-intersection, genus zero |
| `FrobeniusSpanCalibration` | curve data, Lefschetz/adjunction, span defect = Toeplitz form |
| `FrobeniusSpanHodgeIndexIsRH` | Hodge index on the span ⟺ unitarity |
| `FakeCurvesAndTheWindowLaw` | golden datum, window visibility and hiding |
| `TheGoldenCurveIsABeurlingSystem` | orbit counting for subshifts; the golden fake curve as a rank-one Beurling system |
| `WittIntegralityIsNotPurity` | zeta series and ghost components, Witt splitting of the pole plane, integrality vs purity |
| `SpanContactLaw` | contact window = number of distinct eigenvalues |
| `TheFrobeniusSpanDefectCountsTheOuterEigenvalues` | Pontryagin law over `𝔽_q`: span defect = #distinct eigenvalues off the circle, visible at window `2g` |
| `HodgeIndexFromEffectivity` | Riemann–Roch and ample axioms ⟺ Hodge index |
| `TheScalingSurface` | the scaling surface of `ℤ`; Hodge index ⟺ RH; positivity is not effectivity |
| `ArithmeticHodgeIndexSignatureLaw` | Gram signature law, one positive square ⟺ RH, selection of `Λ`, Pontryagin bound |
| `InfiniteGenusLaw` | no nonzero compact transform annihilating almost all simple critical zeros; RH ⟺ positive definite |
| `FiniteConfigurationPontryaginLaw` | transform interpolation and exact negative index for finite configurations |
| `TemperedConfigurationPontryaginLaw` | absolute convergence on tempered configurations, dual tests, translated pairs, exact negative index with finitely many right zeros |
| `TheKroneckerRankDichotomy` | recurrent (finite-rank) configurations have Hodge defect `0` or `∞` |
| `TheReflectionSectorsOfTheHodgeDefect` | even/odd sectors: exact sector Pontryagin law; each sector of `ζ` carries half the defect |
| `TheDegreeFiltrationOfTheHodgeDefect` | Hodge defect by degree: monotone, exhaustive, zero below `3/10` for `ζ` |
| `TheHodgeDefectCountsTheRightZeros` | zero-side coordinates in `ℓ²`, exponential-sum uniqueness, density, the exact Pontryagin law, Hodge defect of `ζ` = #zeros right of the line |
| `ResonatorKroneckerLaw` | Kronecker law of resonators, additive envelopes, successor orthogonality |
| `HeckeIncidenceCartesianLaw` | Cartesian law: the prime part is a product of towers |
| `ThePronicWeightIsThePoleMassOfTheSuccessorCell` | pronic weight = pole mass of the successor cell; `ℤ` vs `𝔽_q[T]` successor structure |
| `TheResonatorRemainderIsNegative` | the review's adjunction remainder is negative definite on resonators |
| `TheAdjunctionConjectureMeanField` | mean-field law, refutation of the polynomial adjunction bound |
