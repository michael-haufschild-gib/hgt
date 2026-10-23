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
the missing geometric input. The finite Pontryagin law and Cartesian prime-incidence law are
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

### 3.4 Fake curves and the window law (`FakeCurvesAndTheWindowLaw`)

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

### 3.5 The contact law (`SpanContactLaw`)

16. For unitary data the defect on the window of `n` Frobenius graphs is positive definite iff
    `n ≤ s`, the number of distinct eigenvalues (`toeplitz_pos_on_window_iff`); above it the radical
    contains the reduced characteristic polynomial, which is real (`exists_radical_of_lt`,
    `map_conj_reducedCharPoly`). The sections of the span are its multiples.

### 3.6 The scaling surface, the signature law and the Pontryagin bound
(`TheScalingSurface`, `ArithmeticHodgeIndexSignatureLaw`)

17. **The scaling surface is a polar surface whose defect is Weil's form**
    (`scalingSurface`, `scalingSurface_defect_self`), so **its Hodge index theorem is RH**
    (`scalingSurface_hodgeIndex_iff`), and under RH Weil's pairing obeys Cauchy–Schwarz
    (`weilPair_sq_le_of_riemannHypothesis`).
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
    no prescribed aperture or uniform conditioning estimate, and it does not remove the infinite
    on-line tail of the actual zeta configuration.

### 3.7 Hodge index from effectivity (`HodgeIndexFromEffectivity`, `TheScalingSurface`)

21. **Hodge index ⟺ an effectivity with the Riemann–Roch and ample axioms**
    (`exists_effectivity_iff_hodgeIndex`); the positive cone is the canonical witness
    (`positiveCone_axioms`). For `ℤ`: **RH ⟺ such an effectivity exists on the scaling surface**
    (`riemannHypothesis_iff_exists_effectivity`).
22. **Positivity is not effectivity.** The pole quadrant with nonnegative tests fails the
    Riemann–Roch axiom unconditionally (`posTestCone_not_riemannRoch`, via
    `not_riemannRoch_of_perturbation`).
22′. **No cone avoids the positive cone.** An effectivity with the Riemann–Roch axiom and
    nonnegative degrees contains every class of positive square and positive degree
    (`openPositiveCone_subset_of_effectivity`); its ample axiom therefore contains the Hodge index
    constraint on the resulting cycle theory. Items 21–22′ specify the missing
    section count; none of them supplies it.

### 3.8 The infinite genus law (`InfiniteGenusLaw`)

23. **No exact transform-annihilating test at any aperture.** A test whose transform vanishes at all but finitely many simple
    critical zeros is zero (`eq_zero_of_paperFT_vanish`), and **RH ⟺ Weil's form is positive
    definite** on nonzero tests (`riemannHypothesis_iff_weil_positive_definite`). The contact window
    of the unitary finite-field span has no exact counterpart in this test class. This is strict
    positivity of each nonzero test under RH, not a uniform positive lower bound for every
    normalized test. Near-radical families remain possible.

### 3.9 The adjunction formula on resonators (`ResonatorKroneckerLaw`, `HeckeIncidenceCartesianLaw`)

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
   towers (items 24–25); the remaining archimedean and polar terms still require a sign argument.
7. **Kronecker rank.** Rank-one (lattice) systems are curve data; their span is Hodge iff unitary
   (item 12), fake data exist (item 13), and hiding needs genus exponential in the degree (items
   14–15). For tests of any Kronecker rank the prime part decouples into one tower per prime
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
| Counting multiplicities in the Pontryagin bound | Negative squares are bounded by the number of *distinct* zeros right of the line; a multiple zero contributes one rank-two block. |
| Expecting finitely many window conditions to see a deep pair | Over `𝔽_q` the hiding genus grows like `r^n` (items 14–15); over `ℚ` the genus is infinite. |
| Signs of the hyperbolic plane | `H·V = 1`, `H² = V² = 0`; the ample class `H + V` has square `2`, the class `H − V` square `−2`; the pole plane alone has one positive and one negative square (`posIndex_polePlane`, `negIndex_polePlane`). |

---

## 6. Open problems and the tools the programme develops

1. **An independent effectivity for `ℤ` — the open core.** The scaling-surface Hodge index is
   RH-equivalent, but no independent arithmetic effectivity theory supplies it. Wanted: a notion of
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
3. **Quantitative and infinite Pontryagin laws.** Finite configurations already satisfy the exact
   index formula (item 20′). Control the aperture, norms and conditioning of the interpolating
   tests, then account for the remaining infinite zero sum. The target is a theorem relating
   negative index at aperture `A` to visible off-line zeros, with the tail estimate explicit.
4. **The Kronecker law beyond the prime part.** On resonators the archimedean collar couples the
   towers through `ω(|i log p + j log q|)`; compute the full local intersection of narrow Hecke
   cycles and decide positivity of the finite-Euler-product form `ζ_p ζ_q · Γ` on lattice tests.
5. **The collar between towers.** By the Cartesian law (item 24) the prime part of every lattice
   test is a sum of tower forms; the interaction of different towers is the archimedean density
   `ω(|Σ_p (v_p(a) − v_p(b)) log p|)` and the pole. Bound this collar coupling on rank-`P` boxes
   and compare it with the sum `Σ_p E_p` of the envelopes, which is `≍ e^{r}` at aperture `r`.
6. **The pole-compensated aggregate.** The survivor of item 27: subtract from `Σ_p w_p p^{iξ}` the
   pole's mean field `∫ t^{−1/2+iξ}`; the centred aggregate is governed by the zeros, and its growth
   rate should be the zero width.
7. **Successor structure.** Consecutive Hecke cycles `Γ_k, Γ_{k+1}` (`k ≥ 2`) have no prime
   intersection (`heckeIncidence_succ`); over `𝔽_q[T]` consecutive polynomials of positive degree
   sit at lag `0`. State the pronic weight `1/(k(k+1))` as an intersection number of the
   archimedean collar at the lag `log(1 + 1/k)` and prove that `𝔽_q[T]` is the case where successor
   and incidence structures coincide.
8. **Witt and λ-ring structure.** Over `𝔽_q`, `Z_C = Z_{ℙ¹} · P_C` splits off the pole plane in the
   ring of Witt vectors and RH is purity of the `H¹` class; formalize the decomposition and the
   statement that integrality of `P_C` holds for fake data.
9. **Spectral structure behind partial results.** Why inertia gives proportions (`2/3`) and not totality
   (items 19–20 give the exact accounting), why finite-prime extremizers are real-rooted, and the
   Landau–Widom rate (topic 2).

---

## 7. Success criteria and criteria for contributions

**The programme succeeds when** the scaling surface carries an effectivity whose ampleness is
proved independently of the sign of the form and which satisfies the Riemann–Roch axiom (topic 1),
or when it is proved that no cone definable from a stated class of arithmetic data can have both —
in either case with the `𝔽_q` reduction to Weil's proof verbatim. Until then the Hodge index of the
scaling surface is RH-equivalent and unsupplied; the programme's theorems are the exact
specification of what is missing and the calibration of every step over `𝔽_q`.

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
   excess positive directions are bounded by the distinct right-hand zeros; finite configurations
   attain this count on suitable test families.
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
| `SpanContactLaw` | contact window = number of distinct eigenvalues |
| `HodgeIndexFromEffectivity` | Riemann–Roch and ample axioms ⟺ Hodge index |
| `TheScalingSurface` | the scaling surface of `ℤ`; Hodge index ⟺ RH; positivity is not effectivity |
| `ArithmeticHodgeIndexSignatureLaw` | Gram signature law, one positive square ⟺ RH, selection of `Λ`, Pontryagin bound |
| `InfiniteGenusLaw` | no nonzero compact transform annihilating almost all simple critical zeros; RH ⟺ positive definite |
| `FiniteConfigurationPontryaginLaw` | transform interpolation and exact negative index for finite configurations |
| `ResonatorKroneckerLaw` | Kronecker law of resonators, additive envelopes, successor orthogonality |
| `HeckeIncidenceCartesianLaw` | Cartesian law: the prime part is a product of towers |
| `TheAdjunctionConjectureMeanField` | mean-field law, refutation of the polynomial adjunction bound |
