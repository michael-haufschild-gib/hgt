# Arithmetic Gauge Theory of the ring ℤ (AGT)

Namespace `GaloisForLFunctions.ArithmeticGaugeTheory`; umbrella `ArithmeticGaugeTheory.lean`.

**Question.** The integers carry two structures, addition and multiplication. Each has a dual: the
circle of additive characters, and the gauge torus `G` of unimodular completely multiplicative
functions. The prime source `Λ` is one point of `G`, the trivial point `0`, and Haar-almost every other
point already satisfies the square-root law that RH asks of `0`. What makes `0` typical, and where do
the two structures meet so that a proof could see the difference between `0` and its twins? Over `𝔽_q`
they meet in Frobenius, a ring endomorphism that is additive and multiplicative at once. `ℤ` has none.

AGT studies `ℤ` through this pair of duals. Its basic object is a **gauge point** `x ∈ G`, its twist
`χ_x`, and a coefficient system read through it. Its basic dichotomy is between **gauge-invariant**
statistics, which are constant on gauge orbits, and **gauge-charged** statistics, which have gauge mean
zero. Its basic invariant is the **gauge exponent** of a point, the least power bounding its twisted
partial sums. Everything is unconditional; RH appears only inside equivalences, as the statement that
the trivial point is typical.

---

## 1. Place in the research

The corpus established two facts that define this programme.

- **Selectivity has two sources.** Weil positivity is pointwise-closed, and every twist of `Λ` is a
  pointwise limit of vertical shifts (AKLT). A selective statement must use the shift-fixed terms (pole,
  Gamma) or non-ratio lags, i.e. additive structure (SSHA). Multiplicative data are gauge-invariant
  and cannot select.
- **The first source has a limited reach.** The pole pays the complete Weil form at bounded overlap and
  rejects the Liouville twin and `ω₁₁` there (TM). Past touching, additive successor shells enter the
  form. At the RH-complete overlap the remaining input is gauge charge at one point.

AGT is the programme for the second source. ACG built the gauge torus and its orthogonality; AGT asks
what the additive structure of `ℤ` contributes at the one point that is additively invariant, and which
invariants of a gauge point see the zeros.

| Programme | Interface |
|---|---|
| ArithmeticCorrelationGeometry (ACG) | `GaugeTorus`, `gaugeHaar`, `twist`, orthogonality, successor charge, finite gauge subgroups, the comeager–null exceptional set. AGT builds on these objects. |
| ArithmeticKreinLangerTheory (AKLT) | Twin-blindness of pointwise-closed statements; the parity twin lives in the Bohr closure; the producer ledger; Stepanov's order over `𝔽_q`. |
| ArithmeticOfSquareRootPrecision (ASRP) | Precision classes; deciding-input theorem; finite aperture cannot decide. AGT's tail invariance is the gauge form of these. |
| SpacingScaleHarmonicAnalysis (SSHA) | Diamagnetic inequality; the gauge enters through non-ratio lags; length–height coordinates. |
| TransMetzlerWeilPositivity, CACT, RAPT | Bounded-overlap positivity; successor-shell thresholds; nonpolar losses. AGT's shell decomposition is the exact algebra of the shells. |
| RHTower, BezoutValuationIncidence | Littlewood's Mertens bound at the zero abscissa, twisted Littlewood for `L(s, χ)`, the zero obstruction, `M(x) ≠ o(√x)`, the multiplicative large sieve. AGT turns them into the exponents of the special locus and the sampling of Haar measure by Dirichlet points. |
| HTGeometry, PNTPlus | Torus Haar measure as a product, the finite-modification zero–one law, Paley–Zygmund; the prime number theorem. AGT uses them to pin the typical exponent at `1/2`. |
| HeckeKreinToeplitz, EAHT | Index of the Weil kernel; global law. |
| ArithmeticOrientationGeometry (AOG) | Orientation of the scaling correspondence; AGT supplies the additive side its "Bézout-selective orientation" asks for. |

---

## 2. Why

**One point among many.** Twisting `Λ` or `μ` by a gauge point gives a coefficient system on the same
footing as the original. Haar-almost every twist cancels to the square root. The exceptional set is
comeager and null, and `0` lies in its closure. So RH is not a statement about an ensemble. It is the
typicality of one point, as Roth's theorem is the typicality of algebraic numbers.

**What singles out `0`.** It is the only gauge point compatible with addition, and the identity
`Λ * 1 = log` collapses every divisor fibre at `0` to an archimedean absolute value. A proof must use
this additive structure at square-root precision; multiplicative arguments prove almost-sure statements.

**Why a new field.** Over `𝔽_q`, Frobenius couples the two structures and Weil's theorem follows in
Stepanov's order. Over `ℤ` there is no endomorphism to supply multiplicity, and the parity twin is not
geometric. AGT locates what replaces Frobenius, and proves what cannot.

---

## 3. Objects and language

| Object | Meaning | Lean |
|---|---|---|
| Gauge torus `G`, Haar measure | Unimodular completely multiplicative functions | ACG `GaugeTorus`, `gaugeHaar`, `twist` |
| Trivial point `0` | The prime source itself | `twist_trivialPoint`, ACG `twist_zero` |
| Special point | Gauge point with additive structure | `TheAdditivelyInvariantPoint` |
| Special locus | Dirichlet gauge points and their vertical shifts | `dirichletGauge χ + verticalShift t` |
| Approximate ring endomorphism | Completely multiplicative, bounded additive defect | `IsApproxRingEndomorphism`, `AdditiveDefectBounded` |
| Adams operation `ψ^k` | `x ↦ k x` on `G`; raises twists to the `k`-th power | `adams`, `IsAdamsFixed` |
| Divisor fibre `F_x(ℓ)` | `Σ_{k∣ℓ} Λ(k) χ_x(k)` | `divisorFibre` |
| Prime pair form, ratio part, shells | Prime part of Weil's form on atomic families, split by `n` vs `km` | `primePairForm`, `ratioPart`, `shellPart`, `truncConv` |
| Gauge transform | Simultaneous twist of weights and vectors | `gaugeTransform` |
| Gauge exponent | Least power bounding twisted partial sums | `gaugeExponent`, `GaugePowerBound` |
| Zero abscissae `Θ`, `Θ_χ` | `sup Re ρ` over the zeros of `ζ`, of `L(s, χ)` | `RHTower.zetaZeroAbscissa`, `RHTower.zeroAbscissa` |
| Archimedean line | Vertical shifts `n^{it}` | `verticalShift` |
| Coprime Möbius sums | Twisted Möbius sums prime to `p`, to a set of primes | `coprimeMoebiusSum`, `coprimeMoebiusSet` |
| Factorial-ratio producer | `∏(a_i n)!/∏(b_j n)!`, `Σa_i = Σb_j` | `padicValNat_le_of_factorialRatio` |
| Twin tail | Keeps finitely many coordinates, Liouville sign elsewhere | ACG `twinTail` |
| Typical exponent | Almost-sure value of the Möbius exponent, equal to `1/2` | `typicalExponent`, `typicalExponent_eq_half` |
| Top primes | The primes of `(M, 2M]`: independent coordinates of `S_{2M}` | `topPrimes`, `gaugeRestrict` |
| Constant source | `a ≡ 1`; its exponent separates the special points | `oneSource` |
| Rough source | Coefficients on integers whose prime factors exceed `R` | `RoughSource` |
| Escape state | Limit of `|S_N|² dHaar / N`: where the energy of the sums sits on `G` | `tendsto_escapeCoefficient` |

**Words.**

- *Gauge-invariant*: constant on gauge orbits. *Gauge-charged*: gauge mean zero. *Boundary*:
  shift-fixed and archimedean (pole, Gamma).
- *Typical*: has the Haar-almost-sure exponent of the source (`1/2` for the Möbius and the constant
  source). *Special*: carries additive structure. *Liouville point*: a twin tail or the Liouville twist;
  *exceptional*: exponent `> 1/2`.
- *Coherent*: a nonnegative statistic, maximal at `0`. *Rational point of `ψ^q`*: a twist with
  `χ^q = χ`.
- *Shell*, *repayment*, *marginal positivity*, *multiplicity beyond divisibility*, *Frobenius
  substitute*, *class of the trivial point* (finite modifications and vertical shifts of `0`).

---

## 4. Mechanisms

1. **Gauge calculus.** Orthogonality of twists splits every statistic into a gauge-invariant part
   (coinciding products) and a gauge-charged part. The gauge average of the prime pair form is its ratio
   part; the shells average to zero (`integral_primePairForm_gaugeTransform`).
2. **Special-point rigidity.** A nowhere-vanishing completely multiplicative function that is
   eventually periodic or convergent is identically one (`eq_one_of_eventually_periodic`,
   `eq_one_of_tendsto`). Dirichlet characters escape only because they vanish at their modulus.
3. **The Frobenius gap and its home.** Completely multiplicative maps with bounded additive defect are
   the identity or bounded by one (`approxRingEndomorphism_classification`); the unimodular ones are the
   gauge points. The equation `x^q = x` lives instead on `G`: the fixed twists of `ψ^q` are the
   finite-order twists (`isAdamsFixed_iff`), the trivial point is the unique fixed twist of `ψ²`.
4. **Coherence.** A nonnegative statistic is maximal at `0` (`norm_twistSum_le_trivial`); the excess
   over the gauge root-mean-square is at least `√(S(0)/L)` (`coherence_ratio`). For `Λ` this coherent
   excess is the pole (`primeSource_coherence`). The divisor collapse `F_0(ℓ) = log ℓ` is the
   fibrewise form (`trivialPoint_coherent`).
5. **Diamagnetism.** On nonnegative data the gauge-transformed prime pair form and its shells are
   dominated by their value at `0` (`norm_primePairForm_gaugeTransform_le`,
   `norm_shellPart_gaugeTransform_le`). Since the prime part of Weil's form is subtracted, `0`
   minimizes the energy among its gauge transforms on nonnegative data.
6. **Exponent transport.** Abel summation transports power bounds through slowly varying weights
   (`norm_sum_mul_le_of_partial_sums`); splitting off a prime inverts through a geometric series in
   `p^{−θ}` (`coprimeMoebiusSum_eq_sum`, `norm_coprimeMoebiusSum_le`). Both preserve the exponent.
7. **Bounded multiplicity.** Above the square root of their length, balanced factorial ratios have
   `v_p ≤ #denominators − 1` (`padicValNat_le_of_factorialRatio`).
8. **Congruence projection.** Averaging over the Dirichlet gauge points of level `q` keeps exactly the
   pairs `km ≡ n (mod q)`; a shell `n = km + j` survives iff `q ∣ j` (`sum_primePairForm_dirichletGauge`).
   The finite gauge points of conductor up to `R` sample the Haar mean square of rough sources up to the
   factor `N + R² − 1` (`dirichletGauge_largeSieve_haar`).
9. **Zero–one law.** For a tail-invariant source, sublevel sets of the exponent are invariant under
   finite modification and hence have Haar measure `0` or `1`
   (`gaugeHaar_gaugeExponent_le_eq_zero_or_one'`).
10. **Independent top block.** The integers `n ≤ 2M` divisible by a prime of `(M, 2M]` are those primes.
    Translating along these coordinates moves `S_{2M}` by a sum of independent Steinhaus variables
    (`partialSum_add_gaugeRestrict`); products of two elements of `{1} ∪ primes` determine the
    pair, so Paley–Zygmund applies with constant `1/8` (`block_paleyZygmund`), and translation
    invariance spreads the bound over the torus (`le_measure_of_translates`).
11. **Descent through a modulus.** Removing the primes of `q` one at a time costs `log₂ N + 1` per prime
    for the constant source (`norm_coprimeTwistSum_le_of_insert`) and preserves power bounds for the
    Möbius source (`hasBound_iff_of_subset`); on the integers prime to `q` a Dirichlet gauge point is its
    character. So the gauge sums at a Dirichlet point are character sums, bounded by periodicity, and
    twisted Mertens sums, governed by the zeros of `L(s, χ)`.

---

## 5. Pillar theorems

1. **Uniqueness of the additively invariant point** — `eq_one_of_eventually_periodic`,
   `twist_eq_one_of_tendsto`, `dirichletCharacter_eq_one_of_periodic_gauge`.
2. **The Frobenius gap** — `approxRingEndomorphism_classification`,
   `approxRingEndomorphism_unimodular_iff`, `ringEndomorphism_classification`,
   `int_approxRingEndomorphism_classification`; contrast `natDegree_frobenius`.
3. **The Adams operations** — `twist_adams`, `adams_adams`, `isAdamsFixed_iff_frobenius`,
   `isAdamsFixed_two_iff`, `isAdamsFixed_dirichletGauge`.
4. **The divisor collapse** — `divisorFibre_trivial`, `re_divisorFibre_eq_log_iff`,
   `divisorFibre_eq_log_forall_iff`, `integral_divisorFibre`, `integral_divisorFibre_mul_conj`,
   `trivialPoint_coherent`.
5. **The shell decomposition** — `primePairForm_eq_convolved`,
   `primePairForm_eq_ratioPart_add_shellPart`, `ratioPart_gaugeTransform`,
   `integral_shellPart_gaugeTransform`, `integral_primePairForm_gaugeTransform`,
   `truncConv_poleVector_trivial`.
6. **The gauge exponent** — `ae_gaugeExponent_le_half`, `gaugeExponent_moebius_trivial` (the trivial
   point has exponent `Θ = sup Re ρ`), `riemannHypothesis_iff_gaugeExponent_moebius_trivial_le_half`,
   `moebius_exponent_exceptional_null_and_residual`, `moebius_exponent_threeQuarters_residual`.
7. **Invariance of the exponent** — `gaugeExponent_add_verticalShift`,
   `gaugeExponent_moebius_verticalShift`, `gaugeExponent_moebius_eq_of_agree_off_finset`,
   `gaugeExponent_moebius_finiteFlip`: the whole class of the trivial point has exponent `Θ`.
8. **Coherence and diamagnetism** — `coherence_ratio`, `primeSource_coherence`,
   `norm_primePairForm_gaugeTransform_le`.
9. **Bounded multiplicity of classical producers** — `padicValNat_le_of_factorialRatio`,
   `padicValNat_centralBinom_le_one`.
10. **The Liouville points** — `gaugeExponent_moebius_twinTail`, `gaugeExponent_moebius_liouville`
    (exponent exactly `1`), `one_le_of_cylinder_bound` (finitely determined certificates are useless).
11. **The typical exponent is one half** — `gaugeHaar_gaugeExponent_le_eq_zero_or_one'`,
    `ae_gaugeExponent_eq_typical`, `typicalExponent_eq_half`, `ae_gaugeExponent_moebius_eq_half`.
12. **RH is an extremal equality** — `half_le_gaugeExponent_moebius_trivial` (the trivial point is never
    better than typical), `riemannHypothesis_iff_trivialPoint_eq_typical`,
    `typicalExponent_le_gaugeExponent_moebius_finiteFlip`,
    `typicalExponent_le_gaugeExponent_moebius_verticalShift`.
13. **No gauge-invariant certificate** — `gaugeExponent_moebius_not_const`,
    `threeQuarters_le_of_gaugeInvariant_bound`.
14. **The major arcs and the large sieve** — `sum_primePairForm_dirichletGauge`,
    `sum_shellPart_dirichletGauge`, `shellPair_survives_iff`, `dirichletGauge_largeSieve_haar`.
15. **Affine-invariant kernels are trivial** — `affineInvariant_kernel_lt`,
    `affineInvariant_kernel_gt`, `affineInvariant_kernel_diag`.
16. **The special points of the constant source are atypical** — `ae_gaugeExponent_one_eq_half`;
    `gaugeExponent_one_dirichletGauge_verticalShift` (exponent `0` along every nonprincipal Dirichlet
    line), `gaugeExponent_one_principal_verticalShift` and `gaugeExponent_one_trivial` (exponent `1`, the
    pole), `gaugeExponent_one_special_ne_typical`,
    `trivialPoint_atypical_one_and_rh_iff_typical_moebius` (typical modulo the pole).
17. **The special locus reads GRH** — `gaugeExponent_moebius_dirichletGauge` (the Möbius exponent at a
    primitive Dirichlet point is `Θ_χ`), `typicalExponent_le_gaugeExponent_moebius_dirichletGauge`,
    `dirichletGRH_iff_dirichletGauge_typical`, `gaugeExponent_moebius_dirichletGauge_verticalShift`;
    on average it is typical at every scale: `largeSieve_coprimeMoebius_dirichletGauge`,
    `card_atypical_dirichletGauge_le_rpow`.
18. **The Liouville point is the antipode** — `primeGaugeSum_liouville_add_trivial`
    (`S_N(ℓ) + S_N(0) = 2ψ(√N)`), `tendsto_primeGaugeSum_trivial`, `tendsto_primeGaugeSum_liouville`
    (pole `+1`, anti-pole `−1`), `eventually_re_primeGaugeSum_liouville_neg`.
19. **The escape state leans to the Liouville point** — `integral_normSq_moebiusGaugeSum_mul_twist_eq`,
    `tendsto_escapeCoefficient` (Fourier coefficients `μ(a) d(a)/a`), `tendsto_escapeMass` (`6/π²`),
    `tendsto_escapeCoefficient_prime` (`−(6/π²)/(p + 1)`), `eventually_re_escapeCoefficient_prime_neg`.

---

## 6. The programme's questions and their status

| Question | Status | Answer |
|---|---|---|
| What replaces `x^q = x` over `ℤ`? | **Answered** | Not a self-map of `ℤ`: the only bounded-defect endomorphisms are the identity and gauge points (Frobenius gap). The equation lives on the gauge torus as the fixed-point equation of `ψ^q`; its solutions are the finite-order twists, with the trivial point the unique fixed twist of `ψ²`. A producer built from Adams operations acts on characters, not on integers. |
| At which points should an auxiliary vanish, and finer than divisibility in what sense? | **Partly answered** | Divisibility cannot select a parity class (AKLT); factorial ratios have bounded multiplicity above the square root. Open: a vanishing notion whose multiplicity grows. |
| Is there a structure on which the Liouville twist acts geometrically? | **Answered** | Yes: `G`, where the twist is translation by a point; that point is a pointwise limit of vertical shifts but not one of them (AKLT). The exponent is constant along the archimedean line and under finite modifications, so typicality is not visible to the archimedean place or to finitely many primes. |
| What is the positive form of the affine Weil kernel, and is its boundary the pole? | **Partly answered** | A kernel invariant under all dilations and the successor is three constants (`affineInvariant_kernel_lt`): affine positivity without a boundary term carries no arithmetic. The dilation face (ratio part) is the gauge average; the successor face (shells) is gauge charge, projected by finite gauge subgroups onto `q ∣ j`. The pole is the boundary that separates the twins: for the prime source the Liouville point is the antipode of the trivial point, `S_N(ℓ) + S_N(0) = 2ψ(√N)`, so the pole is `+1` at `0` and `−1` at `ℓ`, while every size statement sees both as coherent. Open: the positive form itself, a unitary affine action whose matrix coefficients carry this boundary. |
| Which gauge-charged statistics have values at `0` determined by structure? | **Answered for the coherent class and the special locus** | Nonnegative statistics are coherent at `0` and determined by their coefficients: divisor fibres (`log ℓ`), the prime source (`ψ(N)`, the pole), the shells on the pole vector (`log ℓ`). For the constant source the whole special locus is decided by structure: exponent `0` along nonprincipal Dirichlet lines (periodicity), `1` along principal ones (the pole), against `1/2` almost surely. Signed statistics such as Möbius sums are not determined by structure; their size at `0` is `Θ`. Their Haar escape state is pure structure (an Euler product, `tendsto_escapeCoefficient`) and leans to the Liouville point, so the discrepancy at `0` is invisible to it. |
| What is the gauge exponent of a point, and is it `Θ` at `0`? | **Answered** | The exponent is almost surely exactly `1/2` (zero–one law plus the independent top block); it equals `Θ` at `0`, at every vertical shift and at every finite modification of `0`; it equals `1` at every twin tail and at the Liouville point; it exceeds `1/2` on a residual null set and is at least `3/4` on a residual set. Unconditionally `Θ ≥ 1/2`: the class of the trivial point is never better than typical, and RH is the equality `exp(0) = θ_typ`. At a primitive Dirichlet point the exponent is `Θ_χ ≥ 1/2`, and GRH for `χ` is the typicality of that point. |
| What replaces Riemann–Roch as an index ceiling? | **Negative part answered; positive part open** | No gauge-invariant bound can go below `3/4` (`threeQuarters_le_of_gaugeInvariant_bound`), and no bound that reads finitely many coordinates can go below `1` (`one_le_of_cylinder_bound`). An index ceiling must use gauge-charged information about the specific point. |
| Why is positivity marginal at the limit? | **Partly answered** | In exponent form RH is extremal: the trivial point can only err upward from the floor `1/2` that Haar-almost every point attains, so RH asks for equality at a boundary, with zero room (`riemannHypothesis_iff_trivialPoint_eq_typical`). Open: the exact identity that carries the zero margin of Weil's form, and whether `1/2` is the floor on all of `G`. |

---

## 7. Traps

| Trap | Truth |
|---|---|
| A multiplicative argument proves something about `0` | It proves the statement Haar-almost surely and decides nothing about `0`. |
| Finitely many primes, or the archimedean place, can decide typicality | The exponent is invariant under finite modifications and vertical shifts. |
| Dirichlet characters are special gauge points in the periodic sense | Unimodular periodic points are trivial; characters are periodic because they vanish at their modulus. |
| `ℤ` has an approximate Frobenius | Bounded-defect endomorphisms are the identity or bounded gauge points. |
| Adams operations are Frobenius on integers | They act on characters; their fixed points are finite-order twists, not integers. |
| The energy of the Möbius sums sits near the trivial point | Its escape state leans to the Liouville point (coefficient `−(6/π²)/(p + 1)` at each prime); off-line energy at `0` is invisible to every Haar average. |
| Coherence at `0` is arithmetic information | It is forced by nonnegativity; the pole is coherence. Arithmetic information sits in signed statistics. |
| A special point can be better than typical for `μ` | The trivial point and every primitive Dirichlet point have Möbius exponent `≥ 1/2`: for `μ` the special locus can only err upward. |
| Additive structure at a point makes it typical | For the constant source it makes every special point atypical: exponent `0` or `1`, never `1/2`. Typicality at `0` must come from the source (`μ = 1/ζ`), not from the point. |
| Shells at `0` help positivity on nonnegative data | Diamagnetism: they are maximal at `0` and enter Weil's form with a minus sign. Repayment must come on signed, nonpolar directions. |
| The exceptional set is small | It is null but residual: topologically it is everything. |
| Typical in measure is typical in category | The two notions disagree on `G`. |
| Factorial ratios can grow multiplicity | Above the square root their multiplicity is bounded by the number of factorials. |

---

## 8. Tools

| Tool | Purpose | Status |
|---|---|---|
| Gauge calculus | Invariant/charged split; gauge averages | Built (with ACG): `integral_twistSum`, `integral_primePairForm_gaugeTransform`. |
| Special-point theory | Gauge points with additive structure | Built: periodic and convergent points; Dirichlet gauge points as rational points of Adams operations; the constant source has exponent `0` at Dirichlet points and `1` at the trivial point. |
| Endomorphism theory | Multiplicative maps compatible with addition | Built: classification and Frobenius gap; Adams operations on `G`. |
| Shell calculus | Exact shells of the prime pair form | Built: convolved form, ratio/shell split, gauge charge, pole-vector collapse. Not built: sign of the complete form at `c = 2`. |
| Gauge exponents | Typicality of points | Built: Haar-a.e. exponent exactly `1/2` (the calibration test), zero–one law, trivial point `= Θ`, primitive Dirichlet points `= Θ_χ`, both never below typical; Liouville points `= 1`; invariance along the archimedean line and under finite modifications. Not built: Siegel and Deuring–Heilbronn as calibration. |
| Producer theory | Multiplicity of integer auxiliaries | Built: factorial-ratio no-go; the `ℤ`/`𝔽_q` contrast. Not built: a growing-multiplicity producer. |
| Affine Krein–Langer theory | Positivity on the affine semigroup with boundary | Built: the no-go (affine-invariant kernels are trivial: one source, no arithmetic) and the boundary test (the pole separates the twins by sign). Not built: the positive form. |
| Index ceiling | Bound `κ` from ring data | No-go built: gauge-invariant and finitely determined certificates fail. The positive ceiling is open. |
| Dispersion inside Weil's form | Gauge charge averaged over moduli | Built: congruence projection of the shells at every level; the large sieve as Haar sampling by finite gauge points; the special locus is square-root typical on average at every scale, with at most `2N^{1−2ε}` exceptions up to conductor `√N`. Not built: Bombieri–Vinogradov for the shells. |

---

## 9. Open research topics

1. **A growing-multiplicity producer.** An auxiliary over `ℤ` with `v_p ≥ 2` on a positive proportion of
   the primes of `(x, 2x]` at size below twice their mass, or a no-go for a class beyond factorial
   ratios. Adams operations suggest building it on characters.
2. **Bombieri–Vinogradov for the shells.** Turn the large-sieve sampling into a level-of-distribution
   bound for the shell part, and measure what it leaves at the single point `0`.
3. **Typicality of special points.** Every point of the special locus has Möbius exponent `Θ_χ ≥ 1/2`,
   and its typicality is GRH for `χ`; on average over the locus typicality holds at every scale.
   The gap is from "most points at each scale" to "each point at all scales". A Roth- or Siegel-type theorem would bound `Θ_χ` from the
   arithmetic of the locus; a Thue-type first rung, a uniform bound `Θ_χ ≤ 1 − c`, would already be a
   zero-free strip.
4. **The exponent floor.** Is the Möbius exponent at least `1/2` at every gauge point? It holds almost
   surely and on the class of the trivial point; a general proof would need a Carlson-type mean value
   for `1/L_x`.
5. **Shell repayment.** The repayment of the nonpolar `−log c` loss on signed directions, organized by
   conductors `q ∣ j`.
6. **Affine Krein–Langer theory.** A positivity principle for the affine semigroup whose boundary is the
   pole.
7. **An index ceiling from ring data.**

---

## 10. Success criteria and what a contribution must be

**Success.** One of the following:

- a statement about gauge charge at `0` that is false for Haar-random points;
- a producer with growing multiplicity;
- a positivity theorem in which additive structure pays on signed directions;
- a typicality theorem for the class of the trivial point;
- a proof that no input of a stated class can do any of these, with its positive survivor.

**A contribution:**

1. is unconditional;
2. says what it gives at `0`, at Haar-random points, at Liouville points, along the archimedean line and
   at finite modifications;
3. separates gauge-invariant from gauge-charged content;
4. states its analogue over `𝔽_q`;
5. records the positive survivor of every no-go.

**Battery.** The Liouville twin; prime flips; twin tails; Haar-random gauge points; Dirichlet gauge
points; vertical shifts; `Λ + ε n^{−η}`; over-regular Beurling systems; the golden curve datum.

**Principles.** Identities first, sign last. Work at one point. Calibrate over `𝔽_q`. Selectivity is a
theorem. A reformulation is not a reduction.
