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

**The shared target.** The programmes in the table work on RH as the sign of one critical arithmetic
form. ACS reads that sign as the Hodge index of the scaling surface and asks for the geometric input
that produced it over `𝔽_q`: an effectivity with Riemann–Roch supply. Every positivity route of the
corpus — incidence, lag, aperture — meets the same form; ACS contributes the exact count of its
failure (right zeros), the calibration over `𝔽_q`, and the fake data any forcing argument must
exclude. Read §§1–2 for the dictionary, §3 for the pillar theorems, §5 for the traps and §§6–7 for
the questions and open problems.

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
15. **Visibility and hiding.** Over `𝔽_q` the window `n_0 + 2 n_+ ≤ 2g` sees all `n_+` outer
    eigenvalues (`card_spectrum_eq_onCircle_add_two_mul_outer`, `negIndex_spanGram_eq_of_onCircle`).
    Over `ℚ`, an isolated pair `½ ± δ + iγ₀` in an on-line lattice of density `L` is seen exactly
    from the degree where `sinh(2δa)/δ = 2L + 2a` (`hodgeDefectAt_isolatedPair`). For `n` pairs in
    density `L`, below `L/2` the Weil form is `2L∫|f|² + Σ_k (|f̂(γ_k − iδ_k) + f̂(γ_k + iδ_k)|² −
    |f̂(γ_k − iδ_k) − f̂(γ_k + iδ_k)|²)/2` (`re_W_multiPairConfig`), so any subset `S` whose
    complement has total pair energy `Σ_{k∉S} (sinh(2δ_k a)/δ_k − 2a) ≤ L` bounds the defect by
    `|S|` (`hodgeDefectAt_multiPairConfig_le`, `hodgeDefectAt_multiPairConfig_eq_zero`,
    `exists_n_hidden_at_degree`). Conversely, with dual tests `b` on `[−a₀, a₀]` (which exist for
    every `a₀ > 0`, `exists_dual_tests_Icc`), all right zeros are visible at `a ≥ a₀ + Δ` once
    `2 · onLineMass Z b + ½ ≤ cosh((Re ρ − ½)Δ) − 1` (`hodgeDefectAt_eq_of_onLineMass`,
    `hodgeDefectAt_eq_of_log_onLineMass`), with `onLineMass = 2L Σ_ρ ∫|b_ρ|²` in a lattice of
    density `L` (`onLineMass_multiPairConfig_eq`, `hodgeDefectAt_multiPairConfig_eq_card`),
    `onLineMass ≤ m₀ M (2a₀ + 2π) e^{2π} Σ_ρ ∫|b_ρ|²` under unit-window density `M`
    (`onLineMass_le_of_locallyBounded`, `hodgeDefectAt_eq_of_locallyBounded`), and
    `hodgeDefectAt Z a ≥ |T|` for any `T` separated isolated right zeros with positive
    `visibleMargin` under logarithmic density `A₀ log(|t| + 3)` (`card_le_hodgeDefectAt_of_visible_pairs`,
    `zeta_intersectionGram_posIndex_ge_of_visible_pairs`). Over `𝔽_q` the window `2g` sees
    everything; over `ℚ` no degree does (`exists_hidden_at_degree`).
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

### 3.8 Rank–trace inertia: what a Gram functional can certify (`TheTwoThirdsConstantIsPairCorrelation`, `BreakingTheCoalescenceBlindSpotAndThreeQuarters`)

Without Riemann–Roch effectivity the intersection form still certifies a *proportion* of zeros,
through rank–trace inertia on the real evaluation Gram `Â = P + Q` of hat-unit tests — `P` from the
critical-line zeros, `Q` from the off-line pairs — with `tr Â = N` and `‖Â‖_F² = κN`. Inertia
replaces the Hodge index `p = 0` by `n₊(Q) ≤ p`.

25. **Capacity `2 − κ` and the coalescence blind spot.** At `c = 2`, the unique value with
    `c² − k_c(2) = (c − 2)² = 0` (`offLine_sub_doubleZero_weight`,
    `paramDeficit_nonneg_and_eq_zero_iff`), a double critical zero and a coalescing off-line pair
    produce the identical rank-one matrix `2vvᵀ` (`blockA_coalescedPair_eq_doubleZero`). The form
    certifies `(2 − κ)N` simple critical zeros (`unitary_calibration_full_simple` at `κ = 1` over
    `𝔽_q`; `κ ≥ 2` on fake curves with `s₁ = 0`, `fake_curve_frobSq_lower_bound`,
    `goldenDatum_rankTrace_barrier`), and no functional of `(Â, N)` alone certifies more
    (`universal_matrix_functional_barrier`). Below the square-root threshold `0 < λ ≤ 1` the
    archimedean diagonal `1/λ` and the unconditional prime diagonal `λ/3` give `κ(λ) = 1/λ + λ/3`, so
    the certificate is `2 − κ(λ) ≤ 2/3`, with equality only at `λ = 1`
    (`subthreshold_two_thirds_deficit`, `subthreshold_cert_le_two_thirds`), where the barrier is exact
    on `6k`-zero configurations (`universal_matrix_functional_barrier_at_two_thirds`). This is the
    intersection-theoretic reading of Alpöge–Furman's two-thirds theorem
    (`RHTower.thmA_lam_spectralSlack`, from the vendored `Zeta23`): the constant `2/3` is set by
    stopping pair correlation at `λ = 1`, and every finite pair-correlation bound `F ≤ B` beyond
    `λ = 1` would give `2/3 + 1/(3(3B − 2))` (`two_thirds_and_pair_correlation_escape`,
    `tendsto_certOpt_atTop`).
26. **Two routes past the blind spot, each with one unproved input.** The summed matrix forgets
    which part of `Â` is on the line; the pair `(P, Q)` does not. For `Q = 0` the on-line Parseval
    slack is exactly `‖P‖_F² − c tr P + (c²/4) rank P` (`onSlack_zero_eq`), which restores the rank
    at `c = 2` (`rank_trace_add_onSlack_zero_eq_rank`), while a non-coalesced off-line pair carries
    negative-part credit `4m‖y‖² > 0` (`offLine_pair_negPart_credit_pos`). The average of the `c = 2`
    and `c = 3` functionals is `((7 − 3κ)/4)N`, which is `(3/4)N` at `κ = 4/3`
    (`jointRankTrace23_at_four_thirds`, `three_quarters_of_broken_blind_spot_at_four_thirds`). For `ζ`
    this gives two implications, not a theorem:
    * *the zero-side route:* the unconditional bound `(2/3 − ε)N + S(T) ≤ N₀*` keeps the zero-side
      slack `S(T) ≥ 0`, so `S(T) ≥ N(T, 2T)/12` would give `(3/4 − ε)N(T, 2T) ≤ N₀*(T, 2T)`
      (`zeta_three_quarters_of_spectralSlack_one_twelfth`);
    * *the prime-side route:* `3/4` is equivalent to `κ ≤ 5/4` (`kappa_five_fourths_iff_three_quarters`);
      at bandwidth `λ = 4/3` the diagonal, archimedean and pole constant is unconditionally
      `43/36 = 5/4 − 1/18` and the prime–pole cross term is `O(T^{5/6}log²T)`, so the proposition
      `RHTower.PrimeSurplusFourThirds` — a prime surplus filling the margin `1/18` — would give `3/4`
      of the zeros simple and on the line; double windowing bounds the prime-frequency off-diagonal
      at aperture `min(r, ρ)` unconditionally
      (`zeta_three_quarters_from_prime_surplus_and_double_window`).

    Neither premise is proved. The theorems fix exactly what has to be shown.

### 3.9 The λ-ring of the scaling surface (`TheLambdaRingOfTheScalingSurface`)

27. **Adams operations, Hecke cycles and the pole-plane splitting.** On any polar surface
    `polarPart x = (x · V)H + (x · H)V` and `prim = 1 − polarPart` are orthogonal idempotents splitting
    the surface into the pole plane and the primitive complement with pairing `−defect`
    (`polarPart_add_prim`, `pair_orthog_split`, `pair_polarPart_prim`). The Newton–Witt exponential
    `sigmaSeries g = exp(Σ_{j≥1} g(j)X^j/j)` is a `λ`-ring exponential (`hasGhost_sigmaSeries`,
    `sigmaSeries_add`) that splits any trace `(1 + q^j) + g_prim(j)` into the pole factors times
    `sigmaSeries g_prim` (`sigmaSeries_pole_split`); over `𝔽_q` this recovers
    `zetaSeries = poleZeta · hOnePoly` (`CurveDatum.sigmaSeries_pointCount_split`), with the span Adams
    operations exact isometries commuting with the splitting (`pair_spanAdams`, `polarPart_spanAdams`).
    Over `ℚ` the logarithmic translation `scaleShift t` scales the pole coordinates by
    `(e^{−t/2}, e^{t/2})` (`weilTest_scaleShift`), so the normalized Adams operators `adamsOp q` are
    exact intersection, polar and defect isometries commuting with the splitting (`pair_adamsOp`,
    `defect_adamsOp`, `polarPart_adamsOp`, `prim_adamsOp`). The Hecke correspondences
    `T_a = √a · adamsOp a` satisfy `T_a H = aH`, `T_a V = V`, and the Hecke cycles `Γ_a(g) = T_a Δ_g` obey
    the rational-scale pullback law `Γ_a(g) · Γ_b(g) = b · L(Δ_g, a/b)` (`pair_heckeCycle`), which on a
    prime tower is `p^{min(k,l)} L(Δ_g, p^{|k−l|})` (`pair_heckeCycle_pow`). The arithmetic Lefschetz
    number splits as `(a + 1)(x · H)(x · V) − √a · defect(adamsOp a x, x)` (`arithLefschetz_split`,
    `sigmaSeries_arithLefschetz_split`); narrow bumps at integer scales read the prime comb as the Hecke
    incidence (`weightedPrimeComb_scaleShift_eq_heckeIncidence`); and on the zero side `scaleShift (log q)`
    multiplies the readout at `ρ` by `q^{ρ − 1/2}` (`paperFT_scaleShift_gammaOf`). The formal structure of
    Weil's surface — Frobenius as an Adams operation, graphs as Hecke cycles, Lefschetz numbers as
    intersections — therefore exists on the scaling surface. What it lacks is still Riemann–Roch.

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
| The three-quarters modules prove that 75% of the zeros are on the line | They prove `(3/4)N` *conditionally*: on a zero-side slack `S(T) ≥ N/12`, or on the proposition `PrimeSurplusFourThirds`. The unconditional content is `(2/3 − ε)N + S(T) ≤ N₀*` with the slack retained, the `43/36` diagonal constant and the `O(T^{5/6}log²T)` cross term. |
| Adams operations make the scaling surface a Weil surface | They make it a surface with Frobenius, graphs and Lefschetz numbers; Riemann–Roch is still the missing ingredient. |
| The rank–trace form is capped at `2/3` | The form has capacity `2 − κ` (reaching `1` at `κ = 1`); `2/3` is `2 − κ(1)` from stopping pair correlation at `λ = 1` (`κ(1) = 4/3`), where double zeros and coalesced pairs share `blockA`. |

---

## 6. Questions the programme answers and the tools it builds

### 6.1 Questions

1. **Which ingredients of Weil's proof exist for `ℤ`?** The pairing, the fibres, Lefschetz,
   adjunction, Bézout positivity, Adams operations and Hecke graphs: all exact. Riemann–Roch: absent,
   and its existence with ample degrees is RH.
2. **What does the failure of the Hodge index measure?** The number of distinct zeros right of the
   line, filtered by degree, split by reflection sector; never depth or multiplicity.
3. **Which arithmetic data force the sign?** Not span data, integrality, functional equation or
   positive Euler data — the golden datum has all of them and fails. A forcing input must be
   violated by such fake data.
4. **What can a Gram functional certify without effectivity?** A proportion `2 − κ`, capped at `2/3`
   below pair correlation at `λ = 1`, with two named inputs that would reach `3/4`.
5. **What would an effectivity for `ℤ` have to be?** A cone with Riemann–Roch supply and ample
   degrees proved without the sign of the form, reducing over `𝔽_q` to Weil's.

### 6.2 Tools

Built and reusable:

- *Polar surfaces*: defect, primitive projection, four forms of the Hodge index, realizability.
- *The `𝔽_q` calibration*: curve data, span Toeplitz forms, the Pontryagin law, fake curves, Witt and
  Beurling structure.
- *The scaling surface* with its signature law and the Pontryagin law over tempered configurations,
  reflection sectors and the degree filtration.
- *Visibility calculus* of right zeros from on-line mass, local and logarithmic density.
- *The Kronecker-rank dichotomy* and exponential-polynomial recurrence.
- *Bézout positivity* through the Lévy jump form of the collar.
- *Hecke incidence*: the Cartesian law, resonators, the successor cell.
- *Rank–trace inertia* with spectral slack.
- *The `λ`-ring*: Adams operations, Hecke correspondences and cycles, arithmetic Lefschetz numbers.

To be built:

- a notion of section on the scaling surface with Riemann–Roch supply and an ampleness proof that does
  not use the sign of the form;
- an effectivity stable under the Hecke correspondences;
- the near-radical count of Landau–Widom type;
- a bound on the coupling of prime towers through the collar on rank-`P` boxes.

---

## 7. Open problems

1. **Riemann–Roch for `ℤ` — the open core (`RiemannRochForZAndTheReflectedPrimePolarLedger`).**
   Dually to the closed positive cone `S.positiveCone` (where `RiemannRochAxiom` holds
   unconditionally and `AmpleAxiom` is equivalent to `HodgeIndex`), the open positive cone
   `S.openPositiveCone` (`strictCoupledArithmeticCone V` on `scalingSubsurface V`) satisfies
   `AmpleAxiom` **unconditionally without assuming the sign of `W`**
   (`PolarSurface.openPositiveCone_ample`, `strictCoupledArithmeticCone_ample`), so the entire
   Hodge index theorem on `scalingSubsurface V` reduces to the single property
   `RiemannRochAxiom (strictCoupledArithmeticCone V)`
   (`strictCoupledArithmeticCone_riemannRoch_iff_hodgeIndex`). On `scalingSurface`, the pole-plane
   hyperbolic form `2 B(F) A(F)` is the Lorentz moment form `2 evenPoleMoment(F)² − poleCharge F`
   (`two_mul_poleB_mul_poleA_eq_lorentz_moments`), so on `oddRealTestsAt r` (`evenPoleMoment F = 0`)
   the incidence-ledger `poleCharge F = 2 A(F)²` is the negative self-intersection of the polar
   projection `A(F)(H − V)`. At every degree `r > 0` and plateau radius `R > r`, the
   Castelnuovo–Severi defect `δ(x, x)` equals the archimedean gauge budget minus
   `reflectedPrimePolarCost f r` — or equivalently minus the horizon-localized two-pole Chebyshev
   defect integral on `(0, 2r]` (`scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger`,
   `scalingSubsurface_odd_defect_eq_chebyshevDefectLedger`) — with the unconditional rate-`1/2`
   bound `δ(x, x) ≥ −78 e^r ∫ f²` (`scalingSubsurface_odd_defect_ge_neg_seventy_eight_mul_exp`).
   Exact `100%` critical-line zeros (`rightZeros zetaZeroConfig = ∅`) is unconditionally equivalent
   to `RiemannRochAxiom (strictCoupledArithmeticCone (oddRealTestsAt r))` and to reflected-prime /
   two-pole Chebyshev-defect allocation across all degrees `r > 0`
   (`rightZeros_zeta_eq_empty_iff_forall_odd_strictCoupled_riemannRoch`,
   `rightZeros_zeta_eq_empty_iff_forall_odd_chebyshevDefectAllocation`), and holds unconditionally
   past the first prime (`r ≤ 181/500`,
   `strictCoupledArithmeticCone_odd_riemannRoch_of_le_threeHundredSixtyTwoThousandths`).
2. **Near-radical count (Landau–Widom).** The two-sided law for `h⁰_ε(L)`, the dimension of
   aperture-`L` tests with `|W| ≤ ε‖f‖²`, unconditionally in its upper half, and the rate
   `−log μ(L) ≍ 2π² N(T*)/log N(T*)` for configurations on the line. Known: lower bounds
   (`zeta_weil_near_radical_dimension_smooth`, `RHTower.zeta_weil_near_radical_sharp_count`).
3. **Aperture over `ℚ`.** The degree at which `n` right zeros become visible is explicit in terms
   of on-line mass, local density and logarithmic density, with the stepwise filtration for multiple
   pairs (item 15); no degree works uniformly over all configurations. Open for `ζ`: a visibility
   degree uniform in height, which needs the local off-line density that Square-Root Threshold
   identifies as the clustering alternative.
4. **The collar between towers.** On rank-`P` boxes the towers couple through the collar and the
   pole only; bound this coupling against `Σ_p E_p` and decide positivity of the
   finite-Euler-product form on lattice tests.
5. **Effectivity from the `λ`-ring.** The Adams operations, Hecke correspondences and the pole-plane
   splitting exist (§3.9). Open: a cone of cycles stable under the Hecke correspondences, with
   nonnegative ample degree and Riemann–Roch supply, built from them; and whether the identity
   `L(x, a) = (a + 1)(x · H)(x · V) − √a · defect(adamsOp a x, x)` constrains the defect on the
   primitive part beyond what the signature law gives.
6. **Beyond `2/3`.** The constant is explained: capacity `2 − κ` at `λ = 1` (§3.8). Open: either input
   that gives `3/4` — a zero-side spectral slack `S(T) ≥ N(T, 2T)/12`, or the prime surplus
   `RHTower.PrimeSurplusFourThirds` at bandwidth `4/3` — or pair correlation beyond `λ = 1`.

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
| `TheVisibilityDegreeOfRightZeros` | visibility degree of `n` right zeros from on-line mass, local density, and logarithmic density |
| `TheKroneckerRankDichotomy` | recurrent configurations have defect `0` or `∞` |
| `TheZerosOfAnExponentialPolynomialRecur` | recurrence of zeros of exponential polynomials |
| `ResonatorKroneckerLaw` | Kronecker law of resonators, additive envelopes |
| `HeckeIncidenceCartesianLaw` | Cartesian law: the prime part is a product of towers |
| `TheResonatorRemainderIsNegative` | cross-prime remainder on resonators is negative definite |
| `TheAdjunctionConjectureMeanField` | mean-field law; no polynomial adjunction bound |
| `ThePronicWeightIsThePoleMassOfTheSuccessorCell` | pronic weight = pole mass of the successor cell |
| `TheSuccessorCollar` | collar bounds; consecutive Hecke cycles meet through the collar alone |
| `TheTwoThirdsConstantIsPairCorrelation` | `2 − κ` capacity of rank–trace inertia, coalescence indistinguishability, `2/3` from `λ = 1` pair correlation |
| `BreakingTheCoalescenceBlindSpotAndThreeQuarters` | unsplit `(P, Q)` spectral slack, `jointRankTrace23` (`(7 − 3κ)/4 = 3/4` at `κ = 4/3`), `κ = 5/4` prime-surplus & double-window routes to `75%` |
| `RiemannRochForZAndTheReflectedPrimePolarLedger` | `strictCoupledArithmeticCone` unconditional ampleness, Lorentz–polar identity, all-aperture reflected-prime / Chebyshev-defect Castelnuovo–Severi ledger, equivalence with exact `100%` critical-line zeros |
| `TheLambdaRingOfTheScalingSurface` | universal `λ`-ring series, Adams operations `adamsOp q` and Hecke cycles `heckeCycle a g` on `scalingSurface`, pole-plane splitting, narrow-bump `heckeIncidence`, zero-side eigenlaw |
