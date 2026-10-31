# Signed Arithmetic Hodge Theory (SAHT)

Namespace `GaloisForLFunctions.SignedArithmeticHodgeTheory`; umbrella `SignedArithmeticHodgeTheory.lean`; 42 modules.
All results are unconditional; no RH-type input. Most modules end with `#print axioms` lines. "Hodge" means signed
orthogonal decomposition of the complete Weil form against a paid positive carrier, not a cohomology theory.

## 1. Motivation

ArithmeticIndexDescent supplies a positive arithmetic carrier (the closed integer-log cell carrier) with a bounded Weil
projection, and shows that the Gamma energy pays most mixed Euler sources on complete cell profiles. The open parts are the
signed complement and the passage from finitely many detail labels to whole translation orbits. SAHT studies three things:

- the exact algebra of the signed complement (residual identities, one stationarity budget, the radical);
- the complete-cell space as a dyadic clock, so cutoffs can keep every translation level of finitely many generators;
- quantitative budgets for Ramanujan modal families in the prime matrix.

The goal is to replace "finite head of detail coordinates" by "finitely many complete generator orbits" with the same original
Gamma reserve, then pay all Euler layers that admit absolute or signed payment on that object.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Residual, stationarity | `arithmeticResidual`, `arithmeticStationarity`, `familyStationarity` | `1 − P` for the carrier projection `P`; `D = proj_K ∘ A` (`A` = Weil operator) |
| Complement, radical | `arithmeticComplement`, `arithmeticWeilRadical` | `ker P`; `ker A` |
| Scale transport | `sourceTranslate`, `translatedSourceGraph`, `apertureScaleTransport` | translation of compact tests; its extension to completed apertures |
| Ramanujan budgets | `ramanujanPrimeResidual`, `primeMertensRemainderProfile`, `primeMertensSquareBudget`, `ramanujanResidualConductorCost` | prime-row residual of a modal profile; one Mertens/floor remainder; `√φ(m)(1 + 4 log m)` |
| Dyadic clock | `logCellDyadicIsometry`, `logCellDyadicWandering`, `logCellDyadicDetail`, `logCellDyadicBasis`, `logCellDyadicCoordinates` | weighted shift `W e_a = α_a e_{2a} + β_a e_{2a+1}`; wandering space; balanced detail; Hilbert basis on `ℕ × Option ℕ+` |
| Haar readout | `logCellHaarReadout`, `logCellDyadicParentVariance`, `logCellAncestorWeight` | `√haarMass·(child mean difference)`; parent variance; `⌊log₂ a⌋ + 1` |
| Generator cutoff | `logCellGeneratorHead`, `wholeLineGeneratorTail` | keeps root and labels `< A` at every level; its physical complement |
| Stopping cells | `logCellStoppingAncestor`, `logCellStoppingVector` | ascend `n ↦ ⌊n/2⌋` until label `< 2A` |
| Physical head/tail | `finiteLogCellProfile`, `actualGeneratorHeadProfile`, `actualGeneratorTailProfile` | finite cell source; its block-average head; the rest |
| Correlations | `wholeLineTranslationCorrelation`, `dyadicEulerCorrelation`, `wholeLinePrimeEulerCorrelation`, `wholeLineHigherEulerCorrelation` | `Re⟨T_tF, F⟩`; prime-2, prime-`p`, cube-and-higher Euler sums |
| Coefficient tails | `criticalEulerTailWeight` | `2Λ(p^{k+r+1})/√p^{k+r+1}` over all primes |
| Stopping grid | `stoppingGridWidth`, `stoppingGridBoundary`, `stoppingGammaKernelConstant` | padded graded partition; `32e²` |

External: `fixedLogCellWeilProjection`, `closedFixedLogCellGraph`, `graphWeilOperator`, `realTestGraphLift`, `cellGammaWeight`,
`squarePrimeSource`, `centeredSquarePrimeSource`, `primeTwoPowerWeight`, `primePowerMixedWeight` (ArithmeticIndexDescent);
`haarProfile`, `haarMass`, `completePairProfile`, `wholeCellProfile` (ArithmeticCastelnuovoSeveri); `ramanujanPoleProfile`,
`renormalizedPrimeEnergy` (RenormalizedArithmeticPotentialTheory); `levyEnergy`, `SourceGraph`, `weilForm`, `weilBilin`,
`logCellShift`, `logCellEmbedding` (RHTower).

## 3. Language

- **Paid carrier**: a closed subspace with a proved coercive Weil estimate and bounded Weil projection.
- **Stationarity**: the Weil operator restricted to the carrier; it is the only charge for trial corrections.
- **Whole-orbit cutoff**: keep a generator label at every dyadic level, never truncate levels.
- **Generator / level**: coordinates `(j, a)` of the dyadic basis; `a` is the Haar label, `j` the translation power of `log 2`.
- **Original Gamma**: `levyEnergy` of the untruncated source; every bound is stated in it.
- **Stopping block**: integers with the same quotient `⌊m/2^j⌋ = a`, physical interval `j log 2 + [log a, log(a+1))`.
- **Head / tail**: `P_A f` and `f − P_A f` as actual compact BV profiles.

## 4. Mechanisms

**A. Signed complement**

1. **Trial calculus.** For `u` in the carrier, `W(x − u) = W(res x) + W(Px − u)`; `W(Px) ≤ 2‖Dx‖²`, `‖Px − u‖ ≤ 2‖D(x − u)‖`; mixed
   entries `|W(x−u, y−v) − W(res x, res y)| ≤ 2‖D(x−u)‖‖D(y−v)‖`. A family is charged once by `‖D(F − U)‖²`.
2. **Radical.** `D x = 0 ⇔ x ∈ ker P`; `ker A ⊆ ker P`; restricting to the complement creates no new radical; the theta family
   gives infinitely many independent radical vectors.
3. **Escape.** The theta kernel decays faster than every exponential, so the graph mass weight dominates `e^{B|u|}` for all `B`.
   Translation keeps the Weil value and pushes the graph norm past every exponential rate, also in the residual; no amplitude
   renormalization fixes this. On bounded windows and bounded shifts, translation is a two-sided bounded map and extends to
   completed apertures, preserving every Weil pairing and multiplying strip readouts by `e^{izt}`.

**B. Ramanujan modal budgets**

4. **Gram.** Periodic Abel summation: `|Σ_{n≤N} ρ_mρ_l − δ_{ml}H_N| ≤ 2ml`, so families cost `(1 + 2Σm²)Σc²` against `log N·Σc²`.
5. **Residual.** Conductor correction `≤ 4φ(m) log m/y`; every row residual is `cost(m)·profile(⌊N/n⌋)/√n` with one Mertens/floor
   profile; the square budget is bounded uniformly in `N` (Mertens `e^{−c√log}` decay + Wiener kernel `≤ 1 + 2π²`).
6. **Capture.** `ρ_m(n)² ≤ φ(m)/n` bounds local mass; fixed modal spans and bounded prime-energy sublevels lose all normalized
   mass on every fixed integer window.

**C. Dyadic clock**

7. **Wold decomposition.** `W` is a pure isometry (range of `W^j` vanishes below `2^j`); wandering levels are orthogonal and dense.
   `{e_1} ∪ {balanced details}` is a Hilbert basis of the wandering space; all levels give `ℓ²(ℕ+) ≅ ℓ²(ℕ × Option ℕ+)`.
8. **Physical identity.** `√haarMass·detail_a` embeds as `haarAtom a`; level `j` is literal translation by `j log 2`; Hilbert
   coordinates of an actual source are its translated Haar readouts.
9. **Arithmetic action.** `T_p` commutes with `W`; its level matrix is lower triangular and Toeplitz; prime two shifts levels.

**D. Gamma on the dyadic tree**

10. **Sibling payment.** `Var(parent) = Var(L) + Var(R) + parallel·(mean difference)²`; children of log cells keep `≥ 1/4` of the
    width, so a sibling rectangle pays `Var/8`. Floor labels make all sibling rectangles disjoint across levels: `Σ Var ≤ 16Γ`.
11. **Square function.** Variance flow along orbits counts every ancestor once: `Σ (1 + log a)·readout² ≤ 32Γ`; high labels `a ≥ A`
    cost `32Γ/(1 + log A)` summed over all levels.
12. **Non-compactness.** Each fixed level of unit-Gamma details is compact, but one generator's orbit is an infinite orthogonal
    family of equal Gamma: whole orbits must be kept.

**E. Orbit cutoffs and Euler layers**

13. **Exact splitting.** `P_A` commutes with every `W^k`, so `⟨W^kx,x⟩ − ⟨W^kP_Ax,P_Ax⟩ = ⟨W^k(x−P_Ax), x−P_Ax⟩`. A tail vector reads
    only the other source's tail; translation preserves Γ; hence every real-lag correlation error is `≤ 96Γ/(1 + log A)`.
14. **Layers.** Prime two: `(2 log 2/(√2−1))·32Γ/(1 + log A)`. Fixed finite prime sets: `Σ_P 2 log p/(√p−1)·96Γ/(1 + log A)`. All
    cubes and higher of all primes: one total `H < ∞`. Absolute coefficient mass is summable over all primes exactly from cubes on;
    first powers and squares diverge.
15. **Stopping averages.** `P_A` fixes cells below `2A`; each cell projects onto its stopping cell; the head's physical height is the
    log-length weighted mean over the stopping block. The head preserves the integral, the tail has mean zero and is
    L²-orthogonal to the head.
16. **Gamma stability.** The stopping grid has widths `≤ 1` and adjacent ratio `≤ 3`; comparable kernels on touching and separated
    intervals plus zero padding give `Γ(head) ≤ 32e²Γ`, `Γ(head) + Γ(tail) ≤ (2 + 96e²)Γ`.
17. **Squares.** Centering corrections cancel on head/tail; the zero-mean tail's square-source error is its square mass. With
    stability, `|S_even(f) − S_even(head)| ≤ (ε + C_ε/(1 + log A))Γ(f)`.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Certified residual bounds | `arithmetic_trial_energy_bounds`, `arithmetic_trial_mixed_error`, `family_mixed_error_le_opNorm` | proved |
| Complement keeps exactly the Weil radical | `complement_radical_iff`, `exists_infinite_arithmeticWeilRadical` | proved |
| Translation escapes every exponential graph bound | `translatedSourceGraph_all_exponential_lower_bounds`, `translatedSourceGraph_eventually_outside_carrier` | proved |
| Faithful transport on completed apertures | `weilBilin_apertureScaleTransport`, `apertureScaleTransport_injective` | proved |
| Horizon-uniform Ramanujan residual budget | `exists_uniform_ramanujanPrimeResidual_family_bound` | proved |
| Bounded prime energy escapes fixed windows | `eventually_primeHorizonWindowMass_le_of_energy_le` | proved |
| Dyadic coordinates of the cell space | `logCellDyadic_wandering_complete`, `logCellDyadicWanderingBasis`, `logCellDyadicCoordinates` | proved |
| Details are the physical Haar sources | `sqrt_haarMass_smul_logCellEmbedding_detail`, `physicalLogCellCoordinates_detail` | proved |
| One Gamma reserve for all parent variances | `sum_logCellDyadicParentVariance_le`, `sum_log_weight_readout_sq_le` | proved |
| Orbits are not compact | `not_totallyBounded_firstHaarTranslationOrbit` | proved |
| All-lag tail bound | `abs_allLevel_translation_head_error_le` | proved |
| Prime-two, finite sets, cubes and higher | `exists_physicalDyadicEuler_finite_generator_approximation`, `exists_finiteEuler_allLevel_generator_approximation`, `exists_allPrimeHigherEuler_allLevel_generator_approximation` | proved |
| Absolute coefficient threshold at cubes | `summable_criticalEulerTailWeight_iff` | proved |
| Head is a stopping-interval mean | `logCellGeneratorHead_physicalHeight`, `actualGeneratorHead_eq_intervalMean` | proved |
| Uniform head/tail Gamma stability | `actualGeneratorHead_tail_gamma_le` | proved |
| Complete even-power approximation | `exists_allEvenPrimePowers_generator_approximation` | proved |

## 6. Tools

**Developed**
- Stationarity calculus for trial corrections on a coercive carrier.
- Dyadic Wold coordinates with exact physical Haar identification and arithmetic level matrices.
- Sibling-rectangle Gamma allocation, variance flow and the logarithmic Haar square function.
- Whole-orbit cutoffs with explicit stopping-block matrices; head/tail as BV profiles.
- Graded-grid Gamma averaging bound (touching-boundary defects, gap comparison, zero padding).
- Ramanujan Gram, residual and capture budgets with explicit conductor costs.

**To build**
- A payment for the first-prime layer on whole orbits, jointly with both exponential poles.
- A sign or index bound on the retained generator orbits.
- Uniform stationarity smallness for growing Ramanujan families in the full source graph.
- An arithmetic upper bound on the critical source energy.

## 7. Open questions

1. Can the first-prime and square layers, whose absolute coefficient mass diverges, be paid on whole orbits by cancellation
   with the poles?
2. What is the Weil sign on the span of finitely many complete generator orbits?
3. Can growing Ramanujan families make the carrier stationarity uniformly small while keeping Gamma and both poles?
4. Is there a moving-coordinate norm in which escaping modes and translated orbits stay controlled?
5. Does the dyadic clock admit a twin for odd primes with comparable level structure?

## 8. Traps

| Trap | Fact |
|---|---|
| Finite detail heads give finite-dimensional approximation | Each label's orbit is infinite and non-compact; only whole orbits are controlled |
| Gamma of the cutoff head is automatic | It needs the graded-grid averaging bound; constant `2 + 96e²` |
| Absolute coefficient payment covers all layers | It works exactly from cubes on; first powers and squares diverge |
| A null vector is a negative direction | The complement keeps the radical; no graph floor on it |
| Translation is bounded on the source graph | Only on bounded windows and shifts; globally it escapes every exponential rate |
| The sparse shift `e_m ↦ e_{2m}` is the cell clock | The clock is the weighted shift `α e_{2m} + β e_{2m+1}` |
| Ordinary mean zero is a pole condition | Mean, discrete pole and the two exponential moments are different |
| Prime-matrix positivity is Weil positivity | Gamma and both poles are outside the prime matrix |
| Bounded prime energy keeps mass locally | It escapes every fixed integer window |

## 9. Context

**Uses**

| Programme | Imports | For |
|---|---|---|
| ArithmeticCastelnuovoSeveri | 9 | Haar cells, interval variance, Gamma capacity and exterior subsets, finite-cell arithmetic form |
| RHTower | 8 | CHMD source graph and theta modes, log-cell shifts, Mertens, CCM remainder |
| ArithmeticIndexDescent | 6 | carrier projection, Euler mixed weights, compact details, centred square bounds |
| SpacingScaleHarmonicAnalysis | 3 | Gamma translation invariance, archimedean pairing, constant-one self-energy |
| RenormalizedArithmeticPotentialTheory | 3 | Ramanujan profiles, quasimodes, prime-energy approximation |
| HTGeometry | 3 | partial summation, dyadic sibling partition, coordinate projections |
| PNTPlus | 1 | Wiener kernel bound |

**Used by**

| Programme | Modules | For |
|---|---|---|
| CriticalArithmeticCorrelationTheory | 3 | conductor residuals and packets |
| SuccessorShellArithmetic | 2 | Ramanujan divisor moments, nonpolar joint cancellation |
| CompletedArithmeticForms | 2 | Weil polynomial residual, growing packets |
| `MainTheorems.lean` | 1 | aggregation |

| Neighbour | Relation |
|---|---|
| ArithmeticIndexDescent | supplies the carrier and Euler layers; SAHT lifts its finite heads to whole orbits |
| ArithmeticCastelnuovoSeveri | owns cells and Haar profiles; SAHT gives them dyadic coordinates |
| RenormalizedArithmeticPotentialTheory | owns modal profiles; SAHT gives horizon-uniform budgets |

## 10. Big picture

SAHT shows that the cell space carries a canonical dyadic structure in which the prime two acts as a shift and every Haar
coefficient is a literal physical readout. In these coordinates one original Gamma reserve pays every layer of the Euler
product that has finite absolute coefficient mass, and also the even powers by signed compensation, without truncating any
translation level. The complement of the positive carrier retains exactly the global null directions, so nothing is lost by
removing the carrier.

The lesson for the RH programme is a sharp split. Everything with summable coefficient mass, and the squares, is now paid on
objects that keep all translation levels. What remains is the first-prime layer together with the two exponential poles, and
the sign on the retained orbits. These cannot be reached by absolute estimates; they require cancellation between primes and
poles on infinite-dimensional, non-compact orbit spaces.
