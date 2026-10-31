# Arithmetic Index Descent (AID)

Namespace `GaloisForLFunctions.ArithmeticIndexDescent`; umbrella `ArithmeticIndexDescent.lean`; 105 modules.
All results are unconditional. RH occurs only as one side of an equivalence (`riemannHypothesis_iff_*`) or a disjunct
(`RH ∨ …`); nothing assumes it. Many modules end with `#print axioms` lines.

## 1. Motivation

The RH target can be written as an index statement: the negative index of the complete Weil Gram on finite smooth families
counts right zeros, and the spline orbit index is bounded by one only under RH (SpacingScaleHarmonicAnalysis). AID studies the
negative index of the literal complete form (prime comb, Gamma term, both pole moments) from two sides:

- **zero side**: what pays the index (transverse energy, damped source work, scale increments, the critical rate);
- **source side**: how the index descends through actual arithmetic presentations (positive section spaces, projection,
  completion, cell exhaustion) and which parts of the arithmetic source the Gamma energy can pay.

The result is a precise map: Gamma pays every mixed Euler source except the growing first-prime layer, and on that layer the
pole must be spent at square-root scale.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Real Weil form | `realWeilForm`, `complexWeilMixed` | complete Weil pairing on compact real C² tests; complexified Gram = literal `weilGram` |
| Source work, increments | `doubledSourceWorkIncrement`, `quadraticWorkIncrement` | `W(2R)−W(R)`, `R²(W(2R)−W(R))` of damped source work |
| Critical energy | `xiCriticalSourceEnergy`, `quadraticIndexUnit`, `quadraticExclusionQuantum`, `resolventIndexCharge` | limit of the critical rate; certified unit per right copy; `2·unit`; `50k²−3k/2` |
| Spline index | `splineIndex` | negative index of the Weil Gram on cubic-spline translates at integer logs |
| Section projection | `arithmeticSectionProjection`, `finiteSectionProjection` | unique Weil projection onto a narrow arithmetic section span |
| Completion | `sectionCompletionEnergy`, `sectionCompletionForm`, `completedSectionResidualForm` | sup of projection energies; PSD removal form; `W − removal` |
| Source kernel | `weilSourceKernel`, `sourceKernelEnergy` | continuous kernel with `W(p,g) = Re∫p·K_g`; `∫_s|K_g|²` |
| Gamma collar | `sourceCollarCorrelation`, `orderedGammaTail`, `orderedSourceLagWeight` | two-sided mixed correlation; Gamma tail after its first mode; `e^{−h/2}·corr` |
| Gamma Schur weight | `gammaBoundarySchurWeight`, `gammaBoundaryPairReserveDensity` | `e^{t/2}/√(e^{2t}−1)`; exact square reserve density |
| Cell capacity | `cellGammaWeight` | `log(1/w_a)` for the pair cell `a` |
| Mixed Euler sources | `integerMixedSource`, `primeEulerMixedSource`, `finiteEulerMixedSource`, `higherPrimePowerMixedSource`, `oddHigherPrimePowerMixedSource` | coarse/detail mixed prime-power terms on complete cell profiles |
| Square sources | `squarePrimeSource`, `squarePrimeMixedSource`, `centeredSquarePrimeSource` | `2Σ(Λ(n)/n)·corr(2 log n)` and its mixed/centred parts |
| Symbols | `gammaIncrementSymbol`, `squarePrimeRegularSymbol` | Gamma jump symbol; regular part of the even-power boundary |
| Joint forms | `fullDetailCoupledSourceForm`, `fullPolarNonfirstSourceForm`, `fullSquarePolarSourceForm`, `haarLogarithmicMass`, `fullDetailPrimeGap` | successive joint payment forms; `Σ cellGammaWeight·haarMass·d²`; `1 − 1/√2` |
| Head coupling | `headCoupling`, `headCouplingLimit`, `headTrace`, `fullPrimeWindowMixedPole`, `fullPrimeWindowRemainder` | Euler head `p ≤ Y` on detail × far window; its `√Y` limit; pole cross terms |
| Graph carriers | `realTestGraphLift`, `closedSectionGraph`, `closedFixedLogCellGraph`, `graphWeilOperator` | inverse Doob lift into the complete source graph; closed carriers |
| Moving band | `movingArithmeticBandTest`, `movingBandFloor` | upper band `N/2 ≤ n ≤ N` recentred by `−log N` |

External: `divisorTransverseEnergy`, `xiCopyTransverseEnergy`, `xiDampedSourceWork`, `xiTaperedSourceWork`, `atomSpacing`
(ArithmeticElectrostatics); `arithmeticSectionTests`, `fullSectionRatio`, `sectionReserve`, `completePairProfile`,
`averageSectionProfile`, `haarSectionProfile`, `haarProfile`, `haarMass`, `roughWeil`, `haarPrimeEnergy`, `completeGammaMixed`,
`weilGram` (ArithmeticCastelnuovoSeveri); `logCellWidth` (BiarithmeticGaugeGeometry); `levyEnergy`, `ccmGammaBoundaryCLM`,
`archLevyDensity`, `SourceGraph`, `weilForm`, `weilBilin`, `coshHalfMoment`, `sinhHalfMoment` (RHTower); `hermNegIndex`
(HTGeometry); `primePolarCutoffSymbol` (ArithmeticCompensationTheory).

## 3. Language

- **Index**: Hermitian negative index of a complete Weil Gram (not the positive index of an intersection form).
- **Descent**: transport of the literal complete form through projection, completion or limits; never a corrected form.
- **Reserve**: a source-proved nonnegative quantity: square-mass floor, width reserve, Gamma share, logarithmic detail mass,
  Gamma square reserve.
- **Payment**: an inequality absorbing an adverse term in a reserve.
- **Complete profile**: `F = g + h`, pair averages `g` (coarse `q`) plus balanced Haar details `h` (detail `d`), horizon `X`.
- **Detail head `A`**: the coordinates `d_a`, `a < A`. **Uniform finite index**: every negative subspace injects into the head
  readouts plus at most two scalar readouts (sinh moment, ordinary mean), uniformly in horizon, family size and profiles.
- **Gamma-small**: `|source tail| ≤ δ·Γ(F)` after a detail head, with `Γ = levyEnergy` of the untruncated profile.
- **Damping then taper**: order of limits for finite source-work readings.
- **Full prime window**: all prime powers `m ≤ (b+1)Y` visible to a detail and a window at `log Y`.

## 4. Mechanisms

**A. Zero side: the index is paid by energy and work**

1. **Energy.** Negative index ≤ transverse energy; strictly below it when nonzero (horizontal partner gives 1, FE reflection adds
   the diagonal angle). RH ⇔ energy ≤ 2.
2. **Work.** Damped source work increases to copy energy; bounded ⇔ finite off-line support ⇔ bounded spline indices; RH ⇔
   cofinally work ≤ 2. Every amount below the index is eventually exceeded by finite tapered work.
3. **Scale.** Above the zero-free height gap `|Im ρ| ≥ 4` the damping velocity is relatively Lipschitz, so reflected pair work is
   monotone in scale. Doubling gap `21/100`, own-height gap `39/100`, quartet quantum `39/50`; RH ⇔ every increment ≤ `39/50`.
4. **Critical rate.** `R²(W(2R)−W(R))` is convex-secant hence monotone (convexity in inverse-square scale), converges to the
   critical energy, and gives a trichotomy (RH / finite exceptions with limit above the quantum / infinite and → ∞). Each negative
   square costs `quadraticIndexUnit`; strip-edge resolvent mass `≤ 3/100` makes the cost quadratic, `50k² − 3k/2`.

**B. Exact descent through positive sections**

5. **Sections.** Narrow section Grams have only presentation radicals; mixed blocks lie in their range; the Weil projection is
   unique with residual identity `W(g−Pg, h−Ph) = W(g,h) − W(Pg,Ph)`. Haynsworth congruence for range-compatible singular blocks
   gives `negIndex(sections ⊔ g) = negIndex(residuals)`.
6. **Cost.** `W(p,g) = Re∫p·K_g` with continuous `K_g`: window cost `2LC²`, cost `≤ ∫_{cells}|K_g|²`, vanishing `O(w)` as cells shrink,
   divided by unused reserve `1 + ((1−a)/8)·weight`; at full width a strict reserve `1/8 − r(e^r+1) > 0` survives.
7. **Completion.** Finite projection energies are monotone and bounded; polarization gives a PSD removal form; the residual
   `W − removal` vanishes on all sections, its index is attained at a finite stage, equals an actual smooth Weil Gram index, and
   is paid by work.
8. **Finite-Gram descent.** Entrywise limits and rectangular pullbacks cannot lose negative squares. Complete-cell Grams converge
   entrywise to the Weil Gram, so they eventually carry every finite index (lower bound only).
9. **Graph.** The inverse Doob lift preserves the full Weil pairing; `‖lift f‖² ≤ W(f) + penalty·∫f²·cosh(u/2)/K(u)`. Coercive
   closed carriers have bounded Weil projections (Lax–Milgram compression) equal to the finite-section limits.

**C. Gamma boundary and ordered collars**

10. **Collar.** Polarized Lévy identity: on disjoint supports the Gamma cross term is minus the collar `∫f g(·+x) + f(·+x)g`
    against `ω`; a gap `d` leaves the Lévy tail `∫_d^∞ ω`; touching supports give the half-line Hankel operator.
11. **Sharp boundary.** The Schur weight `e^{t/2}/√(e^{2t}−1)` turns the Gamma row into the Carleman row: `‖Γ‖ = π/2` exactly,
    `(π/2)‖f‖² − Re⟨f,Γf⟩` is an exact weighted square, strict for `f ≠ 0`, no norm maximizer, truncations lose at most 16.
12. **Polar cancellation.** `ω(h) = e^{−h/2} + e^{−2h}ω(h)`; the first mode is exactly the inward polar product. The tail is the
    Gamma pairing of `e^{±2(u−b)}`-tilted profiles: `= (π/4)(boundary masses) − square reserve`. Abel summation turns the remaining
    pole plus prime part into a centred Chebyshev defect `−∫(ψ-error − c)·q'` for any `c`.

**D. Cells and carriers**

13. **Mixed payment.** On a window: prime part is a finite sum (`C_R = Σ_{n<e^{2R}} Λ/√n`), poles cost `2Re^R`, Gamma cross costs the
    Lévy tail (gap) or `π` (touching); rescaling gives `2|W(f,g)| ≤ ε‖f‖² + D‖g‖²`.
14. **Short cells.** A single cell of width `w` has floor `log(1/w) − const`, so short cells pay any mass charge; a new short cell
    pays its interaction and keeps `(1−ε)` of the old floor.
15. **Fixed widths.** For strictly increasing centres, one width sequence (decreasing reserve `1 + 1/(n+1)`) makes every finite
    prefix coercive, also for any continuous weight `ω ≥ 1`, hence `‖lift‖² ≤ (1+ε)W`. The closed integer-log carrier is proper
    (cusp escape lies outside), has a bounded Weil projection, and leaves the infinite theta radical in its complement.
16. **Moving bands.** The recentred upper band has floor `~ log N` in a fixed window, so energy-unit band sections become
    invisible to every fixed probe.

**E. Mixed Euler sources on complete cells**

17. **Gamma controls details.** `Γ(F) ≥ Σ cellGammaWeight·Var_pair(F) ≥ Σ log a·haarMass·d_a²`; `Γ(g) + Γ(h) ≤ C·Γ(F)`; translation
    invariance makes every translated detail probe `≤ Γ(F)/cellGammaWeight(A)`; unit-Gamma details are precompact.
18. **Integer incidence.** At lag `log m` the coarse→detail orientation vanishes; even `m`: detail–detail vanishes by parity; odd
    `m`: `(2a+1)m = 2b+1` forces `a ≤ b`. Hence each mixed lag costs `≤ 2(2Λ(m)/√m)·Γ/cellGammaWeight(A)`.
19. **Summable layers.** Euler factor at `p` costs `2 log p/(√p − 1)`; exponents ≥ 3 are summable over all primes; prime two
    reads coarse differences paid by the Gamma mean graph with `1/log A` tail decay. Each layer has uniform finite index.
20. **Depth law.** `cost(P) ≤ log A ⇒ index ≤ A`; the head `p ≤ Y` costs `≤ 32√Y log Y`, so depth `A` reaches `Y ≈ (log A)²`. The
    Euler costs are not summable: no depth pays the whole first-prime layer.
21. **Growing head.** The head's edge at `m = Y` couples detail `a` to the window at `log Y + [log 2b, log(2b+2))` with strength
    `√Y·L[a,b]` (window PNT); `L` is lower triangular with diagonal `−4√(2a)J_a < 0`. Coarse coefficients `(s/√Y)Lᵀx` cost `O(1/Y)`
    in Gamma and gain `sσ‖x‖²`: unbounded negative index, already for heads `p ≤ (log N)^A`.
22. **Pole cancellation.** Including every prime power in the full window, `(all-prime mixed source − mixed pole)/√Y → 0`: the
    growing-head coupling is exactly the pole's square-root term.
23. **Squares.** Even-power source = regular Fourier boundary + `(1/2)(∫u)²`. Symbol gap `Γsym − regular = γ + log 4π + π/2 −
    π/(2cosh πt) − 2/(1+4t²) + 2Re(ξ'/ξ)(1+2it) ≥ γ` (zero-free edge, no RH); `Re ξ'/ξ(1+iT) ≥ c log T` retains a fixed Gamma share;
    `ζ'/ζ` sublogarithmic on `Re s = 1` makes the regular symbol `≤ εΓsym` at infinity.
24. **Haar prime diagonal.** Directed prime matrix: rows `≤ 16 haarMass`, large-multiplier columns `≤ log(2b+1)/√N` (divisor
    identity); bounded multipliers use upward incidence. All prime powers on details have uniform finite heads.
25. **Joint chain.** One Gamma reserve pays, in order: full Haar Weil diagonal with Gamma coupling (gap `1 − 1/√2`), mixed exponents
    ≥ 2, the full original pole (one sinh readout), the coarse square source (one mean readout): index `≤ A`, `A+1`, `A+2`.
26. **Prime–polar cutoff.** `primeSum − poles` equals a cutoff multiplier pairing; for support `[−R,R]` it is `≤ εe^R(Γ + ∫f²)`.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Index ≤ transverse energy, strict; RH ⇔ energy ≤ 2 | `negIndex_eq_zero_or_lt_divisorTransverseEnergy`, `riemannHypothesis_iff_divisorTransverseEnergy_le_two` | proved |
| Bounded work ⇔ finite support ⇔ bounded spline index | `eventually_bounded_dampedSourceWork_iff`, `bounded_splineIndex_iff_offLineSupport_finite` | proved |
| Quartet quantum; RH ⇔ increments ≤ 39/50 | `offLineQuartet_strict_increment`, `riemannHypothesis_iff_all_scale_increments_le_quantum` | proved |
| Critical-rate trichotomy and canonical energy | `quadratic_source_rate_trichotomy`, `quadraticWorkIncrement_tendsto_criticalEnergy` | proved |
| Quadratic index cost | `resolventIndexCharge` bounds in `TheSourceBudgetMakesTheIndexCostQuadratic` | proved |
| Exact section descent | `negIndex_weilGram_section_extension_eq_residual` | proved |
| Completion reaches the index at a finite stage | `eventually_negIndex_completedSectionResidual_eq`, `exists_actual_weilGram_with_completion_index` | proved |
| Complete-cell index capture | `exists_completeCell_weilGram_index_capture` | proved (lower bound) |
| Sharp Gamma boundary | `norm_ccmGammaBoundaryCLM_eq_pi_half`, `gammaBoundary_quadratic_deficit`, `norm_ccmGammaBoundaryCLM_apply_lt` | proved |
| Ordered source = centred Chebyshev + Gamma reserve | `realWeilForm_ordered_eq_chebyshev_add_gammaReserve` | proved |
| Fixed widths control the source graph | `exists_fixedCellWidths_coercive`, `exists_fixedLogCellWidths_graph_coercive` | proved |
| Integer-log carrier projection; theta radical survives | `exists_fixedLogCellWeilProjection`, `exists_infinite_critical_fixedLogCellResidual` | proved |
| Finite Euler sets and higher powers: uniform index | `exists_uniform_finiteEulerGamma_negative_dimension`, `exists_uniform_higherPrimePowerGamma_negative_dimension` | proved |
| Depth law and non-summable first layer | `finiteEulerGamma_negative_dimension_le`, `exists_eulerHead_cost_gt` | proved |
| Growing heads have unbounded index | `not_exists_uniform_eulerHead_index`, `eventually_logPowerHead_negative_family` | proved |
| Full prime window cancels the pole | `tendsto_allPrimesMixedSource_sub_pole_div_sqrt`, `fullPrimeWindowRemainder_uniform_finite_family` | proved (fixed families) |
| Square-prime Gamma gap | `eulerConstant_le_gammaIncrement_sub_squarePrimeRegular`, `exists_squarePrime_retained_gamma_complete` | proved |
| Joint payment with full pole and square source | `exists_uniform_fullPolarNonfirst_negative_dimension`, `exists_uniform_fullSquarePolar_negative_dimension` | proved |
| Prime–polar Gamma bound | `exists_primePolar_gamma_bound_bv` | proved (aperture factor `e^R`) |
| Fixed coarse cells | `exists_uniform_fixedCoarse_fullWeil_negative_dimension` | proved |

## 6. Tools

**Developed**
- Singular index descent: range compatibility, Haynsworth splitting, rectangular pullback, entrywise index survival.
- Section projection calculus: canonical completion, PSD removal form, residual descent, source-kernel cost bounds.
- Graph embedding of compact tests with exact Weil pairing; coercive compression ⇒ bounded Weil projections.
- Gamma boundary toolkit: Lévy polarization, collar bounds, exact Schur weight, square reserve, tilted-profile tail identity.
- Ordered Chebyshev identity: lag weight, Abel summation with arbitrary centring.
- Complete-cell Gamma accounting: cell capacity `log(1/w_a)`, translated-detail bound, integer incidence lemmas.
- Head/window asymptotics: window PNT `Σ_{m≤x}Λ/√m ~ 2√x` on windows, proper-power bound `144 M^{1/4}`, head reindexing.
- Readout injection lemma pattern for uniform finite index.

**To build**
- An upper estimate for complete-cell negative indices.
- Uniform full-window pole cancellation over growing detail and window indices.
- Arithmetic upper bounds for `W(2R)−W(R)` or the critical rate.
- Prime–polar cancellation without the aperture factor.

## 7. Open questions

1. Is the negative index of complete-cell Grams bounded? Index capture would transfer any bound to every finite family; bound
   one is RH.
2. Can the first-prime coarse layer be paid jointly with the pole uniformly in the cell indices? Fixed families cancel at
   `o(√Y)`; growing heads alone have unbounded index.
3. Is there an arithmetic upper estimate for scale increments below `39/50`, or for the critical rate below the quantum?
4. Can `|primeSum − poles| ≤ ε(Γ + ∫f²)` hold without `e^R`?
5. Which fixed-width carriers are dense enough to see off-line structure, given that the closed integer-log carrier misses the
   cusp escape?
6. Do the coarse odd source and coarse archimedean mass admit a payment of the same kind as the square source?

## 8. Traps

| Trap | Fact |
|---|---|
| Gamma pays all mixed Euler sources | Euler costs `2log p/(√p−1)` are not summable; depth `A` reaches only `p ≲ (log A)²` |
| Uniform index for each finite head gives a uniform bound | Growing heads have unbounded index; the pole must be included |
| Index capture bounds complete-cell indices | It is a lower bound: late cell Grams carry at least the Weil index |
| `RH ⇔ …` equivalences are progress toward RH | They identify closed targets; no upper bound on work is proved |
| Completed residual is a new form | It is `W − (PSD removal)`, with the index of an actual smooth Weil Gram |
| `‖Γ‖ = π/2` with strict deficit gives a gap | No maximizer and no uniform gap; truncations approach `π/2` |
| The square Gamma gap uses RH | It uses only `Re ξ'/ξ ≥ 0` on `Re s ≥ 1` and the zero-free edge |
| Fixed-width carriers exhaust the source graph | The closed integer-log carrier is proper; the cusp escape lies outside |
| Moving bands invisible to probes means positivity | It means decoupling; their own index is not controlled |
| Singular section Grams need inversion | Range compatibility suffices; no Gram inverse is used |
| Shrinking cells is free | Removal vanishes at fixed `N`, not uniformly in `N` |

## 9. Context

**Uses**

| Programme | Imports | For |
|---|---|---|
| RHTower | 47 | Weil functional, CCM Gamma boundary, CHMD source graph and theta modes, ξ log-derivative, zero counts, window PNT |
| ArithmeticCastelnuovoSeveri | 32 | narrow sections, log cells, Haar profiles, complete-cell Gamma accounting, Weil index law |
| HTGeometry | 11 | Hermitian inertia, Haynsworth, Carleman weight, coercive operators, digamma |
| ArithmeticElectrostatics | 4 | transverse energy, source work, atom spacing, prime external field |
| SpacingScaleHarmonicAnalysis | 3 | spline index law, archimedean pairing of atoms |
| BezoutValuationIncidence | 2 | prime-power Dirichlet sums |
| ArithmeticCompensationTheory | 2 | prime–polar cutoff symbol |
| SelectiveMultiscaleArithmeticPositivity, BiScaleUncertainty, ArithmeticIncidencePositivity | 1 each | pole hyperplane; probe Parseval; lag Chebyshev Abel summation |

**Used by**

| Programme | Modules | For |
|---|---|---|
| SignedArithmeticHodgeTheory | 6 | dyadic Euler tail, generator heads, Schur error bounds, compact details |
| SelectiveMultiscaleArithmeticPositivity | 2 | level coupling through the Chebyshev error |
| HeckeKreinToeplitz, TransMetzlerWeilPositivity, SpacingScaleHarmonicAnalysis, ArithmeticCastelnuovoSeveri | 1 each | index-is-energy; zero-side stratum; ordered cutoff; Haar smooth effectivity |

| Neighbour | Relation |
|---|---|
| ArithmeticElectrostatics | owns transverse energy and work; AID turns them into index payments |
| ArithmeticCastelnuovoSeveri | owns sections and cells; AID descends the index through them (mutual import) |
| SpacingScaleHarmonicAnalysis | spline index endpoint; AID matches its finite stratum |
| SignedArithmeticHodgeTheory | consumes the Euler-tail and head machinery |
| ArithmeticCompensationTheory | supplies the prime–polar cutoff; AID adds the Gamma norm |

## 10. Big picture

AID says the RH problem, in index form, has a sharp seam. Everything except the first-prime coarse layer is paid by the Gamma
energy: higher powers, squares, finite prime sets, all detail self-interactions, and the full pole with only one or two scalar
readouts lost. The index descends exactly through sections, completions and limits, so no information is lost in the
presentation itself. On the zero side, every negative square has a quantized price in energy, work and critical rate.

The seam is the first-prime layer. Its cost grows like `√Y`, so Gamma can pay heads only up to `(log A)²`, and a growing head
alone creates unbounded index. That growth is exactly the pole's square-root term: with every prime power in the window, the two
cancel. The open problem is this cancellation with uniform control, a square-root prime count matched against the pole. Any RH
proof along these lines must exploit arithmetic cancellation between primes and pole; positivity of separate pieces cannot
suffice.
