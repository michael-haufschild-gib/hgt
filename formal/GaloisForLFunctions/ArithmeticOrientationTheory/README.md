# Arithmetic Orientation Theory (AOT)

**One question.** Which sign- and integer-valued invariants of arithmetic sources survive passage to
unbounded aperture, horizon, damping and height — and which counting theorems compute them?

AOT makes orientation the primitive object. A signed incidence form carries its switching class; a
divisor row its companion (parity) class; a reading the question whether it separates a datum from
its flip; a test space at a node divisor the dimension of its sections; an unpaid weight an ideal of
the critical Wiener algebra and its obstruction hull. Theorems are identities, classifications and
counts; estimates are corollaries. Everything is unconditional; RH appears only in exact
equivalences or as the conclusion of an implication from one stated inequality.

Namespace `GaloisForLFunctions.ArithmeticOrientationTheory`; umbrella `ArithmeticOrientationTheory.lean`.

---

## 1. Place in the research

Recurring obstructions in the corpus are information lost by a reading: magnitudes and
complete-period data identify sources whose signed receivers differ; finite apertures admit
off-line extensions; positivity says nothing about upper bounds. An orientation invariant records
the sign, reflection or arithmetic distinction a limit must keep. AOT supplies: frustration index
and mass; per-tower rank-one law and coset/Cholesky forms of the odd prime side; the Nyquist rank
bound (rank–nullity RR for readings); the even flip read at the prime 2; the critical Wiener algebra
`𝒲_{1/2}` (Bohr polydisk, Wiener's lemma) with repairing ideals and obstruction hulls; section cones;
the receiver index theorem; the width dictionary and width functor.

Supporting framework for routes HF, ACS, AIP, PM, MC. Every dictionary entry is an equivalence;
progress is a bound in one of its units.

| Neighbour | Interface |
|---|---|
| [ScaleSignedIncidenceCriticality](../ScaleSignedIncidenceCriticality/README.md) | Readings, shadows, resolution; AOT adds flips, faithfulness, closure of blindness |
| [SignedArithmeticEnergyIncidence](../SignedArithmeticEnergyIncidence/README.md) | Balance, holonomy, local payment; AOT attaches index and mass and bounds the ground energy |
| [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Ratio/product atoms, `2R − P` odd autocorrelation; AOT proves the tower rank-one law |
| [TransHorizonIncidenceMechanics](../TransHorizonIncidenceMechanics/README.md) | Even flip, parity barrier, first pronic moment, `CriticalWiener`; AOT proves monoid/algebra structure |
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Damping chain; flow transports orientation on residue combinations |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Scaling surface, Hodge index, effectivity axioms; AOT's section cones are their section-count form |
| [ArithmeticCriticalityTheory](../ArithmeticCriticalityTheory/README.md) | Ground energy `μ(A)`; prime anti-diagonal non-Z-type obstruction = frustration |
| [ArithmeticContinuationAndCriticalEnergy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Exact damping/aperture derivatives; AOT's aperture jump = shell flux |
| [SquareRootThreshold](../SquareRootThreshold/README.md), [BiScaleUncertainty](../BiScaleUncertainty/README.md), [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | Nyquist threshold `N ≍ T` = square-root threshold; beyond it section counts must beat large values |
| [ArithmeticDefectRigidity](../ArithmeticDefectRigidity/README.md) | Cofactor escape modules; AOT's Wiener actions on them (operator vs annihilator hull) |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md), [ArithmeticLocalDivisorGeometry](../ArithmeticLocalDivisorGeometry/README.md) | Orbit orientation and local source-divisor geometry beyond the reading calculus |
| [ArithmeticCompensationTheory](../ArithmeticCompensationTheory/README.md), [arithmetic-positivity-theory](../arithmetic-positivity-theory/README.md) | Ceiling decay; temperedness gate; battery tests |

---

## 2. Why

**One invariant, many units.** `Δ = sup|Re ρ − ½|` is read exactly by every receiver: damping
(`Θ − ½`), aperture (`μ(A) ≥ 0` ∀A), growth (linear Chebyshev band), index (one positive square),
effectivity (RR + ample). `widthDictionary_tfae` is the change of coordinates; a new unit is not a proof.

**Loss of orientation.** Unconditional estimates sit at width `½` (+ Vinogradov–Korobov). The closing
mechanisms fail by losing orientation: amplitude readings are blind (payment is a function of
Ramanujan amplitudes iff `ε > ½`, and blindness is closed under post-processing); finite data admit
off-line extensions; positivity of a form does not see the frustrated rank-one pole charge.
Topological index theory and algebraic effectivity are how mathematics keeps orientation through
limits; neither exists on `ℤ × (scale)`. AOT builds their finite exact parts.

---

## 3. Objects and language

| Orientation | Signed forms | Damped weights | Readings | Sections | Wiener algebra |
|---|---|---|---|---|---|
| orientation | switching class | even flip `c♭` | flip `κ` | — | unit orbit |
| index | frustration index `ν(c)` | `W_c(2)` | — | `h⁰(A)` | `rank 𝒲/P(c)` |
| trivial | balanced | `W_c(2) = 0` | `κ`-fixed | — | `P(c) = ⊤` (paid) |
| faithful | sign-vector energy | first pronic moment | `OrientationFaithful` | rank | obstruction hull |
| blind | energy of `|c|` | amplitude reading | `Invisible` | — | — |

Objects (Lean):
- Signed Dirichlet form `signedDirichletForm`, `groundEnergy`; `misalignedMass`, `misalignedCount`,
  `frustrationIndex`, `frustrationMass`; `primeSumPairs`; samples `matchedPos`, `primeTrianglePos`,
  `packedPrimePos`, `collarPos`.
- Lattice correlations `ratioCorr` `R_q(m) = Σ_a q(a)q(am)`, `productCorr` `P_q(m) = Σ_{ab=m}q(a)q(b)`;
  `towerMellin` `S_p(q)`; `towerProductPart`, `towerOddPrimeSide`, `latticeOddPrimeSide`; `cosetToeplitz`,
  `pfreePart`; `archReflectedDiagWeight`, `towerTotalOddForm`; `activeTowerWeight`; `continuumPrimeTower`.
- Readings: `Matrix m n ℂ`, `frobeniusMass`, `HasFrameBound`, `h0`, `h1`; `dirichletSampling`,
  `dirichletCellSampling`, `sobolevDirichletSampling`, `harmonicDirichletSampling`, `dirichletAffineFrameConstant`.
- Oriented data: `Orientation`, `OrientationFaithful`, `Invisible`, `FourFreeDamped`, `evenFlip`,
  `amplitudeReading`.
- Wiener: `CriticalWiener` (THIM), `WienerAlgebraAt σ` (`𝒲_σ`), `BohrPoint`, `bohrEval`,
  `NormalizedBohrPoint`; `paidIdeal`, `obstructionHull`, `translatedOffLineZeroHull`,
  `visibleTranslatedZetaOrder`; `WienerUnitOrbit`, `WienerMonoidOrbit`; `orientNorm`; `operatorHull`.
- Section cones: `cycleObstructionReading`, `cycleH0`, `sectionEffectivityCone`; `sourceObstructionReading`,
  `sourceH0`, `sourceSectionCone`; `frobMassSectionCone`, `chebyshevSectionCone`, `gradedChebyshevSectionCone`,
  `l2MassSectionCone`.
- Receiver index: `poleJetMatrix`, `principalPartReadingOne/Two`, `zetaJetDiagReading`, `discreteEulerChar`,
  `nodeDivisorEulerChar s = e^s + s − 1 − ψ(e^s)`.
- Width: `ReceiverObject`, `widthFunctor`, `WidthLine = [0, ½]`, `IsZeroWidthObject`.

**Words.** *Faithful*: separates every datum from its flip; *blind*: invisible to it. *Frustration*:
misaligned overlaps after the best switching. *Tower*: prime powers of one prime. *Section*: a test
annihilated by a reading; *Nyquist bound*: sections ≤ dim − (Frobenius mass)/(frame bound). *Paid*:
receiver bounded; *repairing ideal* `P(c)`: kernels whose convolution pays `c`; *obstruction hull*:
Bohr points annihilating `P(c)`. *Unit*: a coordinate on the width line.

---

## 4. Mechanisms

### Frustration of signed forms and the odd Weil ledger
1. **Index controls ground energy.** Switching covariance (`frustrationIndex_switch`); balanced ⇔ index 0;
   `D_c(s) = 4·misalignedMass` so `groundEnergy ≤ 4ν_w/n` (`groundEnergy_le_frustrationMass`); on connected
   patterns ground energy 0 ⇔ balanced (`groundEnergy_eq_zero_iff_isBalanced`). Lower bound: signed Cheeger
   `μ ≥ h²/(4D)` (`le_groundEnergy_of_cheeger`); budgets within `h²/(8D)` of degree suffice (`incidenceEnergy_ge_of_cheeger`).
2. **Where the odd ledger frustrates.** Only on prime-sum pairs (`frustrationIndex_oddWeilLedger_le`). Lattice
   samples (logs of integers): within a tower the difference weight dominates the sum weight, so the
   lattice ledger is **balanced at every aperture** (`isBalanced_lattice`, `nonneg_iff_locallyPayable_lattice`).
   Prime triangle: index exactly 2 (`frustrationIndex_primeTriangle`). Sparse samples: index = anti-aligned
   prime-sum count (`frustrationIndex_oddWeilLedger_of_sparse`, cut dominance); matched samples reach `2|Q|`
   (`exists_frustrationIndex_ge`). Mass ≤ β·prime-sum charge (`frustrationMass_le_primeSumCharge`).
3. **Full weight `α = β = 1`.** Polar hyperbolic barrier `K|x+y| − K|x−y| < −8 sinh(x/2)sinh(y/2)` quenches
   matched samples (index 0); prime triangle index 2, mass in `[2/7, 4/5)`; dense triangle packings give
   index ≥ 2M in `(0, log 5]`; collar-skimming `collarPos` reaches `2M|Q|` at every positive weight
   (`exists_collarPos_frustrationIndex_eq_two_mul`); `(0, 3/10]` is frustration-free
   (`oddWeilLedger_offLattice_frustration_and_contact_synthesis`). Frustration is a **continuum** phenomenon
   between lattice points.

### Tower structure of the odd prime side
4. **Rank-one law.** `towerProductPart q p K = log p·(S_p(q)² − q(1)²)` (`sum_vonMangoldt_productCorr_prime_pow`);
   global product part = sum of tower squares beyond `X²` (`sum_vonMangoldt_productCorr_eq_sum_towers`).
5. **Coset law.** Ratio part = Σ over `p`-free cosets of one-sided Toeplitz forms (`towerOddPrimeSide_eq`);
   KMS–Cholesky form ⇒ `towerOddPrimeSide ≥ −log p·Σ_{n≥2}q(n)²` (`towerOddPrimeSide_eq_cholesky`, `towerOddPrimeSide_ge`).
6. **Axis cancellation and arch dominance.** Odd side independent of `q(1)` (`towerOddPrimeSide_update_one`);
   reflected prime-power diagonal is the only negative term on coherent profiles
   (`towerOddPrimeSide_eq_scaleSuppressed_sub_diag`); archimedean reflected diagonal pays twice the interior
   Hankel square for arbitrary-sign profiles (`towerTotalOddForm_ge_half_towerArchDiagForm`). Shifted pair
   `ζ(s−a)ζ(s+a)` reverses every comparison for `|a| ≥ 1`
   (`cosetToeplitz_dominance_and_shiftedPair_selectivity_synthesis`).
7. **Shared all-prime payment on the lattice.** Towers `p > X` vanish (`towerOddPrimeSide_eq_zero_of_lt`);
   singleton cosets cancel, top sites keep `log p/p` ⇒ `M`-independent active weight
   `≤ θ(X/n) + ½ log n` (`sum_towerOddPrimeSide_ge_neg_activeTowerWeight`); arch diagonal dominates on the top
   octave (`sum_towerOddPrimeSide_add_archDiag_nonneg_of_top_octave`). **Horizon-uniform Schur dominance**:
   `2(Λ(m)/√m)|q(a)||q(am)|` split asymmetrically, `Σ Λ(m)/(m√m) ≤ 8`, divisor bound for dilated terms ⇒
   for every `X`, every prime set `S`, every arbitrary-sign `q`:
   `Σ_S towerOddPrimeSide + Σ archDiag·q² ≥ (1/16)Σ_{n≥256} n q(n)² − 106Σ_{n≤255} q(n)²`
   (`sum_towerOddPrimeSide_add_archDiag_ge_tail_sub_head_255`), nonnegative on profiles supported in `[25, X]`
   (`sum_towerOddPrimeSide_add_archDiag_nonneg_of_support_ge_25`). Lattice shared payment is reduced to a
   finite head.
8. **Continuum towers.** Reflection Cholesky `M + 2R − H = (1−r)‖U₀‖² + (r/2)‖U₀ − U₀(L−·)‖² + (1−r²)Σ‖U_j‖²`
   (`continuumTower_reflection_cholesky`); towers with `2A ≤ log p` vanish; all primes at once:
   `Σ_S continuumPrimeTower ≥ −12e^A∫_0^A F²` (`sum_continuumPrimeTower_ge_neg_twelve_exp`) — `S`-uniform but
   exponential in the aperture.

### Readings and sections
9. **Oriented readings.** Blindness closed under composition, joins, families, coarsening (`Invisible.comp`,
   `Invisible.pi`); blind readings resolve only invariant predicates; resolving a flipping predicate forces
   faithfulness (`orientationFaithful_of_resolves_of_flips`). Complete-period quadratic data are sign-orbit blind
   (`mem_shadow_completePeriodLagReading_iff_signOrbit`).
10. **Even flip read at 2.** Involution in the damped class; `M(c♭) − M(c) = 2 log 2·W_c(2)`
    (`firstPronicMoment_evenFlip_sub`); amplitude reading blind (`invisible_amplitude_evenFlip`); parity floor
    (`not_resolves_amplitude_receiverBounded`).
11. **Nyquist rank bound.** `h⁰ + rank = dim`, `h⁰ − h¹ = dim − #nodes` (`h0_sub_h1`); rank–trace
    `mass ≤ K·rank`; `h⁰ ≤ dim − mass/K` (`h0_le_nyquist`), dual `h1_le_nyquist`; Dirichlet polynomials at
    separated heights via large values (`h0_dirichletSampling_le`). Log-free frame constant
    `(5π/2)max(T,1) + 5πeN`, balanced at `T = 2eN` (`dirichletAffineFrameConstant_diagonal_balance`); above the
    diagonal `h⁰ ≥ N − T` (`h0_dirichletSampling_pos_above_diagonal`); diagonal = square-root aperture
    (`nyquist_diagonal_and_squareRoot_threshold_synthesis`).
12. **Selectivity beyond rank.** `h⁰`, rank, `h¹` are invariant under diagonal reweighting, so they cannot
    separate `Λ` from the shifted pair (`h0_rank_h1_weightedDirichletSampling_shiftedPair_eq_vonMangoldt`);
    Frobenius mass can (`frobeniusMass_weightedDirichletSampling_shiftedPair_gt`); box defect
    `E(s) = e^s + s − 1 − ψ(e^s) = h⁰-supply − h¹-obstruction` (`boxH0Supply_sub_boxH1Obstruction`); aperture `h¹`
    correction = pole charge + prime-node obstruction, characterizes Bézout on the odd section cone at each
    aperture (`sectionEffectivityCone_odd_bezout_iff_apertureH1ChebyshevCorrection_le`), paid on `(0, 181/500]`;
    prime-blind sections vanish below spectral height `√(69/2)` (`finrank_primeBlind_subspace_eq_zero`).
13. **Section cones.** `E = {x : h⁰ ≥ 1}` = positive cone ∩ nef quadrant; its Bézout/RR/ample ⇔ Hodge index
    on every polar surface (`sectionEffectivityCone_tfae`) — calibration, reads the form. Sign-free Bézout:
    `δ(x,y)² ≤ Φ(x)Φ(y)` ⇒ Bézout without reading `x²` (`sourceSectionCone_bezout_of_defect_sq_le`); boundary
    rigidity: Bézout ⇔ that inequality; RR + Bézout ⇔ `Φ⁺ = defect` (`sourceSectionCone_riemannRoch_and_bezout_iff_positivePart_eq_defect`);
    Boolean `h⁰ ≤ 1` cannot satisfy a dimension RR formula (`exists_sourceH0_riemannRoch_dimension_failure`);
    finite linear/Fourier reading cones fail Bézout (`finiteLinearReadingSourceSectionCone_not_bezout`).
    Over `𝔽_q`: Rosati/Frobenius-mass cones have Bézout and ampleness always, RR iff zero reflection defect
    (`rosatiSourceCone_riemannRoch_iff_reflection_zero`); golden datum has both positivity axioms and fails RR
    (`goldenDatum_frobMass_bezout_ample_not_riemannRoch`). Over `ℤ`: graded Chebyshev cone has RR at every
    aperture, Bézout/ample ⇔ Chebyshev correction paid by arch budget ⇔ (all apertures) RH
    (`riemannHypothesis_iff_all_aperture_gradedChebyshev_bezout`); `L²`-mass cone convex, ample, RR past the
    prime 2 (`l2MassSectionCone_convex_ample_and_primeTwo_riemannRoch`).
14. **Receiver index theorem.** Pole orders = section codimensions (`receiverBounded_orderOnePole_iff_sections`,
    `poleJetMatrix_two_rank_h1_h0`); zero multiplicities = jet section counts
    (`receiverBounded_logPowerCosine_iff_h0_eq`); node-divisor Euler characteristic from the reflected
    prime-polar ledger (`nodeDivisorEulerChar_integral_from_ledger`); one dictionary (`receiver_index_theorem`).
15. **Trichotomy of readings.** Sub-Nyquist sign-factored readings are depth-blind
    (`trichotomy_of_readings_escape`); escapes cost: trans-Nyquist precision `β²L³`, magnitude ratios
    `½β²L²`/`2β²a²`, third-kind mass data (`branchOne_transNyquist_precision_cost`, `branchTwo_magnitude_precision_cost`).

### The critical Wiener algebra
16. **Monoid and algebra.** `CriticalWiener` closed, submultiplicative (`tsum_abs_dirichletConv_le`); paid class
    is a union of orbits (`receiverBounded_orbit`); `𝒲_σ` Banach algebra, spectrum = Bohr polydisk
    (`apply_eq_bohrEval`); Wiener's lemma (`isUnit_iff_forall_bohrEval_ne_zero`); half-plane form needs a
    uniform lower bound (`isUnit_iff_exists_le_norm_lSeries`), nonvanishing is not enough
    (`not_isUnit_threeTermKernel`); local factor unit ⇔ all `|α_i| < p^σ` (`isUnit_prod_localFactor_iff`);
    units preserve payment both ways (`receiverBounded_dirichletConv_iff_of_isWienerUnit`). Coefficients are
    continuous, point masses independent, `𝒲_σ` infinite-dimensional (`not_finiteDimensional`); normalized Bohr
    points represent distinct characters (`normalizedBohrPoint_eq_of_character_eq`).
17. **Unpayability on the polydisk.** Unpaid ⇔ nonempty obstruction hull (`not_receiverBounded_iff_exists_obstruction`);
    computations: `d^{−ε}` → pole point; oscillating probe → `{ρ, ρ̄}` unless `ζ(ρ) = 0`
    (`obstructionHull_oscillating_nonempty_iff`); codimension counts points (`finrank_quotient_paidIdeal_probeSum`);
    hull calculus (sums, convolution locality); untied hulls off the half-plane (`exists_obstruction_not_tied`);
    multiplicity: `(log d)d^{−ε}` same hull, strictly smaller non-radical ideal (`not_isRadical_paidIdeal_logPower`);
    orbit structure: unit orbits equivalence, monoid preorder with monotone invariants, infinite descending
    chain inside one hull (`iterThreeTermConv_smoothPower_chain`).
18. **Index formula for the Möbius receiver.** Paid ⇔ `P = ⊤` ⇔ hull ∅ ⇔ rank 0; translated off-line zeros
    `ρ − ε` (½+ε < Re ρ < 1) are obstructions (`translatedOffLineZeroHull_subset_obstructionHull_moebius`), their
    number ≤ codimension (`card_le_rank_quotient_paidIdeal_moebius`); equality above the width
    (`moebius_reverse_inclusion_and_index_above_zeroWidth`). **Order level:** every repairing kernel vanishes at
    `ρ − ε` to at least `ord ζ(ρ) − ord ζ(ρ−ε)` (`visibleTranslatedZetaOrder_le_paid_kernel_order`), so its jets
    vanish below that order (`paid_kernel_jets_vanish_below_visible_order`); on the **critical boundary**
    `Re ρ = ½ + ε`, any order loss `ord ζ(ρ−ε) < ord ζ(ρ)` makes `μ d^{−ε}` unpaid
    (`not_receiverBounded_moebius_of_critical_boundary_order_loss`). All persist on the unit orbit, including
    Liouville (`wienerUnitOrbit_moebius_liouville`, `not_receiverBounded_liouville_of_critical_boundary_order_loss`).
    Real characters are paid; multiplicative weights with `f(p) = −1` lie in Möbius's forward cone.
19. **Orientation-faithful norm.** `N(k) = Σ|k(j)|j^ε`; flip acts on pole coordinates
    `(P, P_e) ↦ (P + (1−2^ε)P_e, −P_e)`; both flip members paid ⇔ `P = P_e = 0`
    (`receiverBounded_and_evenFlip_iff`); smooth-power and multiplicative versions
    (`receiverBounded_and_evenFlip_multiplicative_iff`).
20. **Wiener actions on modules.** Bounded multiplicative sequences extend uniquely to contractive
    homomorphisms (`sequenceExtension_unique`); critical kernel actions extend to `𝒲` via dilations
    (`intertwines_cyclic_vector`); max-kernel action faithful (`wiener_representation_injective_of_max_gram`).
    **Operator hull** (characters bounded by the represented norm) ⊆ annihilator hull, equal under closed range
    (`operatorHull_eq_annihilatorHull_of_isClosed_range`). Weighted orthogonal cofactor modules: faithful at
    every weaker weight, so the annihilator hull is full (`hull_eq_univ`) while operator spectra contract
    (`onePoint_not_mem_operatorHull`). Annihilator hulls of faithful cyclic modules carry no localization.

The interior orders, jets, boundary values and unit-orbit statements in item 18
passed final canonical checks with standard axioms. The critical-kernel
and max-kernel applications in item 20 also passed their individual canonical
checks and standard-axiom audits. See the
[completion ledger](../../../docs/drafts/pipeline/1-in-progress/q-iii-existing-findings-lean-completion.md).

### Transport and dictionaries
21. **Damping flow preserves orientation** on residue combinations (`sign_coeff_centeredOperator`).
22. **Aperture transport.** Two-gauge step jump = boundary-shell flux ≥ 0 (`gaugeStepJumpEnergy_eq_gaugeStepBoundaryFlux`);
    window floor strictly decreasing (`hasDerivAt_windowFloor`); `Φ`-gauge defect identity; spectral jumps
    telescope, RH ⇔ they sum to `μ(A₀)` (`riemannHypothesis_iff_hasSum_apertureSpectralJump`); fixed-margin additive
    transport refuted by the Gaussian ceiling (`not_additive_step_transport`); relative steps `c_j ≤ 1` ⇔ RH.
23. **Width dictionary and functor.** `widthDictionary_tfae`, graded (`gradedWidthDictionary_tfae`), forcing
    units and one-sided window ceiling (`forcingSignAndWidthDictionary_tfae`); `widthFunctor` full, faithful,
    iso-reflecting; six ζ-receivers isomorphic (`zetaReceivers_widthVal_eq`); battery models are non-objects
    (`theWidthFunctor_and_selectivityBattery_synthesis`).

---

## 5. Pillar theorems

1. Frustration controls ground energy (`groundEnergy_le_frustrationMass`, `groundEnergy_eq_zero_iff_isBalanced`, `le_groundEnergy_of_cheeger`).
2. Odd ledger: lattice balanced, frustration = prime-sum count (`isBalanced_lattice`, `frustrationIndex_oddWeilLedger_of_sparse`, `exists_collarPos_frustrationIndex_eq_two_mul`).
3. Tower laws (`sum_vonMangoldt_productCorr_prime_pow`, `towerOddPrimeSide_eq_cholesky`, `continuumTower_reflection_cholesky`).
4. Lattice shared payment up to a finite head (`sum_towerOddPrimeSide_add_archDiag_ge_tail_sub_head_255`).
5. Nyquist rank bound and its diagonal (`h0_le_nyquist`, `h0_dirichletSampling_le`, `nyquist_diagonal_and_squareRoot_threshold_synthesis`).
6. Even flip at 2 (`firstPronicMoment_evenFlip_sub`, `not_resolves_amplitude_receiverBounded`).
7. Wiener's lemma on the Bohr polydisk (`isUnit_iff_forall_bohrEval_ne_zero`, `isUnit_iff_exists_le_norm_lSeries`).
8. Unpayability located and counted (`not_receiverBounded_iff_exists_obstruction`, `card_le_rank_quotient_paidIdeal_moebius`, `visibleTranslatedZetaOrder_le_paid_kernel_order`).
9. Section-cone boundary laws (`sectionEffectivityCone_tfae`, `sourceSectionCone_bezout_of_defect_sq_le`, `rosatiSourceCone_riemannRoch_iff_reflection_zero`, `riemannHypothesis_iff_all_aperture_gradedChebyshev_bezout`).
10. Receiver index theorem (`receiver_index_theorem`).
11. Width dictionary (`widthDictionary_tfae`, `categoricalWidthDictionary_tfae`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Frustration index is a coupling property | Switching-class invariant |
| Ground energy 0 ⇒ balance | Only on connected patterns |
| Frustration is a small-sample artefact | Unbounded with aperture (`2|Q|`, `2M|Q|`) |
| Lattice ledger frustrates | Balanced at every aperture; frustration lives between lattice points |
| Lattice shared payment = RH progress | Lattice tests are a restricted class; the continuum bound still costs `e^A` |
| `h⁰` counts nodes | Dimension of annihilated tests; nodes enter via mass and frame bound |
| Rank counts are selective | Reweighting-invariant; use Frobenius mass or `E(s)` |
| Even flip changes amplitudes | Every amplitude reading is blind to it |
| First pronic moment always reads the flip | Only through `W_c(2)` |
| Critical Wiener kernels form a group | A monoid; units = no zero on the polydisk |
| No zero on `Re s ≥ ½` ⇒ unit | Needs a uniform lower bound |
| Hull is a complete invariant | Ideal records multiplicity; same hull, different ideals |
| Annihilator hull of a cofactor module localizes | Faithful modules have full hull; only the operator hull contracts |
| Section effectivity cone is independent effectivity | Membership reads `x² ≥ 0`; calibration only |
| Bézout + ample on Rosati/Frobenius cones ⇒ Weil | Golden datum has both; RR is the selective axiom |
| A new unit is progress | Dictionary entries are equivalences |
| Damping flow changes signs | Scales residue coefficients by `d^{−η} > 0` |

---

## 7. Open problems

1. **Frustration → `μ(A)`.** Signed Cheeger constant and degree of the actual continuum ledger at aperture
   `A` with archimedean/polar budgets: a lower bound on `μ(A)` from the switching class.
2. **Continuum shared payment.** Lattice tower payment is done up to the head `n ≤ 255`; the continuum
   all-prime bound is `−12e^A∫F²`. Open: an aperture-uniform continuum shared payment, and the head constant
   (signed estimate for direct coset correlations at small `n`).
3. **Selective section count at/beyond the diagonal**, coupled to Frobenius mass or `E(s)`, stronger than the
   mean value theorem and passing golden/shifted-pair tests. (Retirement criterion: if the only sections are
   those the large sieve counts, the field's contribution is its dictionary and battery.)
4. **A source energy that is not the defect**: arithmetic `Φ` with `δ(x,y)² ≤ Φ(x)Φ(y)` and RR proved from
   its definition — ACS's open core in section form.
5. **Index formula below the width**: is `hull(μd^{−ε})` exactly the translated off-line zero hull, and is
   `rank 𝒲/P(μd^{−ε})` the zero count with multiplicity? Order-level lower bound and critical-boundary
   obstruction are proved; the reverse inclusion below the width is open.
6. **Ideals beyond hulls**: which ideals occur as repairing ideals; is `P(c)` hull + local orders?
7. **Aperture jump estimate**: a quantitative bound on the signed new-prime correlation (jump = flux is exact).
8. **A faithful reading that is an estimate** in one trichotomy branch at its precision cost.
9. **Wiener index for cofactor modules**: an invariant finer than the annihilator hull (operator hull,
   closed-range criteria) that localizes on the actual escape module.

---

## 8. Tools and selectivity battery

Built: signed Dirichlet form, frustration index/mass, signed Cheeger, sub-sample monotonicity; tower
rank-one, coset, Cholesky, Schur-dominance and continuum reflection identities; Nyquist bound, log-free
frame constants, sampling variants; orientation calculus on readings; even-flip formulas; `𝒲_σ`, Bohr
characters, Wiener's lemma, repairing ideals, hull calculus, index formulas, order-level payment
constraints, operator hulls; section cones (cycle, source, Rosati, Chebyshev, graded, `L²`); receiver index
readings; aperture transport identities; width dictionary/functor.

**Battery** (a width-moving claim must pass every applicable test):

| Test | Content | Anchor |
|---|---|---|
| golden datum | Beurling `1 − 5X + 5X²` impure | `goldenDatum_beurling_not_pure` |
| shifted pair | fails for `ζ(s−a)ζ(s+a)` | `not_summable_shiftedPairVonMangoldt_windowDilationExponent` |
| parity twins | separate `μ`/twin, Fermi/flip | `fermi_evenFlip_parityPair` |
| nodes | fatal at `log 4`, free at `log 6` | `zeroPoleBlindPositiveOn_iff` |
| ceiling | floors decay like `exp(−πe^{2(A−2)})` | `exists_le_floorLoss_of_floor` |
| finite data | bounded readings admit off-line extensions | `resolutionLimit_width_aperturePositivity` |
| rate | use the prime rate in full | `riemannHypothesis_iff_isLeast_primeRate` |
| function field | reproduce curve Hodge index | `curve_hodgeIndex_tfae` |
| integrality | exactly one positive square | `riemannHypothesis_iff_one_positive_square` |
| precision | depth `β` at scale `L` costs `β²L³` | `branchOne_transNyquist_precision_cost` |

---

## 9. Principles

Counts before estimates; gauge first (check covariance under the flip); name the reading and whether it
is faithful; pay rank-one charges globally; tag every result with its unit; accompany positivity claims
by their failure on the battery. Lean: capstones take data only; no RH-equivalent hypothesis; analytic
inputs are proved corpus theorems.
