import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentActualZetaDetectionAndFullZeroFormBridge
import GaloisForLFunctions.SquareRootThreshold.ZetaWeilPositivityBelowApertureOneHundredth
import GaloisForLFunctions.SquareRootThreshold.ZetaSingleHeightPositivityAboveArchimedeanHorizon
import GaloisForLFunctions.SquareRootThreshold.DepthGapVisibilityLaw
import GaloisForLFunctions.SquareRootThreshold.EqualDepthClusterInArbitraryBackground
import GaloisForLFunctions.SquareRootThreshold.AttainedDepthIsVisible
import GaloisForLFunctions.SquareRootThreshold.LargeDyadicPrimeWindowsDecideTheCriticalLine
import GaloisForLFunctions.RHTower.CHMDPolarTransfer
import GaloisForLFunctions.RHTower.CHMDSpectralRiemannCriterion
import GaloisForLFunctions.RHTower.CHMDComplexWeilForm
import GaloisForLFunctions.RHTower.AsymptoticAbscissaLawProducers
import GaloisForLFunctions.RHTower.XiSliceEventualPositivityFiniteOffLine

/-!
# Small-Aperture Coercivity, Polar Doob Graph Transfer, Depth-Gap & Cluster Detection, and the Attained-Depth Abscissa Bridge

This module connects theorems across `ArithmeticPositivityTheory`, `SquareRootThreshold`,
`ArithmeticCriticalityTheory`, and `RHTower` (`CHMDPolar`, `CHMDDoobGraph`, `BacklundConverse`)
to establish four unconditional structural bridges:

1. **Unconditional Small-Aperture (`a ≤ 1/100`) and High-Height Reflection-Defect Coercivity for
   Actual Zeta (`zeta_reflectionDefect_add_l2_le_squareMass_of_aperture_le_hundredth`,
   `fullZeroForm_ge_l2_div_twenty_five_of_aperture_le_hundredth`,
   `zeta_squareMass_sub_reflectionDefect_heightShift_ge`):**
   Combining the three-band archimedean lower bound below aperture `1/100`
   (`zetaZeroConfig_re_W_ge_of_aperture_le_hundredth`) and the localized explicit-formula lower
   bound at height `2πξ` (`zetaZeroConfig_re_W_heightShift_ge`) with the universal zero-side
   reflection identity (`zeta_squareMass_sub_re_W_eq_reflectionDefect`) and the five-way form
   unification (`fullZeroForm_eq_zeta_W_re`, `fullZeroForm_eq_compactFullWeilEnergy`) yields:
   - For every `0 < a ≤ 1/100` and every `f ∈ C_c²(ℝ, ℂ)` supported in `[-a, a]`,
     `configurationReflectionDefect zetaZeroConfig f + (1/25) ∫ ‖f‖² ≤ configurationSquareMass zetaZeroConfig f`.
   - For every real `F ∈ C_c²(ℝ, ℝ)` supported in `[-a, a]` (`0 < a ≤ 1/100`), both `fullZeroForm F`
     and `compactFullWeilEnergy F` satisfy the unconditional `L²`-coercive bound
     `(1/25) ∫ F(t)² dt ≤ fullZeroForm F = compactFullWeilEnergy F`.
   - At any aperture `a ≥ 0` and height shift `ξ ∈ ℝ`, `configurationSquareMass - configurationReflectionDefect`
     on `heightShift ξ f` satisfies the explicit archimedean-horizon lower bound and is
     unconditionally nonnegative above the horizon `|ξ| ≥ Ξ(f)`.

2. **Exact Polar Doob Graph Transfer and the Polar-Strengthened Odd Doob Poincaré Criterion
   (`polarEnergy_eq_phiDoobMoments`, `weilForm_compactLift_eq_archJump_add_primeJump_sub_polarEnergy`,
   `riemannHypothesis_iff_forall_odd_phiDoob_polar_strengthened_poincare`,
   `riemannHypothesis_iff_weilForm_nonneg`, `riemannHypothesis_iff_polarEnergy_le_edge`):**
   We express `CHMDPolar.polarEnergy v` on `MemLp v 2 massMeasure` in terms of the three Doob
   moments `phiDoobCoshMass (v²) - 2 phiDoobCoshMass(v)² + 2 phiDoobSinhMass(v)²`. On the
   primitive hyperplane `phiDoobCoshMass v = 0` (and in particular for every odd `v`),
   `polarEnergy v = phiDoobCoshMass (v²) + 2 phiDoobSinhMass(v)²`, so including the pole term
   strengthens the odd-sector Doob Dirichlet–Poincaré inequality by `2 phiDoobSinhMass(v)² ≥ 0`
   while remaining equivalent to `RiemannHypothesis`, and closes the two-way equivalences
   `RiemannHypothesis ↔ (∀ p : SourceGraph, 0 ≤ weilForm p) ↔ (∀ p : SourceGraph, polarEnergy p.1.1 ≤ ‖p.1.2‖²)`.

3. **Actual-Zeta Depth-Gap Detection, Deep-Companion Forcing, Equal-Depth Cluster Detection, and
   the Dyadic Prime-Window Reflection-Defect Law
   (`actual_zeta_depthGap_detected_by_gridTentPattern_at_aperture`,
   `zeta_gridTentPattern_nonneg_forces_deep_companion`,
   `actual_zeta_equalDepthCluster_detected_by_gridTentPattern_at_aperture`,
   `lagPrimeWindowRHS_re_eq_zeta_squareMass_sub_reflectionDefect`):**
   Connecting `DepthGapVisibilityLaw`, `EqualDepthClusterInArbitraryBackground`, and
   `LargeDyadicPrimeWindowsDecideTheCriticalLine` with `gridTentPattern_actual_zeta_detector_spec`
   gives explicit-aperture single-scale grid tent detection for depth-gap zeros and equal-depth
   clusters, contrapositive deep-companion forcing from eventual grid-tent nonnegativity, and the
   exact zero-side reflection-defect formula for single dyadic prime-window functionals.

4. **Attained-Depth Detection and the `AsymptoticAbscissaLaw` / `ZerosApproachLine` Bridge
   (`actual_zeta_attainedDepth_detected_by_gridTentPattern`,
   `asymptoticAbscissaLaw_of_eventually_gridTentPattern_nonneg`,
   `riemannHypothesis_iff_zerosApproachLine_and_eventually_gridTentPattern_nonneg`):**
   Bridging `XiZeroCopy` (`RHTower`) with `zetaZeroConfig.carrier` (`SquareRootThreshold`), every
   attained maximal-depth zero is unconditionally detected via Cesàro-grid two-bump seeds by
   single-scale grid factorial-tent patterns, so eventual grid-tent nonnegativity unconditionally
   implies `AsymptoticAbscissaLaw`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators CompactlySupported ComplexConjugate InnerProductSpace
open _root_.Zeta23 _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.BacklundConverse _root_.RHTower.LindelofSparse
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ## Section 1: Unconditional Small-Aperture (`a ≤ 1/100`) and High-Height Coercivity for Actual Zeta -/

/-- **Unconditional Small-Aperture Reflection-Defect Coercivity (`a ≤ 1/100`).**
For every `0 < a ≤ 1/100` and every `f ∈ C_c²(ℝ, ℂ)` with `tsupport f ⊆ [-a, a]`, the actual
off-line reflection defect of `ζ` plus `(1/25) ∫ ‖f(t)‖² dt` is bounded above by the zero-side
square mass of `ζ`. -/
theorem zeta_reflectionDefect_add_l2_le_squareMass_of_aperture_le_hundredth
    {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 100) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    configurationReflectionDefect zetaZeroConfig f + (1 / 25) * ∫ t, ‖f t‖ ^ 2 ≤
      configurationSquareMass zetaZeroConfig f := by
  have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  have hW := zetaZeroConfig_re_W_ge_of_aperture_le_hundredth ha0 ha hf hfs
  have hrefl := zeta_squareMass_sub_re_W_eq_reflectionDefect hf hfc
  linarith

/-- **Unconditional Small-Aperture `L²`-Coercivity of `fullZeroForm` and `compactFullWeilEnergy`.**
For every `0 < a ≤ 1/100` and every real `F ∈ C_c²(ℝ, ℝ)` with `tsupport F ⊆ [-a, a]`, both
ACT's `fullZeroForm F` and APT's `compactFullWeilEnergy F` are at least `(1/25) ∫ F(t)² dt`,
with no vanishing-moment hypothesis on the pole terms. -/
theorem fullZeroForm_ge_l2_div_twenty_five_of_aperture_le_hundredth
    {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 100) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFs : tsupport F ⊆ Icc (-a) a) :
    (1 / 25) * (∫ t, F t ^ 2) ≤ fullZeroForm F ∧
      (1 / 25) * (∫ t, F t ^ 2) ≤
        compactFullWeilEnergy ⟨⟨F, hF.continuous⟩,
          isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hFs⟩ := by
  have hFc : HasCompactSupport F := isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hFs
  set f : ℝ → ℂ := fun t => (F t : ℂ)
  have hf : ContDiff ℝ 2 f := Complex.ofRealCLM.contDiff.comp hF
  have hsupp_eq : Function.support f = Function.support F := by
    ext t
    simp [f]
  have hfs : tsupport f ⊆ Icc (-a) a := by
    simpa only [tsupport, hsupp_eq] using hFs
  have hW := zetaZeroConfig_re_W_ge_of_aperture_le_hundredth ha0 ha hf hfs
  have hint : (∫ t, ‖f t‖ ^ 2) = ∫ t, F t ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [f, Complex.norm_real, sq_abs]
  rw [hint, ← fullZeroForm_eq_zeta_W_re hF hFc] at hW
  refine ⟨hW, ?_⟩
  rwa [← fullZeroForm_eq_compactFullWeilEnergy ⟨⟨F, hF.continuous⟩, hFc⟩]

/-- **Quantitative High-Height Lower Bound on `configurationSquareMass - configurationReflectionDefect`.**
For any aperture `a ≥ 0`, any `f ∈ C_c²(ℝ, ℂ)` supported in `[-a, a]`, and any height shift `ξ ∈ ℝ`,
the actual-zeta zero-side balance on `heightShift ξ f` satisfies the archimedean-horizon bound. -/
theorem zeta_squareMass_sub_reflectionDefect_heightShift_ge
    {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    (Real.log (1 + Real.pi * |ξ| / 4) - horizonExponent (Real.exp (2 * a)) -
        2 * pairEnergy (1 / 2) a) * (∫ t, ‖f t‖ ^ 2) -
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + Real.pi * |ξ|)) ≤
      configurationSquareMass zetaZeroConfig (heightShift ξ f) -
        configurationReflectionDefect zetaZeroConfig (heightShift ξ f) := by
  have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  have hg : ContDiff ℝ 2 (heightShift ξ f) := heightShift_contDiff hf ξ
  have hgc : HasCompactSupport (heightShift ξ f) := hfc.mul_left
  have hW := zetaZeroConfig_re_W_heightShift_ge ha hf hfs ξ
  have hrefl := zeta_squareMass_sub_re_W_eq_reflectionDefect hg hgc
  linarith

/-- **Unconditional High-Height Reflection-Defect Domination for Actual Zeta.**
For every `f ∈ C_c²(ℝ, ℂ)`, there exists a height horizon `Ξ` above which the zero-side square mass
of `heightShift ξ f` unconditionally dominates its off-line reflection defect. -/
theorem exists_zeta_reflectionDefect_le_squareMass_heightShift
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ Ξ : ℝ, ∀ ξ : ℝ, Ξ ≤ |ξ| →
      configurationReflectionDefect zetaZeroConfig (heightShift ξ f) ≤
        configurationSquareMass zetaZeroConfig (heightShift ξ f) := by
  obtain ⟨Ξ, hΞ⟩ := exists_zetaZeroConfig_re_W_heightShift_nonneg hf hfc
  refine ⟨Ξ, fun ξ hξ => ?_⟩
  have hW := hΞ ξ hξ
  have hrefl := zeta_squareMass_sub_re_W_eq_reflectionDefect (heightShift_contDiff hf ξ) hfc.mul_left
  linarith

/-! ## Section 2: Polar Doob Graph Transfer and the Polar-Strengthened Odd Doob Poincaré Criterion -/

/-- **Doob Moment Formula for the Polar Jump Energy.**
For every square-integrable profile `v` on `massMeasure`, the polar jump Dirichlet form
`polarEnergy v` equals `phiDoobCoshMass (v²) - 2 phiDoobCoshMass(v)² + 2 phiDoobSinhMass(v)²`. -/
theorem polarEnergy_eq_phiDoobMoments {v : ℝ → ℝ} (hv : MemLp v 2 massMeasure) :
    polarEnergy v =
      phiDoobCoshMass (fun x => v x ^ 2) - 2 * phiDoobCoshMass v ^ 2 +
        2 * phiDoobSinhMass v ^ 2 := by
  rw [polarEnergy_eq hv, ← phiDoobCoshMass_eq_integral_mass (fun x => v x ^ 2),
    ← phiDoobCoshMass_eq_integral_mass v, ← phiDoobSinhMass_eq_integral_mass v]

/-- On the primitive hyperplane `phiDoobCoshMass v = 0`, the polar jump energy is the sum of the
second-moment cosh mass and twice the squared odd sinh moment:
`polarEnergy v = phiDoobCoshMass (v²) + 2 phiDoobSinhMass(v)²`. -/
theorem polarEnergy_eq_coshMass_sq_add_two_sinhMass_sq_of_primitive
    {v : ℝ → ℝ} (hv : MemLp v 2 massMeasure) (hprim : phiDoobCoshMass v = 0) :
    polarEnergy v = phiDoobCoshMass (fun x => v x ^ 2) + 2 * phiDoobSinhMass v ^ 2 := by
  rw [polarEnergy_eq_phiDoobMoments hv, hprim]
  ring

/-- Every odd profile `v : ℝ → ℝ` lies in the primitive hyperplane `phiDoobCoshMass v = 0`. -/
theorem phiDoobCoshMass_eq_zero_of_odd {v : ℝ → ℝ} (hodd : ∀ x, v (-x) = -v x) :
    phiDoobCoshMass v = 0 := by
  unfold phiDoobCoshMass phiDoobTest
  apply integral_eq_zero_of_odd
  intro x
  rw [WeilExcess.riemannKernelReal_neg, hodd x, neg_div, Real.cosh_neg]
  ring

/-- For every odd square-integrable profile `v`, the polar jump energy equals
`phiDoobCoshMass (v²) + 2 phiDoobSinhMass(v)²`. -/
theorem polarEnergy_eq_coshMass_sq_add_two_sinhMass_sq_of_odd
    {v : ℝ → ℝ} (hv : MemLp v 2 massMeasure) (hodd : ∀ x, v (-x) = -v x) :
    polarEnergy v = phiDoobCoshMass (fun x => v x ^ 2) + 2 * phiDoobSinhMass v ^ 2 :=
  polarEnergy_eq_coshMass_sq_add_two_sinhMass_sq_of_primitive hv (phiDoobCoshMass_eq_zero_of_odd hodd)

/-- **Unification of `CHMDPolar.weilForm` and `CHMDDoobGraph.sourceWeilEnergy` on `SourceGraph`.** -/
theorem weilForm_eq_sourceWeilEnergy (p : SourceGraph) :
    weilForm p = sourceWeilEnergy p := by
  have hfun : weilForm = sourceWeilEnergy := by
    refine sourceWeilEnergy_unique continuous_weilForm fun v hv hvc => ?_
    have hf : ContDiff ℝ 2 (fun x => (phiDoobTest v x : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_phiDoobTest hv)
    have hfc : HasCompactSupport (fun x => (phiDoobTest v x : ℂ)) :=
      (hasCompactSupport_phiDoobTest hvc).comp_left Complex.ofReal_zero
    rw [weilForm_compactLift, sourceWeilEnergy_compactLift, zeta_W_eq_literatureRHS hf hfc,
      weilFullFunctional_vonMangoldt]
  exact congrFun hfun p

/-- **Complete Six-Way Identity for `compactLift v` across `CHMDPolar`, `CHMDDoobGraph`, `ACT`, `APT`, and `SRT`.**
For every `v ∈ C_c²(ℝ, ℝ)`, the graph Weil form `weilForm (compactLift v hv hvc)` equals:
1. `fullBVWeilExpression v` (`CHMDComplexWeilForm`),
2. `fullZeroForm (phiDoobTest v)` (`ArithmeticCriticalityTheory`),
3. `compactFullWeilEnergy (phiDoobTest v)` (`ArithmeticPositivityTheory`),
4. `(phiDoobArchJumpEnergy v + ∑' n, ∫ x, phiDoobPrimeJump v n x) - polarEnergy v`, and
5. `configurationSquareMass zetaZeroConfig (Φv) - configurationReflectionDefect zetaZeroConfig (Φv)`. -/
theorem weilForm_compactLift_eq_archJump_add_primeJump_sub_polarEnergy
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    weilForm (compactLift v hv hvc) = fullBVWeilExpression v ∧
    weilForm (compactLift v hv hvc) = fullZeroForm (phiDoobTest v) ∧
    weilForm (compactLift v hv hvc) =
      compactFullWeilEnergy ⟨⟨phiDoobTest v, (contDiff_phiDoobTest hv).continuous⟩,
        hasCompactSupport_phiDoobTest hvc⟩ ∧
    weilForm (compactLift v hv hvc) =
      phiDoobArchJumpEnergy v + (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x) - polarEnergy v ∧
    weilForm (compactLift v hv hvc) =
      configurationSquareMass zetaZeroConfig (fun x => (phiDoobTest v x : ℂ)) -
        configurationReflectionDefect zetaZeroConfig (fun x => (phiDoobTest v x : ℂ)) := by
  have hF : ContDiff ℝ 2 (phiDoobTest v) := contDiff_phiDoobTest hv
  have hFc : HasCompactSupport (phiDoobTest v) := hasCompactSupport_phiDoobTest hvc
  have h1 : weilForm (compactLift v hv hvc) = fullZeroForm (phiDoobTest v) := by
    rw [weilForm_compactLift v hv hvc, ← fullZeroForm_eq_zeta_W_re hF hFc]
  have h2 : weilForm (compactLift v hv hvc) =
      compactFullWeilEnergy ⟨⟨phiDoobTest v, hF.continuous⟩, hFc⟩ :=
    h1.trans (fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc)
  have hc : ⟪(compactLift v hv hvc).val.fst, oneL⟫_ℝ = phiDoobCoshMass v :=
    inner_compactLift_oneL v hv hvc
  have hs : ⟪(compactLift v hv hvc).val.fst, tanhL⟫_ℝ = phiDoobSinhMass v := by
    rw [inner_tanhL, phiDoobSinhMass_eq_integral_mass]
    apply integral_congr_ae
    filter_upwards [compactLift_source_ae v hv hvc] with x hx
    rw [hx]
  have hbv : weilForm (compactLift v hv hvc) = fullBVWeilExpression v := by
    unfold weilForm fullBVWeilExpression
    rw [hc, hs, sourceEnergy_compactLift,
      phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass hv hvc]
  have hpol : weilForm (compactLift v hv hvc) =
      phiDoobArchJumpEnergy v + (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x) - polarEnergy v := by
    rw [hbv, polarEnergy_eq_phiDoobMoments (compact_memLp_mass hv.continuous hvc)]
    unfold fullBVWeilExpression
    ring
  have hrefl : weilForm (compactLift v hv hvc) =
      configurationSquareMass zetaZeroConfig (fun x => (phiDoobTest v x : ℂ)) -
        configurationReflectionDefect zetaZeroConfig (fun x => (phiDoobTest v x : ℂ)) := by
    rw [h1, fullZeroForm_eq_zeta_squareMass_sub_reflectionDefect hF hFc]
  exact ⟨hbv, h1, h2, hpol, hrefl⟩

/-- **Polar-Strengthened Odd Doob Dirichlet–Poincaré Criterion for `RiemannHypothesis`.**
Because including the pole term on the odd sector adds `2 phiDoobSinhMass(v)² ≥ 0` to the mass
side (`polarEnergy v = phiDoobCoshMass (v²) + 2 phiDoobSinhMass(v)²`), `RiemannHypothesis` is
equivalent to the strengthened odd-sector inequality
`phiDoobCoshMass (v²) + 2 phiDoobSinhMass(v)² ≤ phiDoobArchJumpEnergy v + ∑' n, ∫ phiDoobPrimeJump v n`. -/
theorem riemannHypothesis_iff_forall_odd_phiDoob_polar_strengthened_poincare :
    RiemannHypothesis ↔
      ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, v (-x) = -v x) →
        phiDoobCoshMass (fun x => v x ^ 2) + 2 * phiDoobSinhMass v ^ 2 ≤
          phiDoobArchJumpEnergy v + ∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x := by
  constructor
  · intro hRH v hv hvc hodd
    have hnn := weilForm_compactLift_nonneg_of_riemannHypothesis hRH v hv hvc
    rw [(weilForm_compactLift_eq_archJump_add_primeJump_sub_polarEnergy v hv hvc).2.2.2.1,
      polarEnergy_eq_coshMass_sq_add_two_sinhMass_sq_of_odd
        (compact_memLp_mass hv.continuous hvc) hodd] at hnn
    linarith
  · intro h
    rw [riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare]
    intro v hv hvc hodd
    have h1 := h v hv hvc hodd
    nlinarith [sq_nonneg (phiDoobSinhMass v)]

/-- **Two-Way Equivalence between `RiemannHypothesis` and Nonnegativity of `CHMDPolar.weilForm`
on the Completed Arithmetic Graph.** -/
theorem riemannHypothesis_iff_weilForm_nonneg :
    RiemannHypothesis ↔ ∀ p : SourceGraph, 0 ≤ weilForm p := by
  refine ⟨weilForm_nonneg_of_riemannHypothesis, fun h => ?_⟩
  rw [riemannHypothesis_iff_forall_odd_phiDoob_polar_strengthened_poincare]
  intro v hv hvc hodd
  have hnn := h (compactLift v hv hvc)
  rw [(weilForm_compactLift_eq_archJump_add_primeJump_sub_polarEnergy v hv hvc).2.2.2.1,
    polarEnergy_eq_coshMass_sq_add_two_sinhMass_sq_of_odd
      (compact_memLp_mass hv.continuous hvc) hodd] at hnn
  linarith

/-- **Two-Way Equivalence between `RiemannHypothesis` and Domination of the Polar Jump Form
by the Arithmetic Jump Form on `SourceGraph`.** -/
theorem riemannHypothesis_iff_polarEnergy_le_edge :
    RiemannHypothesis ↔ ∀ p : SourceGraph, polarEnergy p.val.fst ≤ ‖p.val.snd‖ ^ 2 := by
  rw [riemannHypothesis_iff_weilForm_nonneg]
  refine forall_congr' fun p => ?_
  rw [weilForm_eq_edge_sub_polar p, sub_nonneg]

/-! ## Section 3: Actual-Zeta Depth-Gap Detection, Deep-Companion Forcing, Equal-Depth Clusters, and Dyadic Prime Windows -/

/-- **Explicit-Aperture Actual-Zeta Depth-Gap Detection by Single-Scale Grid Tent Patterns.**
There exists an unconditional local-count constant `A₀ ≥ 1` such that for any zero
`ρ₀ ∈ zetaZeroConfig.carrier` of depth `δ > 0` (`ρ₀.re = 1/2 + δ`), if every other zero within
ordinate distance `R ≥ 0` (except `ρ₀` and `reflect ρ₀`) has depth at most `δ'`, and the explicit
depth-gap size condition holds at aperture `a`, then there exist a seed `G ∈ C_c²(ℝ, ℝ)` supported
in `[-a, a]` and a margin `μ > 0` such that the single-scale grid factorial-tent pattern on
`[-(a+1), a+1]` and its smoothed detector detect `ρ₀` with margin `μ` for all large `n`. -/
theorem actual_zeta_depthGap_detected_by_gridTentPattern_at_aperture :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → ∀ {δ : ℝ}, 0 < δ → ρ₀.re = 1 / 2 + δ →
      ∀ {a R w δ' : ℝ}, 0 ≤ R → 0 < w → w ≤ a / 4 →
        (∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ reflect ρ₀ → |ρ.im - ρ₀.im| ≤ R →
          |ρ.re - 1 / 2| ≤ δ') →
        384 * A₀ * Real.log (|ρ₀.im| + 3) *
            (2 * a * Real.cosh (δ * a) *
              (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
            (Real.exp (δ' * a) ^ 2 + Real.exp a / (1 + R)) <
          2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2 →
        ∃ (G : ℝ → ℝ) (μ : ℝ), ContDiff ℝ 2 G ∧ HasCompactSupport G ∧
          (∀ x, a < |x| → G x = 0) ∧ 0 < μ ∧
          ∀ᶠ n : ℕ in atTop,
            let M : ℕ := ⌈2 * (a + 1) / sourceFactorialWidth (n + 1)⌉₊
            let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(a + 1)) M
            compactFullWeilEnergy P ≤ -2 * μ ∧
            fullZeroForm P ≤ -2 * μ ∧
            ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
              let D : ℝ → ℂ := smoothGridTentDetector G n (-(a + 1)) M q
              ContDiff ℝ 2 D ∧
              HasCompactSupport D ∧
              |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
                  (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
              (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
                  (EF.weilTest D D)).re ≤ -μ ∧
              (zetaZeroConfig.W D D).re ≤ -μ ∧
              μ ≤ configurationReflectionDefect zetaZeroConfig D -
                configurationSquareMass zetaZeroConfig D := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A₀, hA₀, ?_⟩
  intro ρ₀ hρ₀ δ hδ hre a R w δ' hR hw hwa hgap hbig
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨f, hf, hfs, hneg⟩ :=
    exists_re_W_neg_of_depthGap_deep_zero zetaZeroConfig hA₀ hloc hρ₀ hδ hre hR hw hwa hgap hbig
  have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  have hfa : ∀ x, a < |x| → f x = 0 := fun x hx => by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := abs_le.mpr (hfs hmem)
    linarith
  obtain ⟨φ, hφ, hφc, hφa, -, hφneg⟩ :=
    exists_real_contDiff_fullZeroForm_neg_of_zeta_W_neg hf hfc hfa hneg
  have hspec := gridTentPattern_actual_zeta_detector_spec hφ hφc ha0 hφa hφneg
  refine ⟨fun x => Real.exp (-(3 * x / 2)) * φ x, -fullZeroForm φ / 4,
    by fun_prop, hφc.mul_left, fun x hx => by simp [hφa x hx], hspec.1, hspec.2⟩

/-- **Contrapositive Deep-Companion Forcing from Single-Scale Grid Tent Positivity at Aperture `a`.**
If single-scale grid factorial-tent patterns generated by seeds `G ∈ C_c²(ℝ, ℝ)` supported in
`[-a, a]` have eventually nonnegative `compactFullWeilEnergy`, then every zero
`ρ₀ ∈ zetaZeroConfig.carrier` of depth `δ > 0` (`ρ₀.re = 1/2 + δ`) satisfying the depth-gap size
condition at `a` is forced to have a companion zero `ρ ≠ ρ₀, reflect ρ₀` within ordinate distance
`R` of depth strictly greater than `δ'`. -/
theorem zeta_gridTentPattern_nonneg_forces_deep_companion :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ (a : ℝ),
        (∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, a < |x| → G x = 0) →
          ∀ᶠ n : ℕ in atTop,
            0 ≤ compactFullWeilEnergy
              (gridTentPattern G n (-(a + 1)) ⌈2 * (a + 1) / sourceFactorialWidth (n + 1)⌉₊)) →
        ∀ ρ₀ ∈ zetaZeroConfig.carrier, ∀ δ : ℝ, 0 < δ → ρ₀.re = 1 / 2 + δ →
        ∀ R w δ' : ℝ, 0 ≤ R → 0 < w → w ≤ a / 4 →
          384 * A₀ * Real.log (|ρ₀.im| + 3) *
              (2 * a * Real.cosh (δ * a) *
                (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
              (Real.exp (δ' * a) ^ 2 + Real.exp a / (1 + R)) <
            2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2 →
          ∃ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ ∧ |ρ.im - ρ₀.im| ≤ R ∧
            δ' < |ρ.re - 1 / 2| := by
  obtain ⟨A₀, hA₀, hdet⟩ := actual_zeta_depthGap_detected_by_gridTentPattern_at_aperture
  refine ⟨A₀, hA₀, fun a hpos ρ₀ hρ₀ δ hδ hre R w δ' hR hw hwa hbig => ?_⟩
  by_contra hno
  simp only [not_exists, not_and, not_lt] at hno
  obtain ⟨G, μ, hG, hGc, hGa, hμ, hev⟩ := hdet hρ₀ hδ hre hR hw hwa hno hbig
  obtain ⟨n, hn_neg, hn_pos⟩ := (hev.and (hpos G hG hGc hGa)).exists
  linarith [hn_neg.1]

/-- **Explicit-Aperture Equal-Depth Cluster Detection by Single-Scale Grid Tent Patterns.**
If all off-line zeros of `zetaZeroConfig` form `n > 0` simple pairs `1/2 ± δ + i γ_k` of common
depth `δ > 0` in an arbitrary on-line background, and the grid `ℓ > 0` separates `e^{i γ_k ℓ}` with
nonzero pair weights `pairWeight b δ (γ k) ≠ 0`, then there exists `c > 0` such that at every
logarithmic aperture `a ≥ (1/2δ) log⁺((2 M_b + 3 Σ_k ‖Q_k‖)/c) + (n + 2)ℓ/2 + w`, single-scale
grid factorial-tent patterns and their smoothed detectors detect the cluster with margin `μ > 0`. -/
theorem actual_zeta_equalDepthCluster_detected_by_gridTentPattern_at_aperture
    {n : ℕ} (hn : 0 < n) (γ : Fin n → ℝ) (hγ : Function.Injective γ) {δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ k, heightPoint δ (γ k) ∈ zetaZeroConfig.carrier)
    (hm : ∀ k, heightPoint (-δ) (γ k) ∈ zetaZeroConfig.carrier)
    (hmp : ∀ k, zetaZeroConfig.mult (heightPoint δ (γ k)) = 1)
    (hmm : ∀ k, zetaZeroConfig.mult (heightPoint (-δ) (γ k)) = 1)
    (hon : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 ∨
      ∃ k, ρ = heightPoint δ (γ k) ∨ ρ = heightPoint (-δ) (γ k))
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hw : 0 ≤ w) (hbs : ∀ u, b u ≠ 0 → |u| ≤ w)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hsep : Function.Injective fun k => cexp (I * γ k * ℓ))
    (hQ : ∀ k, pairWeight b δ (γ k) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ,
      1 / (2 * δ) * max 0 (Real.log ((2 * onLineMassOf zetaZeroConfig b +
        3 * ∑ k, ‖pairWeight b δ (γ k)‖) / c)) + (n + 2) * ℓ / 2 + w ≤ a →
        ∃ (G : ℝ → ℝ) (μ : ℝ), ContDiff ℝ 2 G ∧ HasCompactSupport G ∧
          (∀ x, a < |x| → G x = 0) ∧ 0 < μ ∧
          ∀ᶠ m : ℕ in atTop,
            let M : ℕ := ⌈2 * (a + 1) / sourceFactorialWidth (m + 1)⌉₊
            let P : C_c(ℝ, ℝ) := gridTentPattern G m (-(a + 1)) M
            compactFullWeilEnergy P ≤ -2 * μ ∧
            fullZeroForm P ≤ -2 * μ ∧
            ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
              let D : ℝ → ℂ := smoothGridTentDetector G m (-(a + 1)) M q
              ContDiff ℝ 2 D ∧
              HasCompactSupport D ∧
              |(weilFullFunctional (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
                  (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
              (weilFullFunctional (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
                  (EF.weilTest D D)).re ≤ -μ ∧
              (zetaZeroConfig.W D D).re ≤ -μ ∧
              μ ≤ configurationReflectionDefect zetaZeroConfig D -
                configurationSquareMass zetaZeroConfig D := by
  obtain ⟨c, hc, hvis⟩ := equalDepthCluster_visible zetaZeroConfig temperedConfig_zetaZeroConfig
    hn γ hγ hδ hp hm hmp hmm hon hb hbs hℓ hsep hQ
  refine ⟨c, hc, fun a ha => ?_⟩
  have ha0 : 0 ≤ a := by
    have h1 : 0 ≤ 1 / (2 * δ) * max 0 (Real.log ((2 * onLineMassOf zetaZeroConfig b +
        3 * ∑ k, ‖pairWeight b δ (γ k)‖) / c)) := by positivity
    have h2 : 0 ≤ (n + 2 : ℝ) * ℓ / 2 := by positivity
    linarith
  obtain ⟨f, hf, hfs, hneg⟩ := hvis a ha
  have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  have hfa : ∀ x, a < |x| → f x = 0 := fun x hx => by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := abs_le.mpr (hfs hmem)
    linarith
  obtain ⟨φ, hφ, hφc, hφa, -, hφneg⟩ :=
    exists_real_contDiff_fullZeroForm_neg_of_zeta_W_neg hf hfc hfa hneg
  have hspec := gridTentPattern_actual_zeta_detector_spec hφ hφc ha0 hφa hφneg
  refine ⟨fun x => Real.exp (-(3 * x / 2)) * φ x, -fullZeroForm φ / 4,
    by fun_prop, hφc.mul_left, fun x hx => by simp [hφa x hx], hspec.1, hspec.2⟩

/-- **Dyadic Prime-Window Reflection-Defect Identity.**
For `0 < w < (log 2)/2` and `v ≥ 0`, the real part of the single dyadic prime-window functional
`lagPrimeWindowRHS v w` on the two-bump test `twoBump (modScaledBump w γ) v τ` equals the exact
global zero-side difference `configurationSquareMass zetaZeroConfig - configurationReflectionDefect zetaZeroConfig`. -/
theorem lagPrimeWindowRHS_re_eq_zeta_squareMass_sub_reflectionDefect
    {w : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) (γ : ℝ) {v : ℝ} (hv : 0 ≤ v) (τ : ℂ) :
    let f : ℝ → ℂ := twoBump (modScaledBump w γ) v τ
    (lagPrimeWindowRHS v w (EF.weilTest f f)).re =
      configurationSquareMass zetaZeroConfig f -
        configurationReflectionDefect zetaZeroConfig f := by
  dsimp only
  set f : ℝ → ℂ := twoBump (modScaledBump w γ) v τ
  have hf : ContDiff ℝ 2 f := contDiff_bumpTest (contDiff_modScaledBump_two w γ) v ![1, τ]
  have hfc : HasCompactSupport f :=
    hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs (modScaledBump_support hw γ)) v τ
  rw [← literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw γ) hw2 hv,
    ← zeta_W_eq_literatureRHS hf hfc, ← zeta_squareMass_sub_re_W_eq_reflectionDefect hf hfc]
  ring

/-- **Exponential Reflection-Defect Excess on Large Dyadic Prime Windows.**
If `ρ ∈ zetaZeroConfig.carrier` has depth `|ρ.re - 1/2| > σ ≥ 0`, then for every `0 < w < (log 2)/2`
and every `K, V : ℝ` (`0 ≤ V`), there exist a height `γ`, a lag `v ≥ V`, and a unimodular `τ`
(`‖τ‖ = 1`) such that on the single dyadic prime-window two-bump test `f = twoBump (modScaledBump w γ) v τ`,
`configurationReflectionDefect zetaZeroConfig f - configurationSquareMass zetaZeroConfig f > K e^{σv}`. -/
theorem zeta_exists_twoBump_reflectionDefect_sub_squareMass_gt
    {w : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < |ρ.re - 1 / 2|)
    (K : ℝ) {V : ℝ} (hV : 0 ≤ V) :
    ∃ (γ v : ℝ) (τ : ℂ), V ≤ v ∧ ‖τ‖ = 1 ∧
      K * Real.exp (σ * v) <
        configurationReflectionDefect zetaZeroConfig (twoBump (modScaledBump w γ) v τ) -
          configurationSquareMass zetaZeroConfig (twoBump (modScaledBump w γ) v τ) := by
  obtain ⟨γ, v, τ, hVv, hτ, hlt⟩ := zeta_exists_primeWindow_lt hw hw2 hρ hσ0 hσ K V
  refine ⟨γ, v, τ, hVv, hτ, ?_⟩
  have heq := lagPrimeWindowRHS_re_eq_zeta_squareMass_sub_reflectionDefect hw hw2 γ (hV.trans hVv) τ
  linarith

/-! ## Section 4: Attained-Depth Detection and the `AsymptoticAbscissaLaw` / `ZerosApproachLine` Bridge -/

/-- **Unconditional Actual-Zeta Attained-Depth Detection by Single-Scale Grid Tent Patterns.**
If `t₀ ∈ zetaZeroConfig.carrier` is right of the critical line (`1/2 < t₀.re`) and attains the
maximal real part of `zetaZeroConfig.carrier`, then `t₀` is unconditionally detected (via
Abel–Cesàro grid two-bump seeds, with no depth-gap or finiteness assumption) by single-scale grid
factorial-tent patterns and their smoothed detectors with margin `μ > 0`. -/
theorem actual_zeta_attainedDepth_detected_by_gridTentPattern
    {t₀ : ℂ} (ht₀ : t₀ ∈ zetaZeroConfig.carrier) (hre : 1 / 2 < t₀.re)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ t₀.re) :
    ∃ (G : ℝ → ℝ) (R μ : ℝ), ContDiff ℝ 2 G ∧ HasCompactSupport G ∧ 0 ≤ R ∧ 0 < μ ∧
      ∀ᶠ n : ℕ in atTop,
        let M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M
        compactFullWeilEnergy P ≤ -2 * μ ∧
        fullZeroForm P ≤ -2 * μ ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
          (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re ≤ -μ ∧
          (zetaZeroConfig.W D D).re ≤ -μ ∧
          μ ≤ configurationReflectionDefect zetaZeroConfig D -
            configurationSquareMass zetaZeroConfig D := by
  obtain ⟨f, hf, hfc, hneg⟩ :=
    attainedDepth_visible zetaZeroConfig temperedConfig_zetaZeroConfig ht₀ hre htop
  obtain ⟨R, hR, hfR⟩ := exists_radius_bound hfc
  have hfR' : ∀ x, R < |x| → f x = 0 := fun x hx => by
    by_contra hne
    exact not_le.mpr hx (hfR x hne)
  obtain ⟨φ, hφ, hφc, hφR, -, hφneg⟩ :=
    exists_real_contDiff_fullZeroForm_neg_of_zeta_W_neg hf hfc hfR' hneg
  have hspec := gridTentPattern_actual_zeta_detector_spec hφ hφc hR hφR hφneg
  refine ⟨fun x => Real.exp (-(3 * x / 2)) * φ x, R, -fullZeroForm φ / 4,
    by fun_prop, hφc.mul_left, hR, hspec.1, hspec.2⟩

/-- **Bridge from `RHTower.AttainedTop` (`XiZeroCopy`) to `SquareRootThreshold` Attained Maximal Depth
(`zetaZeroConfig.carrier`).** -/
theorem exists_zeta_attainedDepth_of_attainedTop {β₀ : ℝ} (hβ₀ : 1 / 2 < β₀)
    (htop : AttainedTop β₀) :
    ∃ t₀ ∈ zetaZeroConfig.carrier, t₀.re = β₀ ∧ 1 / 2 < t₀.re ∧
      ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ t₀.re := by
  obtain ⟨⟨q₁, hq₁_re⟩, hmax⟩ := htop
  set t₀ : ℂ := (q₁.1 : ℂ)
  have ht₀_re : 1 / 2 < t₀.re := by dsimp [t₀]; linarith
  have ht₀_lt1 : t₀.re < 1 := xiZeroCopy_re_lt_one q₁
  have ht₀_ne1 : t₀ ≠ 1 := by
    intro h1
    rw [h1, Complex.one_re] at ht₀_lt1
    exact lt_irrefl 1 ht₀_lt1
  have hζ : riemannZeta t₀ = 0 :=
    (xi_eq_zero_iff (by linarith) ht₀_ne1).mp (xi_xiZeroCopy_eq_zero q₁)
  have ht₀_mem : t₀ ∈ zetaZeroConfig.carrier := ⟨hζ, by linarith, ht₀_lt1⟩
  refine ⟨t₀, ht₀_mem, hq₁_re, ht₀_re, fun ρ hρ => ?_⟩
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hρ.1 hρ.2.1 hρ.2.2
  rw [← hq, hq₁_re]
  exact hmax q

/-- **Single-Scale Grid Factorial-Tent Positivity Produces `AsymptoticAbscissaLaw` via `attainedDepth_visible`.**
Eventual nonnegativity of `compactFullWeilEnergy` on single-scale grid factorial-tent patterns
rules out any attained maximal abscissa `β₀ > 1/2` by `actual_zeta_attainedDepth_detected_by_gridTentPattern`,
and therefore unconditionally produces `RHTower.AsymptoticAbscissaLaw`. -/
theorem asymptoticAbscissaLaw_of_eventually_gridTentPattern_nonneg
    (h : ∀ (G : ℝ → ℝ) (R : ℝ), 0 ≤ R →
      ∀ᶠ n : ℕ in atTop,
        0 ≤ compactFullWeilEnergy
          (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊)) :
    AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_not_attainedTop ?_
  rintro ⟨β₀, hβ₀, htop⟩
  obtain ⟨t₀, ht₀_mem, -, ht₀_re, ht₀_max⟩ := exists_zeta_attainedDepth_of_attainedTop hβ₀ htop
  obtain ⟨G, R, μ, -, -, hR, hμ, hev⟩ :=
    actual_zeta_attainedDepth_detected_by_gridTentPattern ht₀_mem ht₀_re ht₀_max
  obtain ⟨n, hn_neg, hn_pos⟩ := (hev.and (h G R hR)).exists
  linarith [hn_neg.1]

/-- **Diagnostic Split Equivalence: `ZerosApproachLine` + Eventual Grid-Tent Positivity `↔ RiemannHypothesis`.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_eventually_gridTentPattern_nonneg :
    RiemannHypothesis ↔
      ZerosApproachLine ∧
        ∀ (G : ℝ → ℝ) (R : ℝ), 0 ≤ R →
          ∀ᶠ n : ℕ in atTop,
            0 ≤ compactFullWeilEnergy
              (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊) := by
  constructor
  · intro hRH
    exact ⟨(riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mp hRH).1,
      riemannHypothesis_iff_eventually_gridTentPattern_nonneg.mp hRH⟩
  · rintro ⟨hZAL, hTent⟩
    exact riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr
      ⟨hZAL, asymptoticAbscissaLaw_of_eventually_gridTentPattern_nonneg hTent⟩

/-- **Diagnostic Split Equivalence: `EventualSlicePositivity` + Eventual Grid-Tent Positivity `↔ RiemannHypothesis`.** -/
theorem riemannHypothesis_iff_eventualSlicePositivity_and_eventually_gridTentPattern_nonneg :
    RiemannHypothesis ↔
      EventualSlicePositivity ∧
        ∀ (G : ℝ → ℝ) (R : ℝ), 0 ≤ R →
          ∀ᶠ n : ℕ in atTop,
            0 ≤ compactFullWeilEnergy
              (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊) := by
  constructor
  · intro hRH
    have hFOL : FiniteOffLine := by
      refine Set.finite_empty.subset fun q hq => ?_
      have hq' : (xiSpectralPoint q).im ≠ 0 := hq
      apply hq'
      rw [spectral_im_eq, xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q, sub_self]
    exact ⟨eventualSlicePositivity_of_finiteOffLine hFOL,
      riemannHypothesis_iff_eventually_gridTentPattern_nonneg.mp hRH⟩
  · rintro ⟨hSlice, hTent⟩
    have hZAL : ZerosApproachLine :=
      zerosApproachLine_of_finiteOffLine (finiteOffLine_of_eventualSlicePositivity hSlice)
    exact riemannHypothesis_iff_zerosApproachLine_and_eventually_gridTentPattern_nonneg.mpr
      ⟨hZAL, hTent⟩

end GaloisForLFunctions.ArithmeticPositivityTheory
end
