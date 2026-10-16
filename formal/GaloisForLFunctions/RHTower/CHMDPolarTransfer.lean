import GaloisForLFunctions.RHTower.CHMDPolarJumpForm
import GaloisForLFunctions.RHTower.CHMDThetaCriticalModes
import GaloisForLFunctions.RHTower.CHMDPrimitiveCuspEscape
import GaloisForLFunctions.RHTower.CHMDFullJumpCoreDensity
import GaloisForLFunctions.RHTower.WeilMarkovOnePoleHyperplane

/-!
# Polar transfer: the complete Weil form on the arithmetic jump graph

The signed Doob energy on the complete arithmetic graph is the jump energy minus the theta–cosh
mass. Adding the pole term `2⟨v,1⟩² − 2⟨v,tanh(·/2)⟩²` of the Weil functional gives the complete
Weil form of `Θv`. By the polar identity the mass plus the pole term is exactly the polar jump
energy, so the complete Weil form on the whole completed graph is

`W(Θv) = ‖edge v‖² − ∫∫ cosh((x−y)/2) Θ(x)Θ(y) (v(x)−v(y))²`,

the difference of two jump Dirichlet forms over the same theta geometry. No negative mass term
remains. On compact `C²` tests the form is literally the real part of the Weil form of `Θv`; it is
continuous on the complete graph, vanishes on every exact critical mode, and tends to zero along the
primitive cusp escape. Under the Riemann hypothesis the arithmetic jump energy dominates the polar
jump energy on the entire completed graph.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph

theorem memLp_tanhHalf : MemLp tanhHalf 2 massMeasure :=
  MemLp.of_bound continuous_tanhHalf.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_tanhHalf_le_one x)

/-- The odd polar direction `tanh(x/2)` as a vector of the mass space. -/
def tanhL : Lp ℝ 2 massMeasure := memLp_tanhHalf.toLp tanhHalf

/-- The ground vector `1` of the mass space. -/
def oneL : Lp ℝ 2 massMeasure :=
  (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).toLp _

theorem oneL_eq_constantLift : oneL = (constantLift 1).val.fst := rfl

theorem inner_toLp_right (f : Lp ℝ 2 massMeasure) {g : ℝ → ℝ} (hg : MemLp g 2 massMeasure) :
    ⟪f, hg.toLp g⟫_ℝ = ∫ x, f x * g x ∂massMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  change inner ℝ (f x) (hg.toLp g x) = _
  simp [hx, mul_comm]

theorem inner_oneL (f : Lp ℝ 2 massMeasure) : ⟪f, oneL⟫_ℝ = ∫ x, f x ∂massMeasure := by
  unfold oneL
  rw [inner_toLp_right]
  simp only [mul_one]

theorem inner_tanhL (f : Lp ℝ 2 massMeasure) :
    ⟪f, tanhL⟫_ℝ = ∫ x, f x * tanhHalf x ∂massMeasure :=
  inner_toLp_right f memLp_tanhHalf

theorem norm_sq_eq_integral (f : Lp ℝ 2 massMeasure) :
    ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂massMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp [pow_two]

/-- **The complete Weil form** on the arithmetic graph: signed Doob energy plus the pole term. -/
def weilForm (p : SourceGraph) : ℝ :=
  sourceEnergy p + 2 * ⟪p.val.fst, oneL⟫_ℝ ^ 2 - 2 * ⟪p.val.fst, tanhL⟫_ℝ ^ 2

/-- **Polar transfer.** The complete Weil form is the arithmetic jump energy minus the polar jump
energy; the theta–cosh mass has been absorbed into the polar jump form. -/
theorem weilForm_eq_edge_sub_polar (p : SourceGraph) :
    weilForm p = ‖p.val.snd‖ ^ 2 - polarEnergy p.val.fst := by
  unfold weilForm
  change ‖p.val.snd‖ ^ 2 - ‖p.val.fst‖ ^ 2 + _ - _ = _
  rw [polarEnergy_eq (Lp.memLp p.val.fst), inner_oneL, inner_tanhL, norm_sq_eq_integral]
  ring

theorem weilForm_le_edge (p : SourceGraph) : weilForm p ≤ ‖p.val.snd‖ ^ 2 := by
  rw [weilForm_eq_edge_sub_polar]
  linarith [polarEnergy_nonneg p.val.fst]

theorem continuous_weilForm : Continuous weilForm := by
  unfold weilForm
  have h1 : Continuous fun p : SourceGraph => ⟪p.val.fst, oneL⟫_ℝ :=
    sourceMap.continuous.inner continuous_const
  have h2 : Continuous fun p : SourceGraph => ⟪p.val.fst, tanhL⟫_ℝ :=
    sourceMap.continuous.inner continuous_const
  exact (continuous_sourceEnergy.add ((h1.pow 2).const_mul 2)).sub ((h2.pow 2).const_mul 2)

/-! ## Compact tests: the literal Weil form of `Θv` -/

theorem compactLift_source_ae (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    (compactLift v hv hvc).val.fst =ᵐ[massMeasure] v :=
  (compact_memLp_mass hv.continuous hvc).coeFn_toLp

theorem phiDoobCoshMass_eq_integral_mass (v : ℝ → ℝ) :
    phiDoobCoshMass v = ∫ x, v x ∂massMeasure := by
  rw [integral_mass]
  unfold phiDoobCoshMass phiDoobTest massDensity
  congr 1
  funext x
  ring

theorem phiDoobSinhMass_eq_integral_mass (v : ℝ → ℝ) :
    phiDoobSinhMass v = ∫ x, v x * tanhHalf x ∂massMeasure := by
  rw [integral_mass]
  unfold phiDoobSinhMass phiDoobTest
  congr 1
  funext x
  have h := sinhDensity_eq x
  unfold sinhDensity at h
  linear_combination v x * h

/-- On compact `C²` tests the complete Weil form is the real part of the actual Weil form of
`Θv`, the pole term included. -/
theorem weilForm_compactLift (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    weilForm (compactLift v hv hvc) =
      (zetaZeroConfig.W (fun x => (phiDoobTest v x : ℂ)) (fun x => (phiDoobTest v x : ℂ))).re := by
  have hf : ContDiff ℝ 2 (fun x => (phiDoobTest v x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_phiDoobTest hv)
  have hfc : HasCompactSupport (fun x => (phiDoobTest v x : ℂ)) :=
    (hasCompactSupport_phiDoobTest hvc).comp_left Complex.ofReal_zero
  have hc : ⟪(compactLift v hv hvc).val.fst, oneL⟫_ℝ = phiDoobCoshMass v := by
    rw [inner_oneL, phiDoobCoshMass_eq_integral_mass]
    exact integral_congr_ae (compactLift_source_ae v hv hvc)
  have hs : ⟪(compactLift v hv hvc).val.fst, tanhL⟫_ℝ = phiDoobSinhMass v := by
    rw [inner_tanhL, phiDoobSinhMass_eq_integral_mass]
    apply integral_congr_ae
    filter_upwards [compactLift_source_ae v hv hvc] with x hx
    rw [hx]
  unfold weilForm
  rw [hc, hs, sourceEnergy_compactLift, markovEnergy_eq_W_sub hf hfc, phiDoob_pole hv.continuous hvc]
  ring

/-- The Weil form of a compact test as arithmetic jump energy minus polar jump energy. -/
theorem W_re_eq_edge_sub_polar (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    (zetaZeroConfig.W (fun x => (phiDoobTest v x : ℂ)) (fun x => (phiDoobTest v x : ℂ))).re =
      ‖(compactLift v hv hvc).val.snd‖ ^ 2 - polarEnergy (compactLift v hv hvc).val.fst := by
  rw [← weilForm_compactLift, weilForm_eq_edge_sub_polar]

/-! ## The critical band and the cusp escape -/

theorem massDensity_neg (x : ℝ) : massDensity (-x) = massDensity x := by
  unfold massDensity
  rw [WeilExcess.riemannKernelReal_neg, neg_div, Real.cosh_neg]

theorem tanhHalf_neg (x : ℝ) : tanhHalf (-x) = -tanhHalf x := by
  unfold tanhHalf
  rw [neg_div, Real.tanh_neg]

theorem ratio_neg_arg (a x : ℝ) : CHMDThetaTranslate.ratio a (-x) = CHMDThetaTranslate.ratio (-a) x := by
  unfold CHMDThetaTranslate.ratio
  rw [show -x - a = -(x - -a) by ring, WeilExcess.riemannKernelReal_neg,
    WeilExcess.riemannKernelReal_neg]

theorem criticalFunction_neg (a x : ℝ) :
    CHMDThetaTranslate.criticalFunction a (-x) = CHMDThetaTranslate.criticalFunction a x := by
  unfold CHMDThetaTranslate.criticalFunction
  rw [ratio_neg_arg, ratio_neg_arg, neg_neg]
  ring

/-- An odd Lebesgue integrand has zero integral. -/
theorem integral_eq_zero_of_odd {g : ℝ → ℝ} (hg : ∀ x, g (-x) = -g x) : (∫ x, g x) = 0 := by
  have h := integral_neg_eq_self g (volume : Measure ℝ)
  simp only [hg, integral_neg] at h
  linarith

/-- Exact critical modes are polar-orthogonal to the odd direction. -/
theorem critical_inner_tanhL (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    ⟪(CHMDThetaTranslate.critical a ha).val.fst, tanhL⟫_ℝ = 0 := by
  rw [inner_tanhL]
  have hae : (∫ x, (CHMDThetaTranslate.critical a ha).val.fst x * tanhHalf x ∂massMeasure) =
      ∫ x, CHMDThetaTranslate.criticalFunction a x * tanhHalf x ∂massMeasure := by
    apply integral_congr_ae
    filter_upwards [CHMDThetaTranslate.critical_source_ae a ha] with x hx
    rw [hx]
  rw [hae, integral_mass]
  apply integral_eq_zero_of_odd
  intro x
  rw [massDensity_neg, criticalFunction_neg, tanhHalf_neg]
  ring

/-- The complete Weil form vanishes on every exact critical mode. -/
theorem weilForm_critical (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    weilForm (CHMDThetaTranslate.critical a ha) = 0 := by
  unfold weilForm
  rw [CHMDThetaTranslate.critical_energy, oneL_eq_constantLift,
    CHMDThetaTranslate.critical_primitive, critical_inner_tanhL]
  ring

theorem sinhHalfMoment_translate {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t : ℝ) :
    sinhHalfMoment (CHMDTranslation.translate f t) =
      coshHalfMoment f * Real.sinh (t / 2) + sinhHalfMoment f * Real.cosh (t / 2) := by
  have hc : Integrable (fun x => f x * Real.cosh (x / 2)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hs : Integrable (fun x => f x * Real.sinh (x / 2)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  unfold coshHalfMoment sinhHalfMoment
  rw [← integral_add_right_eq_self (fun x => CHMDTranslation.translate f t x * Real.sinh (x / 2)) t]
  simp only [CHMDTranslation.translate, add_sub_cancel_right]
  have he (x : ℝ) : f x * Real.sinh ((x + t) / 2) =
      (f x * Real.cosh (x / 2)) * Real.sinh (t / 2) +
        (f x * Real.sinh (x / 2)) * Real.cosh (t / 2) := by
    rw [add_div, Real.sinh_add]
    ring
  simp_rw [he]
  rw [integral_add (hc.mul_const _) (hs.mul_const _), integral_mul_const, integral_mul_const]

theorem escape_inner_tanhL (t : ℝ) : ⟪CHMDEscape.source (CHMDEscape.lift t), tanhL⟫_ℝ = 0 := by
  change ⟪(CHMDEscape.lift t).val.fst, tanhL⟫_ℝ = 0
  rw [inner_tanhL]
  have hae : (∫ x, (CHMDEscape.lift t).val.fst x * tanhHalf x ∂massMeasure) =
      ∫ x, CHMDEscape.test t x * tanhHalf x ∂massMeasure := by
    apply integral_congr_ae
    filter_upwards [CHMDEscape.lift_source_ae t] with x hx
    exact congrArg (fun r => r * tanhHalf x) hx
  rw [hae, integral_mass]
  have hpt (x : ℝ) : massDensity x * (CHMDEscape.test t x * tanhHalf x) =
      CHMDTranslation.translate CHMDTranslation.profile t x * Real.sinh (x / 2) := by
    unfold CHMDEscape.test phiDoobInv massDensity tanhHalf
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(riemannKernelReal_pos x).ne', (Real.cosh_pos (x / 2)).ne']
  simp_rw [hpt]
  change sinhHalfMoment (CHMDTranslation.translate CHMDTranslation.profile t) = 0
  rw [sinhHalfMoment_translate CHMDTranslation.profile_contDiff.continuous
    CHMDTranslation.profile_compact, CHMDTranslation.profile_moments.1,
    CHMDTranslation.profile_moments.2]
  ring

/-- Along the primitive cusp escape the complete Weil form is the signed energy. -/
theorem weilForm_normalized (t : ℝ) :
    weilForm (CHMDEscape.normalized t) = sourceEnergy (CHMDEscape.normalized t) := by
  unfold weilForm
  have h1 : ⟪(CHMDEscape.normalized t).val.fst, oneL⟫_ℝ = 0 := by
    have := CHMDEscape.normalized_primitive t
    unfold CHMDEscape.Primitive at this
    rw [oneL_eq_constantLift]
    exact this
  have h2 : ⟪(CHMDEscape.normalized t).val.fst, tanhL⟫_ℝ = 0 := by
    change ⟪CHMDEscape.source (CHMDEscape.normalized t), tanhL⟫_ℝ = 0
    rw [CHMDEscape.normalized, CHMDEscape.source_smul, real_inner_smul_left, escape_inner_tanhL,
      mul_zero]
  rw [h1, h2]
  ring

/-- The complete Weil form has no positive margin on unit-mass primitive vectors: it tends to
zero along the cusp escape. -/
theorem weilForm_normalized_tendsto_zero :
    Tendsto (fun t => weilForm (CHMDEscape.normalized t)) atTop (𝓝 0) := by
  simp only [weilForm_normalized]
  exact CHMDEscape.normalized_energy_zero

/-! ## Riemann hypothesis: arithmetic domination of the polar jump form -/

/-- Under the Riemann hypothesis the complete Weil form is nonnegative on every compact test. -/
theorem weilForm_compactLift_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    0 ≤ weilForm (compactLift v hv hvc) := by
  rw [weilForm_compactLift]
  exact W_re_nonneg_of_riemannHypothesis hRH
    (Complex.ofRealCLM.contDiff.comp (contDiff_phiDoobTest hv))
    ((hasCompactSupport_phiDoobTest hvc).comp_left Complex.ofReal_zero)

/-- Under the Riemann hypothesis the complete Weil form is nonnegative on the entire completed
graph: compact tests are dense and the form is continuous. -/
theorem weilForm_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) (p : SourceGraph) :
    0 ≤ weilForm p := by
  have hclosed : IsClosed {q : SourceGraph | 0 ≤ weilForm q} :=
    isClosed_le continuous_const continuous_weilForm
  have hsub : (compactTests : Set SourceGraph) ⊆ {q : SourceGraph | 0 ≤ weilForm q} := by
    rintro q ⟨v, hv, hvc, rfl⟩
    exact weilForm_compactLift_nonneg_of_riemannHypothesis hRH v hv hvc
  have hall : (univ : Set SourceGraph) ⊆ {q : SourceGraph | 0 ≤ weilForm q} := by
    rw [← dense_compactTests.closure_eq]
    exact closure_minimal hsub hclosed
  exact hall (mem_univ p)

/-- Under the Riemann hypothesis the arithmetic jump energy dominates the polar jump energy on the
entire completed graph. -/
theorem polarEnergy_le_edge_of_riemannHypothesis (hRH : RiemannHypothesis) (p : SourceGraph) :
    polarEnergy p.val.fst ≤ ‖p.val.snd‖ ^ 2 := by
  have h := weilForm_nonneg_of_riemannHypothesis hRH p
  rw [weilForm_eq_edge_sub_polar] at h
  linarith

end RHTower.CHMDPolar
