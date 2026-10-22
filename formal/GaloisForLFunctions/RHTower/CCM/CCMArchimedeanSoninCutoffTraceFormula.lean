import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanSoninGenericDecomposition
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanConvolutionRepresentation
import GaloisForLFunctions.RHTower.SoninLogShellCocycle
import GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier
import GaloisForLFunctions.HTGeometry.SchurKernelComposition
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import GaloisForLFunctions.RHTower.RectangularSemilocalObserverTailSeparation
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten
import GaloisForLFunctions.RHTower.SoninTimeBandSchatten

/-!
# The Sonin trace formula at an arbitrary cutoff

In logarithmic coordinates `t = log |x|` the integrated scaling action `ϑ(g)` on `L²(ℝ)^ev` is the
convolution `C_g` with kernel `g(t - s)`, and the physical shell `P_Λ - P₁` is the interval cutoff
`1_{(0, log Λ]}`.  Hence `ϑ(g)(P_Λ - P₁)ϑ(g)† = C_g 1 C_g†` is a product of two Hilbert--Schmidt
kernel operators with trace `log Λ ∫ |g|²`; the Fourier shell `P̂_Λ - P̂₁` gives the same value
since `F ϑ(g) = ϑ(ǧ) F`.  Combined with the cutoff-one Weil trace formula this is the Sonin trace formula

`-W(g★ ⋆ g) = 2 log Λ · ‖g‖² + Tr(ϑ(g) S_Λ ϑ(g)†) + Tr(ϑ(g) G_Λ ϑ(g)†)`,   `Λ > 1`,

with `S_Λ` the Sonin projection and `G_Λ = 1 - P_Λ - P̂_Λ - S_Λ` trace class.  Sonin-trace
domination `Re Tr(ϑ(g) S_Λ ϑ(g)†) ≤ -Re W(g★ ⋆ g)` is therefore the inequality
`Re Tr(ϑ(g) G_Λ ϑ(g)†) ≥ -2 log Λ · ‖g‖²`, which the bound `|Tr(ϑ(g) G_Λ ϑ(g)†)| ≤ ‖G_Λ‖₁ (∫|g|)²`
settles for all tests supported in `|log u| < log Λ / (‖G_Λ‖₁ + 1)`.
-/

noncomputable section

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace ComplexConjugate SchwartzMap

namespace RHTower

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- `ϑ(g)` for a Schwartz logarithmic kernel, and its adjoint. -/
local notation "ϑ[" g "]" => ccmIntegratedScaling (ccmSchwartzLogKernel g)
local notation "ϑ†[" g "]" =>
  ContinuousLinearMap.adjoint (ccmIntegratedScaling (ccmSchwartzLogKernel g))

/-! ## Logarithmic coordinates: scaling is convolution -/

/-- The scaling orbit `ϑ(e^u)` is translation by `u` in logarithmic coordinates. -/
theorem logEvenUnitary_ccmLogDilationOrbit (f : evenSubspace) (u : ℝ) :
    logEvenUnitary (ccmLogDilationOrbit f u) =
      MellinL2.additiveTranslationUnitary (-u) (logEvenUnitary f) := by
  rw [ccmLogDilationOrbit, logEvenUnitary_evenDilation, Real.log_exp]

theorem additiveTranslationUnitary_ae (a : ℝ) (φ : SoninL2) :
    (MellinL2.additiveTranslationUnitary a φ : ℝ → ℂ) =ᵐ[volume] fun t => φ (t + a) :=
  Lp.coeFn_compMeasurePreserving φ (MellinL2.realTranslation_measurePreserving a)

/-- **`ϑ(g)` is the convolution `C_g`.**  For an `L¹` kernel `g`,
`log ∘ ϑ(g) = C_g ∘ log` with `(C_g φ)(t) = ∫ g(t - s) φ(s) ds`. -/
theorem logEvenUnitary_ccmIntegratedScaling (g : CCMLogKernel) (f : evenSubspace) :
    logEvenUnitary (ccmIntegratedScaling g f) =
      (convolutionKernel (g : ℝ → ℂ) (Lp.stronglyMeasurable g).measurable
        (L1.integrable_coeFn g)).op (logEvenUnitary f) := by
  set φ := logEvenUnitary f
  have hint := integrable_ccmLogKernel_smul_orbit g f
  have hpush : logEvenUnitary (ccmIntegratedScaling g f) =
      ∫ u, g u • MellinL2.additiveTranslationUnitary (-u) φ := by
    rw [ccmIntegratedScaling_apply]
    change logEvenUnitary.toLinearIsometry.toContinuousLinearMap
      (∫ u, g u • ccmLogDilationOrbit f u) = _
    rw [← (logEvenUnitary.toLinearIsometry.toContinuousLinearMap).integral_comp_comm hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    change logEvenUnitary (g u • ccmLogDilationOrbit f u) = _
    rw [map_smul, logEvenUnitary_ccmLogDilationOrbit]
  have hint' : Integrable (fun u => g u • MellinL2.additiveTranslationUnitary (-u) φ) := by
    refine ((logEvenUnitary.toLinearIsometry.toContinuousLinearMap).integrable_comp hint).congr
      (Filter.Eventually.of_forall fun u => ?_)
    change logEvenUnitary (g u • ccmLogDilationOrbit f u) = _
    rw [map_smul, logEvenUnitary_ccmLogDilationOrbit]
  rw [hpush]
  set k := convolutionKernel (g : ℝ → ℂ) (Lp.stronglyMeasurable g).measurable
    (L1.integrable_coeFn g)
  apply ext_inner_left ℂ
  intro ψ
  rw [← integral_inner hint', k.inner_op]
  -- both sides are the absolutely convergent integral of `conj ψ(t) g(u) φ(t - u)`
  have htriple := k.integrable_triple φ ψ
  have hshear : Integrable (fun p : ℝ × ℝ =>
      conj ((ψ : ℝ → ℂ) p.1) * (g : ℝ → ℂ) p.2 * (φ : ℝ → ℂ) (p.1 - p.2))
      (volume.prod volume) := by
    -- the shear `(t, u) ↦ (t, t - u)` preserves Lebesgue measure on the plane
    have he : MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.1 - p.2)) (volume.prod volume)
        (volume.prod volume) := by
      have h := (measurePreserving_prod_add (volume : Measure ℝ) (volume : Measure ℝ)).comp
        ((MeasurePreserving.id (volume : Measure ℝ)).prod
          (Measure.measurePreserving_neg (volume : Measure ℝ)))
      convert h using 1
      funext p
      simp [sub_eq_add_neg]
    refine ((he.integrable_comp htriple.aestronglyMeasurable).mpr htriple).congr
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, convolutionKernel_toFun, k, sub_sub_cancel]
  have hright : (∫ y, ∫ z, conj ((ψ : ℝ → ℂ) y) * k.toFun y z * (φ : ℝ → ℂ) z) =
      ∫ y, ∫ u, conj ((ψ : ℝ → ℂ) y) * (g : ℝ → ℂ) u * (φ : ℝ → ℂ) (y - u) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [← integral_sub_left_eq_self
      (fun z => conj ((ψ : ℝ → ℂ) y) * k.toFun y z * (φ : ℝ → ℂ) z) volume y]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [convolutionKernel_toFun, k, sub_sub_cancel]
  rw [hright, integral_integral_swap hshear]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  rw [inner_smul_right, L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [additiveTranslationUnitary_ae (-u) φ] with y hy
  rw [hy, RCLike.inner_apply, ← sub_eq_add_neg]
  ring

/-- The convolution operator of a Schwartz profile. -/
def ccmLogConvolution (g : 𝓢(ℝ, ℂ)) : SoninL2 →L[ℂ] SoninL2 :=
  (convolutionKernel g g.continuous.measurable g.integrable).op

/-- `log ∘ ϑ(g) = C_g ∘ log` for a Schwartz logarithmic kernel. -/
theorem logEvenUnitary_ccmIntegratedScaling_schwartz (g : 𝓢(ℝ, ℂ)) (f : evenSubspace) :
    logEvenUnitary (ϑ[g] f) =
      ccmLogConvolution g (logEvenUnitary f) := by
  rw [logEvenUnitary_ccmIntegratedScaling, ccmLogConvolution]
  congr 1
  refine SchurKernel.op_eq_of_ae (Filter.Eventually.of_forall fun y => ?_)
  have h := ccmSchwartzLogKernel_ae g
  have h' : ∀ᵐ z ∂volume, (ccmSchwartzLogKernel g : ℝ → ℂ) (y - z) = g (y - z) :=
    (Measure.measurePreserving_sub_left (volume : Measure ℝ) y).quasiMeasurePreserving.ae
      (h.mono fun x hx => hx)
  filter_upwards [h'] with z hz
  simpa only [convolutionKernel_toFun] using hz

local notation "Uc" => logEvenUnitary.toLinearIsometry.toContinuousLinearMap
local notation "Ui" => logEvenUnitary.symm.toLinearIsometry.toContinuousLinearMap

theorem ccmIntegratedScaling_schwartz_eq_logConjugate (g : 𝓢(ℝ, ℂ)) :
    ϑ[g] = Ui ∘L ccmLogConvolution g ∘L Uc := by
  refine ContinuousLinearMap.ext fun f => logEvenUnitary.injective ?_
  change logEvenUnitary _ = logEvenUnitary (logEvenUnitary.symm _)
  rw [LinearIsometryEquiv.apply_symm_apply, logEvenUnitary_ccmIntegratedScaling_schwartz]
  rfl

theorem adjoint_ccmIntegratedScaling_schwartz_eq_logConjugate (g : 𝓢(ℝ, ℂ)) :
    ϑ†[g] =
      Ui ∘L ContinuousLinearMap.adjoint (ccmLogConvolution g) ∘L Uc := by
  have h1 : ContinuousLinearMap.adjoint Uc = Ui :=
    LinearIsometryEquiv.adjoint_eq_symm logEvenUnitary
  have h2 : ContinuousLinearMap.adjoint Ui = Uc :=
    LinearIsometryEquiv.adjoint_eq_symm logEvenUnitary.symm
  rw [ccmIntegratedScaling_schwartz_eq_logConjugate, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, h1, h2, ContinuousLinearMap.comp_assoc]

/-! ## The physical shell trace -/

theorem lintegral_enorm_schwartz_lt_top (g : 𝓢(ℝ, ℂ)) : ∫⁻ x, ‖g x‖ₑ < ⊤ :=
  g.integrable.2

/-- Kernel `g(t - s) 1_{(0, L]}(s)` of `C_g ∘ 1_{(0, L]}`. -/
def ccmShellConvolutionKernel (g : 𝓢(ℝ, ℂ)) (L : ℝ) : SchurKernel (volume : Measure ℝ) where
  toFun y z := g (y - z) * (Ioc 0 L).indicator 1 z
  measurable := (g.continuous.measurable.comp (measurable_fst.sub measurable_snd)).mul
    ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd)
  bound := (∫⁻ x, ‖g x‖ₑ).toNNReal
  row y := by
    rw [ENNReal.coe_toNNReal (lintegral_enorm_schwartz_lt_top g).ne,
      ← lintegral_sub_left_eq_self (fun x => ‖g x‖ₑ) y]
    refine lintegral_mono fun z => ?_
    rw [enorm_mul]
    refine mul_le_of_le_one_right' ?_
    by_cases hz : z ∈ Ioc 0 L <;> simp [hz]
  col z := by
    rw [ENNReal.coe_toNNReal (lintegral_enorm_schwartz_lt_top g).ne,
      ← lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) z]
    refine lintegral_mono fun y => ?_
    rw [enorm_mul]
    refine mul_le_of_le_one_right' ?_
    by_cases hz : z ∈ Ioc 0 L <;> simp [hz]

theorem ccmShellConvolutionKernel_toFun (g : 𝓢(ℝ, ℂ)) (L y z : ℝ) :
    (ccmShellConvolutionKernel g L).toFun y z = g (y - z) * (Ioc 0 L).indicator 1 z := rfl

/-- The shell kernel operator is `C_g ∘ 1_{(0, L]}`. -/
theorem ccmShellConvolutionKernel_op (g : 𝓢(ℝ, ℂ)) (L : ℝ) :
    (ccmShellConvolutionKernel g L).op = ccmLogConvolution g ∘L logIntervalCutoff 0 L := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [(ccmShellConvolutionKernel g L).op_coeFn f,
    (convolutionKernel g g.continuous.measurable g.integrable).op_coeFn (logIntervalCutoff 0 L f)]
    with y h1 h2
  change _ = (ccmLogConvolution g (logIntervalCutoff 0 L f) : ℝ → ℂ) y
  rw [h1, ccmLogConvolution, h2, SchurKernel.apply, SchurKernel.apply]
  refine integral_congr_ae ?_
  filter_upwards [indicatorCutoff_ae (Ioc 0 L) measurableSet_Ioc f] with z hz
  change _ = _ * (logIntervalCutoff 0 L f : ℝ → ℂ) z
  rw [show (logIntervalCutoff 0 L f : ℝ → ℂ) z = (Ioc 0 L).indicator (fun x => f x) z from hz,
    ccmShellConvolutionKernel_toFun, convolutionKernel_toFun]
  by_cases hzI : z ∈ Ioc 0 L <;> simp [hzI]

theorem lintegral_ccmShellConvolutionKernel_sq (g : 𝓢(ℝ, ℂ)) (L : ℝ) :
    ∫⁻ y, ∫⁻ z, ‖(ccmShellConvolutionKernel g L).toFun y z‖ₑ ^ 2 =
      volume (Ioc 0 L) * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have hm : Measurable (Function.uncurry fun y z =>
      ‖(ccmShellConvolutionKernel g L).toFun y z‖ₑ ^ 2) :=
    (ccmShellConvolutionKernel g L).measurable_enorm.pow_const 2
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hz : ∀ z, ∫⁻ y, ‖(ccmShellConvolutionKernel g L).toFun y z‖ₑ ^ 2 =
      (Ioc 0 L).indicator (fun _ => ∫⁻ x, ‖g x‖ₑ ^ 2) z := by
    intro z
    by_cases hzI : z ∈ Ioc 0 L
    · simp only [ccmShellConvolutionKernel_toFun, indicator_of_mem hzI, Pi.one_apply, mul_one]
      exact lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ ^ 2) z
    · simp [ccmShellConvolutionKernel_toFun, hzI]
  simp_rw [hz]
  rw [lintegral_indicator measurableSet_Ioc, setLIntegral_const, mul_comm]

theorem lintegral_enorm_sq_schwartz_lt_top (g : 𝓢(ℝ, ℂ)) : ∫⁻ x, ‖g x‖ₑ ^ 2 < ⊤ := by
  rw [← SchurKernel.eLpNorm_two_sq (μ := volume)]
  exact ENNReal.pow_lt_top (g.memLp 2 volume).eLpNorm_lt_top

theorem lintegral_ccmShellConvolutionKernel_sq_lt_top (g : 𝓢(ℝ, ℂ)) (L : ℝ) :
    ∫⁻ y, ∫⁻ z, ‖(ccmShellConvolutionKernel g L).toFun y z‖ₑ ^ 2 < ⊤ := by
  rw [lintegral_ccmShellConvolutionKernel_sq, Real.volume_Ioc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_enorm_sq_schwartz_lt_top g)

/-- `C_g 1_I C_g† = K K†` with `K = C_g 1_I`. -/
theorem ccmLogConvolution_shell_adjoint (g : 𝓢(ℝ, ℂ)) (L : ℝ) :
    ccmLogConvolution g ∘L logIntervalCutoff 0 L ∘L
        ContinuousLinearMap.adjoint (ccmLogConvolution g) =
      (ccmShellConvolutionKernel g L).op ∘L (ccmShellConvolutionKernel g L).adjoint.op := by
  have hI : ContinuousLinearMap.adjoint (logIntervalCutoff 0 L) = logIntervalCutoff 0 L :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (indicatorCutoff_symmetric (Ioc 0 L) measurableSet_Ioc)).adjoint_eq
  have hII : logIntervalCutoff 0 L ∘L logIntervalCutoff 0 L = logIntervalCutoff 0 L :=
    (indicatorCutoff_idempotent (Ioc 0 L) measurableSet_Ioc).eq
  rw [← SchurKernel.adjoint_op, ccmShellConvolutionKernel_op, ContinuousLinearMap.adjoint_comp,
    hI, ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc (logIntervalCutoff 0 L),
    hII]

/-- **Trace of the logarithmic shell.**  `Tr(C_g 1_{(0, L]} C_g†) = L ∫ |g|²`. -/
theorem opTrace_ccmLogConvolution_shell (g : 𝓢(ℝ, ℂ)) {L : ℝ} (hL : 0 ≤ L) :
    ContinuousLinearMap.opTrace (ccmLogConvolution g ∘L logIntervalCutoff 0 L ∘L
        ContinuousLinearMap.adjoint (ccmLogConvolution g)) =
      ((L * ∫ x, ‖g x‖ ^ 2 : ℝ) : ℂ) := by
  set k := ccmShellConvolutionKernel g L
  have h2 := lintegral_ccmShellConvolutionKernel_sq_lt_top g L
  rw [ccmLogConvolution_shell_adjoint,
    SchurKernel.opTrace_comp_op k k.adjoint h2 ((SchurKernel.lintegral_adjoint_sq k).trans_lt h2)]
  have hinner : ∀ y, ∫ z, k.toFun z y * k.adjoint.toFun y z =
      (((Ioc 0 L).indicator (fun _ => ∫ x, ‖g x‖ ^ 2) y : ℝ) : ℂ) := by
    intro y
    simp only [SchurKernel.adjoint_toFun, Complex.mul_conj, ccmShellConvolutionKernel_toFun, k]
    by_cases hy : y ∈ Ioc 0 L
    · simp only [indicator_of_mem hy, Pi.one_apply, mul_one]
      rw [integral_complex_ofReal]
      congr 1
      rw [← integral_sub_right_eq_self (fun x => ‖g x‖ ^ 2) y]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
        simp [Complex.normSq_eq_norm_sq])
    · simp [hy]
  simp_rw [hinner]
  rw [integral_complex_ofReal, integral_indicator measurableSet_Ioc, setIntegral_const,
    Real.volume_real_Ioc_of_le hL, sub_zero, smul_eq_mul]

/-! ## The physical shell on the even carrier -/

theorem dilation_congr {a b : ℝ} (h : a = b) (ha : 0 < a) (hb : 0 < b) :
    dilation a ha = dilation b hb := by
  subst h
  rfl

/-- In logarithmic coordinates the even shell `P_Λ - P₁` is the interval cutoff `1_{(0, log Λ]}`. -/
theorem evenIndicatorCutoff_shell_eq_logConjugate {Λ : ℝ} (hΛ : 1 < Λ) :
    evenIndicatorCutoff Λ - evenIndicatorCutoff 1 =
      Ui ∘L logIntervalCutoff 0 (Real.log Λ) ∘L Uc := by
  refine ContinuousLinearMap.ext fun f => logEvenUnitary.injective ?_
  have h := logEvenUnitary_evenPhysicalShell 1 Λ one_pos hΛ f
  rw [mul_one, Real.log_one] at h
  rw [h]
  change _ = logEvenUnitary (logEvenUnitary.symm _)
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem ccmIntegratedScaling_physicalShell_eq_logConjugate (g : 𝓢(ℝ, ℂ)) {Λ : ℝ} (hΛ : 1 < Λ) :
    ϑ[g] ∘L
        (evenIndicatorCutoff Λ - evenIndicatorCutoff 1) ∘L
          ϑ†[g] =
      Ui ∘L (ccmLogConvolution g ∘L logIntervalCutoff 0 (Real.log Λ) ∘L
        ContinuousLinearMap.adjoint (ccmLogConvolution g)) ∘L Uc := by
  rw [adjoint_ccmIntegratedScaling_schwartz_eq_logConjugate,
    ccmIntegratedScaling_schwartz_eq_logConjugate, evenIndicatorCutoff_shell_eq_logConjugate hΛ]
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply]

theorem ccmLogConvolution_shell_isTraceClass (g : 𝓢(ℝ, ℂ)) (L : ℝ) :
    (ccmLogConvolution g ∘L logIntervalCutoff 0 L ∘L
      ContinuousLinearMap.adjoint (ccmLogConvolution g)).IsTraceClass := by
  have h2 := lintegral_ccmShellConvolutionKernel_sq_lt_top g L
  rw [ccmLogConvolution_shell_adjoint]
  exact ⟨_, _, (ccmShellConvolutionKernel g L).isHilbertSchmidt_op h2,
    (ccmShellConvolutionKernel g L).adjoint.isHilbertSchmidt_op
      ((SchurKernel.lintegral_adjoint_sq _).trans_lt h2), rfl⟩

theorem ccmIntegratedScaling_physicalShell_isTraceClass (g : 𝓢(ℝ, ℂ)) {Λ : ℝ} (hΛ : 1 < Λ) :
    (ϑ[g] ∘L
        (evenIndicatorCutoff Λ - evenIndicatorCutoff 1) ∘L
          ϑ†[g]).IsTraceClass := by
  rw [ccmIntegratedScaling_physicalShell_eq_logConjugate g hΛ]
  exact ccmIsTraceClass_unitaryConjugate logEvenUnitary _ (ccmLogConvolution_shell_isTraceClass g _)

/-- **Physical shell trace.**  `Tr(ϑ(g)(P_Λ - P₁)ϑ(g)†) = log Λ · ∫ |g|²`. -/
theorem opTrace_ccmIntegratedScaling_physicalShell (g : 𝓢(ℝ, ℂ)) {Λ : ℝ} (hΛ : 1 < Λ) :
    ContinuousLinearMap.opTrace (ϑ[g] ∘L
        (evenIndicatorCutoff Λ - evenIndicatorCutoff 1) ∘L
          ϑ†[g]) =
      ((Real.log Λ * ∫ x, ‖g x‖ ^ 2 : ℝ) : ℂ) := by
  rw [ccmIntegratedScaling_physicalShell_eq_logConjugate g hΛ,
    opTrace_unitaryConjugate_of_isTraceClass logEvenUnitary _
      (ccmLogConvolution_shell_isTraceClass g _),
    opTrace_ccmLogConvolution_shell g (Real.log_nonneg hΛ.le)]

/-! ## The Fourier shell -/

/-- The cosine transform reverses the scaling orbit. -/
theorem evenFourierTransform_ccmLogDilationOrbit (f : evenSubspace) (u : ℝ) :
    evenFourierTransform (ccmLogDilationOrbit f u) =
      ccmLogDilationOrbit (evenFourierTransform f) (-u) := by
  apply Subtype.ext
  change fourierUnitary (dilation (Real.exp (-u)) (Real.exp_pos _) f) =
    dilation (Real.exp (-(-u))) (Real.exp_pos _) (fourierUnitary f)
  rw [fourierUnitary_dilation]
  exact congrArg (fun D : SoninL2 →ₗᵢ[ℂ] SoninL2 => D (fourierUnitary f))
    (dilation_congr (by rw [neg_neg, Real.exp_neg, inv_inv]) _ _)

/-- **`F ϑ(g) = ϑ(ǧ) F`** with `ǧ(u) = g(-u)`. -/
theorem evenFourierTransform_comp_ccmIntegratedScaling (g : 𝓢(ℝ, ℂ)) :
    evenFourierTransform ∘L ϑ[g] =
      ϑ[(SchwartzMap.reflectedSchwartz g)] ∘L
        evenFourierTransform := by
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [ContinuousLinearMap.comp_apply, ccmIntegratedScaling_apply]
  rw [← evenFourierTransform.integral_comp_comm
    (integrable_ccmLogKernel_smul_orbit (ccmSchwartzLogKernel g) f)]
  simp_rw [map_smul, evenFourierTransform_ccmLogDilationOrbit]
  rw [← integral_neg_eq_self (fun v =>
    (ccmSchwartzLogKernel (SchwartzMap.reflectedSchwartz g) : ℝ → ℂ) v •
      ccmLogDilationOrbit (evenFourierTransform f) v) volume]
  have hneg : ∀ᵐ u ∂volume,
      (ccmSchwartzLogKernel (SchwartzMap.reflectedSchwartz g) : ℝ → ℂ) (-u) = g u := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (ccmSchwartzLogKernel_ae (SchwartzMap.reflectedSchwartz g))
    filter_upwards [h] with u hu
    simpa using hu
  refine integral_congr_ae ?_
  filter_upwards [ccmSchwartzLogKernel_ae g, hneg] with u hu hu'
  simp only [hu, hu']

theorem reflectedSchwartz_reflectedSchwartz (g : 𝓢(ℝ, ℂ)) :
    SchwartzMap.reflectedSchwartz (SchwartzMap.reflectedSchwartz g) = g := by
  ext x
  simp

theorem ccmIntegratedScaling_comp_evenFourierTransform (g : 𝓢(ℝ, ℂ)) :
    ϑ[g] ∘L evenFourierTransform =
      evenFourierTransform ∘L
        ϑ[(SchwartzMap.reflectedSchwartz g)] := by
  have h := evenFourierTransform_comp_ccmIntegratedScaling (SchwartzMap.reflectedSchwartz g)
  rw [reflectedSchwartz_reflectedSchwartz] at h
  exact h.symm

theorem evenFourierTransform_comp_adjoint_ccmIntegratedScaling (g : 𝓢(ℝ, ℂ)) :
    evenFourierTransform ∘L
        ϑ†[g] =
      ϑ†[(SchwartzMap.reflectedSchwartz g)] ∘L
        evenFourierTransform := by
  have h := congrArg ContinuousLinearMap.adjoint (ccmIntegratedScaling_comp_evenFourierTransform g)
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_evenFourierTransform] at h
  exact h

theorem evenFourierCutoff_shell_eq (Λ : ℝ) :
    evenFourierCutoff Λ - evenFourierCutoff 1 =
      evenFourierTransform ∘L (evenIndicatorCutoff Λ - evenIndicatorCutoff 1) ∘L
        evenFourierTransform := by
  rw [evenFourierCutoff_eq_reflectedCutoff, evenFourierCutoff_eq_reflectedCutoff, reflectedCutoff,
    reflectedCutoff, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rfl

theorem integral_norm_sq_reflectedSchwartz (g : 𝓢(ℝ, ℂ)) :
    ∫ x, ‖SchwartzMap.reflectedSchwartz g x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 := by
  simpa using integral_neg_eq_self (fun x => ‖g x‖ ^ 2) volume

theorem ccmIntegratedScaling_fourierShell_eq (g : 𝓢(ℝ, ℂ)) (Λ : ℝ) :
    ϑ[g] ∘L
        (evenFourierCutoff Λ - evenFourierCutoff 1) ∘L
          ϑ†[g] =
      evenFourierTransform ∘L
        (ϑ[(SchwartzMap.reflectedSchwartz g)] ∘L
          (evenIndicatorCutoff Λ - evenIndicatorCutoff 1) ∘L
            ϑ†[(SchwartzMap.reflectedSchwartz g)]) ∘L
        evenFourierTransform := by
  rw [evenFourierCutoff_shell_eq]
  simp only [← ContinuousLinearMap.comp_assoc, ccmIntegratedScaling_comp_evenFourierTransform]
  simp only [ContinuousLinearMap.comp_assoc, evenFourierTransform_comp_adjoint_ccmIntegratedScaling]

theorem ccmIntegratedScaling_fourierShell_mem (g : 𝓢(ℝ, ℂ)) {Λ : ℝ} (hΛ : 1 < Λ) :
    ϑ[g] ∘L
        (evenFourierCutoff Λ - evenFourierCutoff 1) ∘L
          ϑ†[g] ∈
      hsTraceIdeal evenSubspace := by
  rw [ccmIntegratedScaling_fourierShell_eq]
  exact hsTraceIdeal_comp_left (hsTraceIdeal_comp_right (isTraceClass_mem_hsTraceIdeal
    (ccmIntegratedScaling_physicalShell_isTraceClass _ hΛ)) _) _

/-- **Fourier shell trace.**  `Tr(ϑ(g)(P̂_Λ - P̂₁)ϑ(g)†) = log Λ · ∫ |g|²`. -/
theorem opTrace_ccmIntegratedScaling_fourierShell (g : 𝓢(ℝ, ℂ)) {Λ : ℝ} (hΛ : 1 < Λ) :
    ContinuousLinearMap.opTrace (ϑ[g] ∘L
        (evenFourierCutoff Λ - evenFourierCutoff 1) ∘L
          ϑ†[g]) =
      ((Real.log Λ * ∫ x, ‖g x‖ ^ 2 : ℝ) : ℂ) := by
  set Y := ϑ[(SchwartzMap.reflectedSchwartz g)] ∘L
    (evenIndicatorCutoff Λ - evenIndicatorCutoff 1) ∘L
      ϑ†[(SchwartzMap.reflectedSchwartz g)]
  have hY : Y ∈ hsTraceIdeal evenSubspace :=
    isTraceClass_mem_hsTraceIdeal (ccmIntegratedScaling_physicalShell_isTraceClass _ hΛ)
  rw [ccmIntegratedScaling_fourierShell_eq]
  change ContinuousLinearMap.opTrace (evenFourierTransform * (Y * evenFourierTransform)) = _
  have hYF : Y * evenFourierTransform ∈ hsTraceIdeal evenSubspace := hsTraceIdeal_comp_right hY _
  rw [opTrace_mul_comm_of_mem hYF, mul_assoc,
    evenFourierTransform_mul_self, mul_one, opTrace_ccmIntegratedScaling_physicalShell _ hΛ,
    integral_norm_sq_reflectedSchwartz]

/-! ## The Weil distribution of an autocorrelation -/

/-- `g★(u) = conj g(-u)` has the starred logarithmic kernel. -/
theorem ccmSchwartzLogKernel_conjugateReflection (g : 𝓢(ℝ, ℂ)) :
    ccmSchwartzLogKernel (SchwartzMap.conjugateReflectionSchwartz g) =
      ccmLogKernelStar (ccmSchwartzLogKernel g) := by
  apply Lp.ext
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (ccmSchwartzLogKernel_ae g)
  filter_upwards [ccmSchwartzLogKernel_ae (SchwartzMap.conjugateReflectionSchwartz g),
    ccmLogKernelStar_ae (ccmSchwartzLogKernel g), hneg] with u h1 h2 h3
  rw [h1, h2, SchwartzMap.conjugateReflectionSchwartz_apply]
  congr 1
  simpa using h3.symm

/-- `ϑ(g)† = ϑ(g★)`. -/
theorem adjoint_ccmIntegratedScaling_schwartz (g : 𝓢(ℝ, ℂ)) :
    ϑ†[g] =
      ϑ[(SchwartzMap.conjugateReflectionSchwartz g)] := by
  rw [adjoint_ccmIntegratedScaling, ccmSchwartzLogKernel_conjugateReflection]

/-- The autocorrelation `u ⋆ u★` has the convolution kernel of `u` and `u★`. -/
theorem ccmSchwartzLogKernel_autocorrelation (u : 𝓢(ℝ, ℂ)) :
    ccmSchwartzLogKernel (SchwartzMap.autocorrelationSchwartz u) =
      ccmLogKernelConvolution (ccmSchwartzLogKernel u)
        (ccmLogKernelStar (ccmSchwartzLogKernel u)) := by
  apply Lp.ext
  filter_upwards [ccmSchwartzLogKernel_ae (SchwartzMap.autocorrelationSchwartz u),
    ccmLogKernelConvolution_ae (ccmSchwartzLogKernel u)
      (ccmLogKernelStar (ccmSchwartzLogKernel u))] with w h1 h2
  rw [h1, h2, SchwartzMap.autocorrelationSchwartz_apply, SchwartzMap.autocorrelation,
    convolution_def]
  have hstar : ∀ᵐ v ∂volume, (ccmLogKernelStar (ccmSchwartzLogKernel u) : ℝ → ℂ) v =
      SchwartzMap.conjugateReflection u v := by
    have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (ccmSchwartzLogKernel_ae u)
    filter_upwards [ccmLogKernelStar_ae (ccmSchwartzLogKernel u), hneg] with v hv hv'
    rw [hv, SchwartzMap.conjugateReflection]
    congr 1
  have hstar' :=
    (Measure.measurePreserving_sub_left (volume : Measure ℝ) w).quasiMeasurePreserving.ae hstar
  refine integral_congr_ae ?_
  filter_upwards [ccmSchwartzLogKernel_ae u, hstar'] with y hy hy'
  rw [ContinuousLinearMap.mul_apply', hy, hy']

/-- The positive test `g★ ⋆ g` attached to a compact logarithmic test `g`. -/
def ccmSoninGramTest (g : CCMCompactSchwartzLogTest) : CCMCompactSchwartzLogTest where
  toSchwartzMap := SchwartzMap.autocorrelationSchwartz
    (SchwartzMap.conjugateReflectionSchwartz g.toSchwartzMap)
  radius := 2 * g.radius + 2
  one_lt_radius := by linarith [g.one_lt_radius]
  eq_zero_of_radius_le_abs := by
    intro x hx
    rw [SchwartzMap.autocorrelationSchwartz_apply, SchwartzMap.autocorrelation, convolution_def]
    apply integral_eq_zero_of_ae
    filter_upwards with y
    simp only [Pi.zero_apply, ContinuousLinearMap.mul_apply',
      SchwartzMap.conjugateReflectionSchwartz_apply, SchwartzMap.conjugateReflection,
      Complex.conj_conj, neg_sub]
    by_cases hy : g.radius ≤ |-y|
    · rw [g.eq_zero_of_radius_le_abs _ hy, map_zero, zero_mul]
    · have hxy : g.radius ≤ |x - y| := by
        rw [abs_neg] at hy
        have := abs_sub_abs_le_abs_sub x y
        linarith [g.one_lt_radius]
      rw [g.eq_zero_of_radius_le_abs _ hxy, mul_zero]

theorem ccmIntegratedScaling_ccmSoninGramTest (g : CCMCompactSchwartzLogTest) :
    ϑ[(ccmSoninGramTest g).toSchwartzMap] =
      ϑ†[g.toSchwartzMap] ∘L
        ϑ[g.toSchwartzMap] := by
  change ccmIntegratedScaling (ccmSchwartzLogKernel (SchwartzMap.autocorrelationSchwartz
    (SchwartzMap.conjugateReflectionSchwartz g.toSchwartzMap))) = _
  rw [ccmSchwartzLogKernel_autocorrelation, ccmIntegratedScaling_convolution_star,
    ← adjoint_ccmIntegratedScaling_schwartz, ContinuousLinearMap.adjoint_adjoint]

/-- **`-W(g★ ⋆ g) = Tr(ϑ(g)(1 - P₁ - P̂₁)ϑ(g)†)`**, by cyclicity of the trace formula
`W(H) = Tr(ϑ(H)(P₁ + P̂₁ - 1))`. -/
theorem neg_ccmArchimedeanWeilDistribution_ccmSoninGramTest (g : CCMCompactSchwartzLogTest) :
    -ccmArchimedeanWeilDistribution (ccmSoninGramTest g) =
      ContinuousLinearMap.opTrace (ϑ[g.toSchwartzMap] ∘L
        (1 - evenIndicatorCutoff 1 - evenFourierCutoff 1) ∘L
          ϑ†[g.toSchwartzMap]) := by
  set T := ϑ[g.toSchwartzMap]
  have hD := ccmIntegratedScaling_mul_scatteringLogDifferential_mem g.toSchwartzMap
  rw [← opTrace_ccmIntegratedScaling_mul_geometricScatteringLogDifferential_eq_weilDistribution,
    ccmIntegratedScaling_ccmSoninGramTest]
  have hcyc := opTrace_mul_comm_of_mem hD (ContinuousLinearMap.adjoint T)
  change ContinuousLinearMap.opTrace (ContinuousLinearMap.adjoint T *
    (T * ccmArchimedeanGeometricScatteringLogDifferential)) = _ at hcyc
  have hassoc :
      (ContinuousLinearMap.adjoint T ∘L T) ∘L ccmArchimedeanGeometricScatteringLogDifferential =
        ContinuousLinearMap.adjoint T * (T * ccmArchimedeanGeometricScatteringLogDifferential) :=
    rfl
  rw [hassoc, hcyc, ← opTrace_neg']
  congr 1
  rw [ccmArchimedeanGeometricScatteringLogDifferential_eq_cutoffs]
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [ContinuousLinearMap.mul_def, _root_.neg_apply,
    ContinuousLinearMap.comp_apply, _root_.sub_apply, _root_.add_apply,
    one_apply_eq_self, map_sub, map_add]
  abel

/-! ## The Sonin trace formula at cutoff `Λ` -/

/-- Generic part `G_Λ = 1 - P_Λ - P̂_Λ - S_Λ` of the cutoff pair at `Λ`. -/
def ccmSoninGenericPartAt (Λ : ℝ) : evenSubspace →L[ℂ] evenSubspace :=
  1 - evenIndicatorCutoff Λ - evenFourierCutoff Λ - evenCentralSoninProjection Λ

/-- `G_Λ` is trace class: it restricts the ambient Sonin correction to the even carrier. -/
theorem memSchattenClass_one_ccmSoninGenericPartAt {Λ : ℝ} (hΛ : 0 < Λ) :
    MemSchattenClass 1 (ccmSoninGenericPartAt Λ) := by
  let T : SoninL2 →L[ℂ] SoninL2 := (-1 : ℂ) • centralSoninProjectionCorrection Λ
  have hT : MemSchattenClass 1 T :=
    memSchattenClass_one_smul (centralSoninProjectionCorrection_memSchattenClass_one Λ hΛ) _
  have hmap : Set.MapsTo T evenSubspace evenSubspace := by
    intro f hf
    change (-1 : ℂ) • (centralSoninProjection Λ f -
      (f - indicatorCutoff (centralInterval Λ) (measurableSet_centralInterval Λ) f -
        fourierCutoff (centralInterval Λ) (measurableSet_centralInterval Λ) f)) ∈ evenSubspace
    exact evenSubspace.smul_mem _ (evenSubspace.sub_mem
      (centralSoninProjection_mapsTo_evenSubspace Λ hf)
      (evenSubspace.sub_mem
        (evenSubspace.sub_mem hf (indicatorCutoff_central_mapsTo_evenSubspace Λ hf))
        (fourierCutoff_central_mapsTo_evenSubspace Λ hf)))
  have heq : T.restrict hmap = ccmSoninGenericPartAt Λ := by
    refine ContinuousLinearMap.ext fun f => Subtype.ext ?_
    change (-1 : ℂ) • (centralSoninProjection Λ f -
      (f - indicatorCutoff (centralInterval Λ) (measurableSet_centralInterval Λ) f -
        fourierCutoff (centralInterval Λ) (measurableSet_centralInterval Λ) f)) =
      ((f : SoninL2) - indicatorCutoff (centralInterval Λ) (measurableSet_centralInterval Λ) f -
        fourierCutoff (centralInterval Λ) (measurableSet_centralInterval Λ) f -
          centralSoninProjection Λ f)
    simp only [neg_one_smul]
    abel
  have hr := memSchattenClass_one_restrict evenSubspace T hmap hT
  rwa [heq] at hr

theorem one_sub_cutoffs_eq_cutoffAt (Λ : ℝ) :
    1 - evenIndicatorCutoff 1 - evenFourierCutoff 1 =
      evenCentralSoninProjection Λ + ccmSoninGenericPartAt Λ +
        (evenIndicatorCutoff Λ - evenIndicatorCutoff 1) +
          (evenFourierCutoff Λ - evenFourierCutoff 1) := by
  rw [ccmSoninGenericPartAt]
  abel

/-- **The Sonin trace formula at every cutoff `Λ > 1`.**  For every compact logarithmic test `g`,

`-W(g★ ⋆ g) = 2 log Λ · ‖g‖² + Tr(ϑ(g) S_Λ ϑ(g)†) + Tr(ϑ(g) G_Λ ϑ(g)†)`,

the shell terms `P_Λ - P₁` and `P̂_Λ - P̂₁` each contributing `log Λ · ‖g‖²`. -/
theorem neg_ccmArchimedeanWeilDistribution_eq_cutoffAt (g : CCMCompactSchwartzLogTest) {Λ : ℝ}
    (hΛ : 1 < Λ) :
    -ccmArchimedeanWeilDistribution (ccmSoninGramTest g) =
      ((2 * Real.log Λ * ∫ x, ‖g x‖ ^ 2 : ℝ) : ℂ) +
        ContinuousLinearMap.opTrace (ϑ[g.toSchwartzMap] ∘L
          evenCentralSoninProjection Λ ∘L
            ϑ†[g.toSchwartzMap]) +
        ContinuousLinearMap.opTrace (ϑ[g.toSchwartzMap] ∘L
          ccmSoninGenericPartAt Λ ∘L
            ϑ†[g.toSchwartzMap]) := by
  set T := ϑ[g.toSchwartzMap]
  set Ta := ContinuousLinearMap.adjoint T
  have hS : T ∘L evenCentralSoninProjection Λ ∘L Ta ∈ hsTraceIdeal evenSubspace := by
    rw [← ContinuousLinearMap.comp_assoc]
    exact hsTraceIdeal_comp_right (isTraceClass_mem_hsTraceIdeal
      (ccmIntegratedScaling_mul_soninProjection_isTraceClass g.toSchwartzMap hΛ.le)) _
  have hP :
      T ∘L (evenIndicatorCutoff Λ - evenIndicatorCutoff 1) ∘L Ta ∈ hsTraceIdeal evenSubspace :=
    isTraceClass_mem_hsTraceIdeal (ccmIntegratedScaling_physicalShell_isTraceClass _ hΛ)
  have hF : T ∘L (evenFourierCutoff Λ - evenFourierCutoff 1) ∘L Ta ∈ hsTraceIdeal evenSubspace :=
    ccmIntegratedScaling_fourierShell_mem _ hΛ
  have hW : T ∘L (1 - evenIndicatorCutoff 1 - evenFourierCutoff 1) ∘L Ta ∈
      hsTraceIdeal evenSubspace := by
    have hD := ccmIntegratedScaling_mul_scatteringLogDifferential_mem g.toSchwartzMap
    have h := neg_mem (hsTraceIdeal_comp_right hD Ta)
    convert h using 1
    rw [ccmArchimedeanGeometricScatteringLogDifferential_eq_cutoffs]
    refine ContinuousLinearMap.ext fun f => ?_
    simp only [ContinuousLinearMap.mul_def, _root_.neg_apply,
      ContinuousLinearMap.comp_apply, _root_.sub_apply, _root_.add_apply,
      one_apply_eq_self, map_sub, map_add]
    abel
  have hsplit : T ∘L (1 - evenIndicatorCutoff 1 - evenFourierCutoff 1) ∘L Ta =
      T ∘L evenCentralSoninProjection Λ ∘L Ta + T ∘L ccmSoninGenericPartAt Λ ∘L Ta +
        T ∘L (evenIndicatorCutoff Λ - evenIndicatorCutoff 1) ∘L Ta +
          T ∘L (evenFourierCutoff Λ - evenFourierCutoff 1) ∘L Ta := by
    rw [one_sub_cutoffs_eq_cutoffAt Λ]
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  have hG : T ∘L ccmSoninGenericPartAt Λ ∘L Ta ∈ hsTraceIdeal evenSubspace := by
    have h := sub_mem (sub_mem (sub_mem hW hS) hP) hF
    convert h using 1
    rw [hsplit]
    abel
  rw [neg_ccmArchimedeanWeilDistribution_ccmSoninGramTest, hsplit,
    opTrace_add_of_mem (add_mem (add_mem hS hG) hP) hF,
    opTrace_add_of_mem (add_mem hS hG) hP, opTrace_add_of_mem hS hG,
    opTrace_ccmIntegratedScaling_physicalShell _ hΛ, opTrace_ccmIntegratedScaling_fourierShell _ hΛ]
  push_cast
  ring

/-- **Sonin-trace domination at cutoff `Λ`.**  `Re Tr(ϑ(g) S_Λ ϑ(g)†) ≤ -Re W(g★ ⋆ g)` exactly
when the generic trace stays within the shell budget:
`0 ≤ 2 log Λ ‖g‖² + Re Tr(ϑ(g) G_Λ ϑ(g)†)`. -/
theorem ccmSoninTraceDomination_cutoffAt_iff (g : CCMCompactSchwartzLogTest) {Λ : ℝ}
    (hΛ : 1 < Λ) :
    (ContinuousLinearMap.opTrace (ϑ[g.toSchwartzMap] ∘L
        evenCentralSoninProjection Λ ∘L
          ϑ†[g.toSchwartzMap])).re ≤
        (-ccmArchimedeanWeilDistribution (ccmSoninGramTest g)).re ↔
      0 ≤ (2 * Real.log Λ * ∫ x, ‖g x‖ ^ 2) +
        (ContinuousLinearMap.opTrace (ϑ[g.toSchwartzMap] ∘L
          ccmSoninGenericPartAt Λ ∘L
            ϑ†[g.toSchwartzMap])).re := by
  rw [neg_ccmArchimedeanWeilDistribution_eq_cutoffAt g hΛ, Complex.add_re, Complex.add_re,
    Complex.ofReal_re]
  constructor <;> intro h <;> linarith

/-! ## Domination for small supports -/

theorem norm_ccmSchwartzLogKernel (g : 𝓢(ℝ, ℂ)) :
    ‖ccmSchwartzLogKernel g‖ = ∫ x, ‖g x‖ := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae ((ccmSchwartzLogKernel_ae g).mono fun x hx => by simp only [hx])

/-- `|Tr(ϑ(g) G_Λ ϑ(g)†)| ≤ ‖G_Λ‖₁ (∫ |g|)²`. -/
theorem norm_opTrace_ccmSoninGenericPartAt_le (g : 𝓢(ℝ, ℂ)) {Λ : ℝ} (hΛ : 0 < Λ) :
    ‖ContinuousLinearMap.opTrace (ϑ[g] ∘L
        ccmSoninGenericPartAt Λ ∘L
          ϑ†[g])‖ ≤
      traceNorm evenSubspace (ccmSoninGenericPartAt Λ) * (∫ x, ‖g x‖) ^ 2 := by
  set T := ϑ[g]
  have hG := memSchattenClass_one_ccmSoninGenericPartAt hΛ
  rw [(memSchattenClass_one_comp_right hG (ContinuousLinearMap.adjoint T)).one_opTrace_comp_comm T,
    ContinuousLinearMap.comp_assoc]
  refine (norm_opTrace_comp_le_norm_mul_traceNorm hG _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (traceNorm_nonneg _)
  calc ‖ContinuousLinearMap.adjoint T ∘L T‖ ≤ ‖ContinuousLinearMap.adjoint T‖ * ‖T‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖T‖ ^ 2 := by rw [LinearIsometryEquiv.norm_map, sq]
    _ ≤ (∫ x, ‖g x‖) ^ 2 := by
        rw [← norm_ccmSchwartzLogKernel]
        gcongr
        exact norm_ccmIntegratedScaling_le _

/-- A trace-norm criterion: domination at cutoff `Λ` holds as soon as
`‖G_Λ‖₁ (∫ |g|)² ≤ 2 log Λ ∫ |g|²`. -/
theorem ccmSoninTraceDomination_cutoffAt_of_traceNorm (g : CCMCompactSchwartzLogTest) {Λ : ℝ}
    (hΛ : 1 < Λ)
    (h : traceNorm evenSubspace (ccmSoninGenericPartAt Λ) * (∫ x, ‖g x‖) ^ 2 ≤
      2 * Real.log Λ * ∫ x, ‖g x‖ ^ 2) :
    (ContinuousLinearMap.opTrace (ϑ[g.toSchwartzMap] ∘L
        evenCentralSoninProjection Λ ∘L
          ϑ†[g.toSchwartzMap])).re ≤
      (-ccmArchimedeanWeilDistribution (ccmSoninGramTest g)).re := by
  rw [ccmSoninTraceDomination_cutoffAt_iff g hΛ]
  have hnorm := norm_opTrace_ccmSoninGenericPartAt_le g.toSchwartzMap (zero_lt_one.trans hΛ)
  have hre := (abs_le.mp (Complex.abs_re_le_norm (ContinuousLinearMap.opTrace
    (ϑ[g.toSchwartzMap] ∘L ccmSoninGenericPartAt Λ ∘L
      ϑ†[g.toSchwartzMap])))).1
  linarith

/-- Cauchy--Schwarz on the support: `(∫ |g|)² ≤ 2ε ∫ |g|²` when `g` vanishes off `(-ε, ε)`. -/
theorem sq_integral_norm_le_of_support (g : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ x, ε ≤ |x| → g x = 0) :
    (∫ x, ‖g x‖) ^ 2 ≤ 2 * ε * ∫ x, ‖g x‖ ^ 2 := by
  set I := Ioo (-ε) ε
  set A := ∫ x, ‖g x‖
  set B := ∫ x, ‖g x‖ ^ 2
  have hoff : ∀ x ∉ I, g x = 0 := fun x hx => hg x (by
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact hx)
  have hA : ∫ x in I, ‖g x‖ = A :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hoff x hx]
  have hB : ∫ x in I, ‖g x‖ ^ 2 = B :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hoff x hx]
  have hvol : volume.real I = 2 * ε := by
    rw [Real.volume_real_Ioo_of_le (by linarith)]
    ring
  have hint1 : IntegrableOn (fun x => ‖g x‖) I := g.integrable.norm.integrableOn
  have hint2 : IntegrableOn (fun x => ‖g x‖ ^ 2) I :=
    ((g.memLp 2 volume).integrable_norm_pow (by norm_num)).integrableOn
  set c := A / (2 * ε)
  have hpos : 0 ≤ ∫ x in I, (‖g x‖ - c) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo fun _ _ => sq_nonneg _
  have hexp : ∫ x in I, (‖g x‖ - c) ^ 2 = B - 2 * c * A + c ^ 2 * (2 * ε) := by
    have hsq : (fun x => (‖g x‖ - c) ^ 2) = fun x => ‖g x‖ ^ 2 - 2 * c * ‖g x‖ + c ^ 2 := by
      funext x
      ring
    have i1 : Integrable (fun x => ‖g x‖ ^ 2 - 2 * c * ‖g x‖) (volume.restrict I) :=
      hint2.sub (hint1.const_mul _)
    have i2 : Integrable (fun _ : ℝ => c ^ 2) (volume.restrict I) := integrable_const _
    calc ∫ x in I, (‖g x‖ - c) ^ 2
        = (∫ x in I, ‖g x‖ ^ 2 - 2 * c * ‖g x‖) + ∫ _ in I, c ^ 2 := by
          rw [hsq]
          exact integral_add i1 i2
      _ = (B - 2 * c * A) + c ^ 2 * (2 * ε) := by
          rw [integral_sub hint2 (hint1.const_mul _), integral_const_mul, setIntegral_const, hA, hB,
            hvol, smul_eq_mul, mul_comm (2 * ε)]
      _ = B - 2 * c * A + c ^ 2 * (2 * ε) := by ring
  rw [hexp] at hpos
  have hε2 : 0 < 2 * ε := by linarith
  have key : B - 2 * c * A + c ^ 2 * (2 * ε) = B - A ^ 2 / (2 * ε) := by
    simp only [c]
    field_simp
    ring
  rw [key] at hpos
  have := (div_le_iff₀ hε2).mp (by linarith : A ^ 2 / (2 * ε) ≤ B)
  linarith

/-- **Small-support Sonin-trace domination at every cutoff `Λ > 1`.**  There is `ε > 0` such that
`Re Tr(ϑ(g) S_Λ ϑ(g)†) ≤ -Re W(g★ ⋆ g)` for every compact logarithmic test `g` vanishing for
`|log u| ≥ ε`; no moment condition on `g` is needed. -/
theorem exists_ccmSoninTraceDomination_cutoffAt_small_support {Λ : ℝ} (hΛ : 1 < Λ) :
    ∃ ε > 0, ∀ g : CCMCompactSchwartzLogTest, (∀ x, ε ≤ |x| → g x = 0) →
      (ContinuousLinearMap.opTrace (ϑ[g.toSchwartzMap] ∘L
          evenCentralSoninProjection Λ ∘L
            ϑ†[g.toSchwartzMap])).re ≤
        (-ccmArchimedeanWeilDistribution (ccmSoninGramTest g)).re := by
  set τ := traceNorm evenSubspace (ccmSoninGenericPartAt Λ)
  have hτ : 0 ≤ τ := traceNorm_nonneg _
  have hlog : 0 < Real.log Λ := Real.log_pos hΛ
  refine ⟨Real.log Λ / (τ + 1), div_pos hlog (by linarith), fun g hg => ?_⟩
  apply ccmSoninTraceDomination_cutoffAt_of_traceNorm g hΛ
  have hcs := sq_integral_norm_le_of_support g.toSchwartzMap
    (div_pos hlog (by linarith)) hg
  have hB : 0 ≤ ∫ x, ‖g x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  calc τ * (∫ x, ‖g x‖) ^ 2 ≤ τ * (2 * (Real.log Λ / (τ + 1)) * ∫ x, ‖g x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcs hτ
    _ = (2 * Real.log Λ * ∫ x, ‖g x‖ ^ 2) * (τ / (τ + 1)) := by
        field_simp
    _ ≤ (2 * Real.log Λ * ∫ x, ‖g x‖ ^ 2) * 1 := by
        have hq : τ / (τ + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
        have h0 : 0 ≤ 2 * Real.log Λ * ∫ x, ‖g x‖ ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hq h0
    _ = 2 * Real.log Λ * ∫ x, ‖g x‖ ^ 2 := mul_one _

end RHTower
