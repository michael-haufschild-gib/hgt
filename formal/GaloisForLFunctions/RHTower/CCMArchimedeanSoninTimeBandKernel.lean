import GaloisForLFunctions.RHTower.CCMArchimedeanSoninTimeBandSplit
import GaloisForLFunctions.RHTower.CCMArchimedeanGeometricCommutatorKernel
import GaloisForLFunctions.RHTower.SuzukiPositiveHalfLine
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral

/-!
# The time-band scaling trace is an explicit cosine integral

On the positive half-line model `W : L²(ℝ)^ev ≃ L²(0,∞)`, `f ↦ √2 f|_{(0,∞)}`, the compressed
cosine transform with a scaling twist is a bounded kernel operator:

`W (P F ϑ_u P) W⁻¹ = K_u`,   `K_u(x, z) = 1_{x ≤ 1} 1_{z ≤ 1} · 2 e^{u/2} cos(2π e^u x z)`.

Since `P P̂ ϑ_u = P F P F ϑ_u` has the same trace as `(P F P)(P F ϑ_u P)`, the time-band scaling
trace is

`T(u) = Tr(P P̂ ϑ_u) = ∫₀¹ ∫₀¹ 4 e^{u/2} cos(2π x z) cos(2π e^u x z) dz dx`.
-/

noncomputable section

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

open MeasureTheory Set ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace ComplexConjugate FourierTransform ENNReal

namespace RHTower

local notation "Pc" => evenIndicatorCutoff 1
local notation "Rc" => evenFourierCutoff 1
local notation "μ₊" => (volume.restrict (Ioi (0 : ℝ)))
local notation "W" => suzukiPositiveHalfLineUnitary

/-! ## The finite cosine kernel -/

/-- `K_u(x, z) = 1_{x ≤ 1} 1_{z ≤ 1} · 2 e^{u/2} cos(2π e^u x z)`. -/
def ccmFiniteCosineKernelFun (u x z : ℝ) : ℂ :=
  (Iic (1 : ℝ)).indicator (fun _ => (1 : ℂ)) x * (Iic (1 : ℝ)).indicator (fun _ => (1 : ℂ)) z *
    ((2 * Real.exp (u / 2) * Real.cos (2 * Real.pi * Real.exp u * x * z) : ℝ) : ℂ)

theorem measurable_ccmFiniteCosineKernelFun (u : ℝ) :
    Measurable (Function.uncurry (ccmFiniteCosineKernelFun u)) := by
  unfold ccmFiniteCosineKernelFun
  refine ((Measurable.indicator measurable_const measurableSet_Iic).comp measurable_fst).mul
    ((Measurable.indicator measurable_const measurableSet_Iic).comp measurable_snd) |>.mul ?_
  exact Complex.measurable_ofReal.comp (by fun_prop)

theorem norm_ccmFiniteCosineKernelFun_le_left (u x z : ℝ) :
    ‖ccmFiniteCosineKernelFun u x z‖ ≤
      (Iic (1 : ℝ)).indicator (fun _ => 2 * Real.exp (u / 2)) x := by
  unfold ccmFiniteCosineKernelFun
  by_cases hx : x ∈ Iic (1 : ℝ)
  · rw [indicator_of_mem hx, indicator_of_mem hx, one_mul, norm_mul]
    have h1 : ‖(Iic (1 : ℝ)).indicator (fun _ => (1 : ℂ)) z‖ ≤ 1 := by
      by_cases hz : z ∈ Iic (1 : ℝ) <;> simp [hz]
    have h2 : ‖(((2 * Real.exp (u / 2) * Real.cos (2 * Real.pi * Real.exp u * x * z) : ℝ)) : ℂ)‖ ≤
        2 * Real.exp (u / 2) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
    calc _ ≤ 1 * (2 * Real.exp (u / 2)) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · simp [hx]

theorem norm_ccmFiniteCosineKernelFun_le_right (u x z : ℝ) :
    ‖ccmFiniteCosineKernelFun u x z‖ ≤
      (Iic (1 : ℝ)).indicator (fun _ => 2 * Real.exp (u / 2)) z := by
  have h : ccmFiniteCosineKernelFun u x z = ccmFiniteCosineKernelFun u z x := by
    unfold ccmFiniteCosineKernelFun
    rw [show 2 * Real.pi * Real.exp u * x * z = 2 * Real.pi * Real.exp u * z * x by ring]
    ring
  rw [h]
  exact norm_ccmFiniteCosineKernelFun_le_left u z x

theorem volume_restrict_Ioi_Iic_one : μ₊ (Iic (1 : ℝ)) = 1 := by
  rw [Measure.restrict_apply measurableSet_Iic, Iic_inter_Ioi, Real.volume_Ioc, sub_zero,
    ENNReal.ofReal_one]

theorem lintegral_indicator_bound (u : ℝ) :
    ∫⁻ z, ENNReal.ofReal ((Iic (1 : ℝ)).indicator (fun _ => 2 * Real.exp (u / 2)) z) ∂μ₊ =
      ENNReal.ofReal (2 * Real.exp (u / 2)) := by
  have h : (fun z => ENNReal.ofReal ((Iic (1 : ℝ)).indicator (fun _ => 2 * Real.exp (u / 2)) z)) =
      (Iic (1 : ℝ)).indicator (fun _ => ENNReal.ofReal (2 * Real.exp (u / 2))) := by
    funext z
    by_cases hz : z ∈ Iic (1 : ℝ) <;> simp [hz]
  rw [h, lintegral_indicator_const measurableSet_Iic, volume_restrict_Ioi_Iic_one, mul_one]

/-- The finite cosine kernel as a Schur kernel on `(0, ∞)`. -/
def ccmFiniteCosineKernel (u : ℝ) : SchurKernel μ₊ where
  toFun := ccmFiniteCosineKernelFun u
  measurable := measurable_ccmFiniteCosineKernelFun u
  bound := Real.toNNReal (2 * Real.exp (u / 2))
  row x := by
    rw [ENNReal.ofNNReal_toNNReal]
    calc ∫⁻ z, ‖ccmFiniteCosineKernelFun u x z‖ₑ ∂μ₊
        ≤ ∫⁻ z, ENNReal.ofReal ((Iic (1 : ℝ)).indicator (fun _ => 2 * Real.exp (u / 2)) z) ∂μ₊ :=
          lintegral_mono fun z => by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (norm_ccmFiniteCosineKernelFun_le_right u x z)
      _ = _ := lintegral_indicator_bound u
  col z := by
    rw [ENNReal.ofNNReal_toNNReal]
    calc ∫⁻ x, ‖ccmFiniteCosineKernelFun u x z‖ₑ ∂μ₊
        ≤ ∫⁻ x, ENNReal.ofReal ((Iic (1 : ℝ)).indicator (fun _ => 2 * Real.exp (u / 2)) x) ∂μ₊ :=
          lintegral_mono fun x => by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (norm_ccmFiniteCosineKernelFun_le_left u x z)
      _ = _ := lintegral_indicator_bound u

theorem ccmFiniteCosineKernel_toFun (u x z : ℝ) :
    (ccmFiniteCosineKernel u).toFun x z = ccmFiniteCosineKernelFun u x z := rfl

/-- The finite cosine kernel is square integrable. -/
theorem lintegral_ccmFiniteCosineKernel_sq_lt_top (u : ℝ) :
    ∫⁻ x, ∫⁻ z, ‖(ccmFiniteCosineKernel u).toFun x z‖ₑ ^ 2 ∂μ₊ ∂μ₊ < ∞ := by
  set c := ENNReal.ofReal (2 * Real.exp (u / 2))
  have hpt : ∀ x z, ‖(ccmFiniteCosineKernel u).toFun x z‖ₑ ^ 2 ≤
      ENNReal.ofReal ((Iic (1 : ℝ)).indicator (fun _ => 2 * Real.exp (u / 2)) x) *
        ENNReal.ofReal ((Iic (1 : ℝ)).indicator (fun _ => 2 * Real.exp (u / 2)) z) := by
    intro x z
    rw [sq]
    refine mul_le_mul' ?_ ?_
    · rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_ccmFiniteCosineKernelFun_le_left u x z)
    · rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_ccmFiniteCosineKernelFun_le_right u x z)
  calc ∫⁻ x, ∫⁻ z, ‖(ccmFiniteCosineKernel u).toFun x z‖ₑ ^ 2 ∂μ₊ ∂μ₊
      ≤ ∫⁻ x, ∫⁻ z, ENNReal.ofReal ((Iic (1 : ℝ)).indicator (fun _ => 2 * Real.exp (u / 2)) x) *
          ENNReal.ofReal ((Iic (1 : ℝ)).indicator (fun _ => 2 * Real.exp (u / 2)) z) ∂μ₊ ∂μ₊ :=
        lintegral_mono fun x => lintegral_mono fun z => hpt x z
    _ = c * c := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_bound]
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_bound]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-! ## The kernel of the compressed scaled cosine transform -/

/-- The everywhere-even representative of `W⁻¹ g`. -/
def suzukiEvenRep (g : SuzukiPositiveL2) (x : ℝ) : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
    (suzukiPositiveZeroExtensionFun g x + suzukiPositiveZeroExtensionFun g (-x))

theorem suzukiEvenRep_neg (g : SuzukiPositiveL2) (x : ℝ) :
    suzukiEvenRep g (-x) = suzukiEvenRep g x := by
  simp only [suzukiEvenRep, neg_neg, add_comm]

theorem suzukiEvenRep_of_pos (g : SuzukiPositiveL2) {x : ℝ} (hx : 0 < x) :
    suzukiEvenRep g x = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * g x := by
  have hneg : -x ∉ Ioi (0 : ℝ) := by simp only [mem_Ioi, not_lt]; linarith
  simp only [suzukiEvenRep, suzukiPositiveZeroExtensionFun,
    indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), indicator_of_notMem hneg, add_zero]

/-- The representative `x ↦ e^{-u/2} 1_{|e^{-u} x| ≤ 1} E(e^{-u} x)` of `ϑ_u P W⁻¹ g`. -/
def ccmTimeBandSourceFun (u : ℝ) (g : SuzukiPositiveL2) (x : ℝ) : ℂ :=
  (Real.sqrt (Real.exp (-u)) : ℂ) *
    (Icc (-1 : ℝ) 1).indicator (suzukiEvenRep g) (Real.exp (-u) * x)

theorem coe_evenIndicatorCutoff_symm_ae (g : SuzukiPositiveL2) :
    ((Pc (suzukiPositiveHalfLineUnitary.symm g) : evenSubspace) : SoninL2) =ᵐ[volume]
      (Icc (-1 : ℝ) 1).indicator (suzukiEvenRep g) := by
  rw [coe_evenIndicatorCutoff_apply, suzukiPositiveHalfLineUnitary_symm_apply]
  filter_upwards [indicatorCutoff_ae (centralInterval 1) (measurableSet_centralInterval 1)
    (suzukiEvenExtension g : SoninL2), suzukiEvenExtension_ae g] with x h1 h2
  rw [h1]
  change (Icc (-1 : ℝ) 1).indicator _ x = _
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hx, indicator_of_mem hx, h2]
    rfl
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

theorem coe_ccmLogDilation_evenIndicatorCutoff_symm_ae (u : ℝ) (g : SuzukiPositiveL2) :
    ((ccmLogDilation u (Pc (suzukiPositiveHalfLineUnitary.symm g)) : evenSubspace) : SoninL2) =ᵐ[volume]
      ccmTimeBandSourceFun u g := by
  have h2 := (coe_evenIndicatorCutoff_symm_ae g).comp_tendsto
    (realMul_quasiMeasurePreserving (Real.exp (-u)) (Real.exp_pos (-u)).ne').tendsto_ae
  filter_upwards [ccmLogDilationOrbit_ae (Pc (suzukiPositiveHalfLineUnitary.symm g)) u, h2] with x h1 h2
  rw [ccmLogDilation_apply, h1, ccmTimeBandSourceFun]
  congr 1

theorem integrable_ccmTimeBandSourceFun (u : ℝ) (g : SuzukiPositiveL2) :
    Integrable (ccmTimeBandSourceFun u g) volume := by
  have hG : Integrable ((Icc (-1 : ℝ) 1).indicator (suzukiEvenRep g)) volume := by
    have h := integrable_indicatorCutoff_Icc (-1) 1 (suzukiPositiveHalfLineUnitary.symm g : SoninL2)
    refine h.congr ?_
    have h' := coe_evenIndicatorCutoff_symm_ae g
    rw [coe_evenIndicatorCutoff_apply] at h'
    exact h'
  exact (hG.comp_mul_left' (Real.exp_pos (-u)).ne').const_mul _

theorem ccmTimeBandSourceFun_neg (u : ℝ) (g : SuzukiPositiveL2) (x : ℝ) :
    ccmTimeBandSourceFun u g (-x) = ccmTimeBandSourceFun u g x := by
  unfold ccmTimeBandSourceFun
  congr 1
  rw [mul_neg]
  set y := Real.exp (-u) * x
  by_cases hy : y ∈ Icc (-1 : ℝ) 1
  · have hy' : -y ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    rw [indicator_of_mem hy, indicator_of_mem hy', suzukiEvenRep_neg]
  · have hy' : -y ∉ Icc (-1 : ℝ) 1 := fun h => hy ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [indicator_of_notMem hy, indicator_of_notMem hy']

/-- `ϑ_u P W⁻¹ g` as an even `L¹ ∩ L²` source. -/
def ccmTimeBandSource (u : ℝ) (g : SuzukiPositiveL2) : CCMEvenL1L2Source where
  toFun := ccmTimeBandSourceFun u g
  integrable := integrable_ccmTimeBandSourceFun u g
  memLp_two := (Lp.memLp (ccmLogDilation u (Pc (suzukiPositiveHalfLineUnitary.symm g)) : SoninL2)).ae_eq
    (coe_ccmLogDilation_evenIndicatorCutoff_symm_ae u g)
  even := ccmTimeBandSourceFun_neg u g

theorem ccmLogDilation_evenIndicatorCutoff_symm_eq (u : ℝ) (g : SuzukiPositiveL2) :
    ccmLogDilation u (Pc (suzukiPositiveHalfLineUnitary.symm g)) = (ccmTimeBandSource u g).toEvenSubspace :=
  Subtype.ext (Lp.ext ((coe_ccmLogDilation_evenIndicatorCutoff_symm_ae u g).trans
    (ccmTimeBandSource u g).coeFn_toEvenSubspace.symm))

/-- **Fourier transform of the source.**
`𝓕 H(X) = √2 e^{u/2} ∫₀^∞ 1_{z ≤ 1} cos(2π e^u X z) g(z) dz`. -/
theorem fourier_ccmTimeBandSourceFun (u : ℝ) (g : SuzukiPositiveL2) (X : ℝ) :
    𝓕 (ccmTimeBandSourceFun u g) X =
      ((Real.sqrt 2 * Real.exp (u / 2) : ℝ) : ℂ) * ∫ z in Ioi (0 : ℝ),
        (Iic (1 : ℝ)).indicator (fun _ => (1 : ℂ)) z *
          ((Real.cos (2 * Real.pi * Real.exp u * X * z) : ℝ) : ℂ) * g z := by
  set φ : ℝ → ℂ := fun z => (Iic (1 : ℝ)).indicator (fun _ => (1 : ℂ)) z *
    ((Real.cos (2 * Real.pi * Real.exp u * X * z) : ℝ) : ℂ) * g z
  have hpt : EqOn (fun y => ccmTimeBandSourceFun u g y *
        ((Real.cos (2 * Real.pi * X * y) : ℝ) : ℂ))
      (fun y => ((Real.sqrt (Real.exp (-u)) : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
        φ (Real.exp (-u) * y)) (Ioi (0 : ℝ)) := by
    intro y hy
    have hpos : 0 < Real.exp (-u) * y := mul_pos (Real.exp_pos _) hy
    have hcos : 2 * Real.pi * Real.exp u * X * (Real.exp (-u) * y) = 2 * Real.pi * X * y := by
      rw [show 2 * Real.pi * Real.exp u * X * (Real.exp (-u) * y) =
        2 * Real.pi * X * y * (Real.exp u * Real.exp (-u)) by ring, ← Real.exp_add,
        add_neg_cancel, Real.exp_zero, mul_one]
    simp only [ccmTimeBandSourceFun, φ, hcos]
    by_cases h1 : Real.exp (-u) * y ≤ 1
    · rw [indicator_of_mem (show Real.exp (-u) * y ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, h1⟩),
        indicator_of_mem (show Real.exp (-u) * y ∈ Iic (1 : ℝ) from h1),
        suzukiEvenRep_of_pos g hpos]
      ring
    · rw [indicator_of_notMem (show Real.exp (-u) * y ∉ Icc (-1 : ℝ) 1 from fun h => h1 h.2),
        indicator_of_notMem (show Real.exp (-u) * y ∉ Iic (1 : ℝ) from h1)]
      ring
  have hF := (ccmTimeBandSource u g).fourier_eq_two_mul_integral_Ioi_cos X
  change 𝓕 (ccmTimeBandSourceFun u g) X = 2 * ∫ y in Ioi (0 : ℝ), ccmTimeBandSourceFun u g y *
    ((Real.cos (2 * Real.pi * X * y) : ℝ) : ℂ) at hF
  rw [hF]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_comp_mul_left_Ioi φ 0 (Real.exp_pos (-u)), mul_zero, Complex.real_smul]
  have hscalar : 2 * (Real.sqrt (Real.exp (-u)) * (Real.sqrt 2)⁻¹ * (Real.exp (-u))⁻¹) =
      Real.sqrt 2 * Real.exp (u / 2) := by
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [← Real.exp_half, Real.exp_neg u, inv_inv]
    have he : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : (2 : ℝ) * (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
      rw [mul_comm, inv_mul_eq_div, div_eq_iff hs2pos.ne', hs2]
    calc 2 * (Real.exp (-u / 2) * (Real.sqrt 2)⁻¹ * Real.exp u)
        = (2 * (Real.sqrt 2)⁻¹) * (Real.exp (-u / 2) * Real.exp u) := by ring
      _ = Real.sqrt 2 * Real.exp (u / 2) := by rw [he, h2]
  have hscalarC : (2 : ℂ) * (((Real.sqrt (Real.exp (-u)) : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
      ((Real.exp (-u))⁻¹ : ℂ)) = ((Real.sqrt 2 * Real.exp (u / 2) : ℝ) : ℂ) := by
    rw [← hscalar]
    push_cast
    ring
  rw [show (2 : ℂ) * (((Real.sqrt (Real.exp (-u)) : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
      ((Real.exp (-u))⁻¹ * ∫ z in Ioi (0 : ℝ), φ z)) =
      ((2 : ℂ) * (((Real.sqrt (Real.exp (-u)) : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
        ((Real.exp (-u))⁻¹ : ℂ))) * ∫ z in Ioi (0 : ℝ), φ z by push_cast; ring, hscalarC]

local notation "Wc" => suzukiPositiveHalfLineUnitary.toLinearIsometry.toContinuousLinearMap
local notation "Wi" => suzukiPositiveHalfLineUnitary.symm.toLinearIsometry.toContinuousLinearMap

/-- **`W (P F ϑ_u P) W⁻¹ = K_u`.** -/
theorem suzukiConj_evenFourierScaling (u : ℝ) :
    Wc ∘L (Pc * evenFourierTransform * ccmLogDilation u * Pc) ∘L Wi =
      (ccmFiniteCosineKernel u).op := by
  refine ContinuousLinearMap.ext fun g => ?_
  change suzukiPositiveHalfLineUnitary (Pc (evenFourierTransform (ccmLogDilation u
    (Pc (suzukiPositiveHalfLineUnitary.symm g))))) = _
  rw [ccmLogDilation_evenIndicatorCutoff_symm_eq, suzukiPositiveHalfLineUnitary_apply]
  set σ := ccmTimeBandSource u g
  have hF : ((evenFourierTransform σ.toEvenSubspace : evenSubspace) : SoninL2) =ᵐ[volume]
      𝓕 (ccmTimeBandSourceFun u g) := by
    rw [coe_evenFourierTransform_apply]
    exact coeFn_fourier_toLp σ.integrable σ.memLp_two
  have hP : ((Pc (evenFourierTransform σ.toEvenSubspace) : evenSubspace) : SoninL2) =ᵐ[volume]
      (Icc (-1 : ℝ) 1).indicator (𝓕 (ccmTimeBandSourceFun u g)) := by
    rw [coe_evenIndicatorCutoff_apply]
    filter_upwards [indicatorCutoff_ae (centralInterval 1) (measurableSet_centralInterval 1)
      (evenFourierTransform σ.toEvenSubspace : SoninL2), hF] with x h1 h2
    rw [h1]
    change (Icc (-1 : ℝ) 1).indicator _ x = _
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hx, indicator_of_mem hx, h2]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  apply Lp.ext
  filter_upwards [suzukiPositiveRestriction_ae (Pc (evenFourierTransform σ.toEvenSubspace)),
    ae_restrict_of_ae hP, (ccmFiniteCosineKernel u).op_coeFn g,
    ae_restrict_mem measurableSet_Ioi] with x hW hPx hK hx
  rw [hW, hPx, hK, SchurKernel.apply]
  simp only [ccmFiniteCosineKernel_toFun, ccmFiniteCosineKernelFun]
  by_cases hx1 : x ≤ 1
  · rw [indicator_of_mem (show x ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [mem_Ioi.mp hx], hx1⟩),
      fourier_ccmTimeBandSourceFun, indicator_of_mem (show x ∈ Iic (1 : ℝ) from hx1), one_mul,
      ← mul_assoc, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
      norm_num
    simp only [Complex.ofReal_mul]
    calc ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.exp (u / 2) : ℝ) : ℂ)) *
          ((Iic (1 : ℝ)).indicator (fun _ => (1 : ℂ)) z *
            ((Real.cos (2 * Real.pi * Real.exp u * x * z) : ℝ) : ℂ) * g z)
        = (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)) * ((Real.exp (u / 2) : ℝ) : ℂ) *
          ((Iic (1 : ℝ)).indicator (fun _ => (1 : ℂ)) z *
            ((Real.cos (2 * Real.pi * Real.exp u * x * z) : ℝ) : ℂ) * g z) := by ring
      _ = _ := by rw [hs2]; push_cast; ring
  · have hx1' : x ∉ Icc (-1 : ℝ) 1 := fun h => hx1 h.2
    rw [indicator_of_notMem hx1', indicator_of_notMem (show x ∉ Iic (1 : ℝ) from hx1)]
    simp

/-! ## The time-band scaling trace -/

/-- `T(u) = ∫₀¹ ∫₀¹ 4 e^{u/2} cos(2π x z) cos(2π e^u x z) dz dx`. -/
def ccmTimeBandTrace (u : ℝ) : ℝ :=
  ∫ x in Ioc (0 : ℝ) 1, ∫ z in Ioc (0 : ℝ) 1,
    4 * Real.exp (u / 2) * Real.cos (2 * Real.pi * x * z) * Real.cos (2 * Real.pi * Real.exp u * x * z)

theorem setIntegral_Ioi_indicator_Iic_one (f : ℝ → ℂ) :
    ∫ z in Ioi (0 : ℝ), (Iic (1 : ℝ)).indicator (fun _ => (1 : ℂ)) z * f z =
      ∫ z in Ioc (0 : ℝ) 1, f z := by
  have h : (fun z => (Iic (1 : ℝ)).indicator (fun _ => (1 : ℂ)) z * f z) =
      (Iic (1 : ℝ)).indicator f := by
    funext z
    by_cases hz : z ∈ Iic (1 : ℝ) <;> simp [hz]
  rw [h, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]

theorem isTraceClass_ccmFiniteCosineKernel_comp (u v : ℝ) :
    ((ccmFiniteCosineKernel u).op ∘L (ccmFiniteCosineKernel v).op).IsTraceClass :=
  ⟨_, _, (ccmFiniteCosineKernel u).isHilbertSchmidt_op (lintegral_ccmFiniteCosineKernel_sq_lt_top u),
    (ccmFiniteCosineKernel v).isHilbertSchmidt_op (lintegral_ccmFiniteCosineKernel_sq_lt_top v),
    rfl⟩

theorem evenIndicatorCutoff_mul_evenFourierTransform_mul_eq (u : ℝ) :
    Pc * evenFourierTransform * ccmLogDilation u * Pc = Wi ∘L (ccmFiniteCosineKernel u).op ∘L Wc := by
  rw [← suzukiConj_evenFourierScaling u]
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply]

/-- **The time-band scaling trace.**  `Tr(P P̂ ϑ_u) = T(u)`. -/
theorem ccmScalingTrace_evenIndicatorCutoff_mul_evenFourierCutoff (u : ℝ) :
    ccmScalingTrace (Pc * Rc) u = (ccmTimeBandTrace u : ℂ) := by
  have hPR := memSchattenClass_one_evenIndicatorCutoff_mul_evenFourierCutoff
  set F := evenFourierTransform
  have hR : Rc = F * Pc * F := by rw [evenFourierCutoff_eq_reflectedCutoff, reflectedCutoff]
  have hX : MemSchattenClass 1 (Pc * Rc * ccmLogDilation u) := memSchattenClass_one_comp_right hPR _
  -- `Tr X = Tr(X P)`, the complementary part vanishing by `(1 - P) P = 0`
  have hsplit : opTrace (Pc * Rc * ccmLogDilation u) =
      opTrace (Pc * Rc * ccmLogDilation u * Pc) := by
    have hQ : MemSchattenClass 1 (Pc * Rc * ccmLogDilation u * (1 - Pc)) :=
      memSchattenClass_one_comp_right hX _
    have hP : MemSchattenClass 1 (Pc * Rc * ccmLogDilation u * Pc) :=
      memSchattenClass_one_comp_right hX _
    have hzero : opTrace (Pc * Rc * ccmLogDilation u * (1 - Pc)) = 0 := by
      have h := hX.one_opTrace_comp_comm (1 - Pc)
      change opTrace ((1 - Pc) * (Pc * Rc * ccmLogDilation u)) =
        opTrace (Pc * Rc * ccmLogDilation u * (1 - Pc)) at h
      rw [← h, ← mul_assoc, ← mul_assoc, sub_mul, one_mul, evenIndicatorCutoff_mul_self, sub_self,
        zero_mul, zero_mul]
      exact opTrace_zero
    have hsum : Pc * Rc * ccmLogDilation u =
        Pc * Rc * ccmLogDilation u * Pc + Pc * Rc * ccmLogDilation u * (1 - Pc) := by
      rw [← mul_add, add_sub_cancel, mul_one]
    conv_lhs => rw [hsum]
    rw [opTrace_add_of_memSchattenClass_one hP hQ, hzero, add_zero]
  have hfac : Pc * Rc * ccmLogDilation u * Pc =
      (Pc * F * ccmLogDilation 0 * Pc) * (Pc * F * ccmLogDilation u * Pc) := by
    rw [ccmLogDilation_zero, hR]
    change _ = Pc * F * 1 * Pc * (Pc * F * ccmLogDilation u * Pc)
    rw [mul_one]
    calc Pc * (F * Pc * F) * ccmLogDilation u * Pc
        = Pc * F * (Pc * Pc) * F * ccmLogDilation u * Pc := by
          rw [evenIndicatorCutoff_mul_self]; noncomm_ring
      _ = _ := by noncomm_ring
  rw [ccmScalingTrace]
  change opTrace (Pc * Rc * ccmLogDilation u) = _
  rw [hsplit, hfac, evenIndicatorCutoff_mul_evenFourierTransform_mul_eq,
    evenIndicatorCutoff_mul_evenFourierTransform_mul_eq]
  have hcomp : (Wi ∘L (ccmFiniteCosineKernel 0).op ∘L Wc) * (Wi ∘L (ccmFiniteCosineKernel u).op ∘L Wc) =
      Wi ∘L ((ccmFiniteCosineKernel 0).op ∘L (ccmFiniteCosineKernel u).op) ∘L Wc := by
    refine ContinuousLinearMap.ext fun f => ?_
    simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometryEquiv.apply_symm_apply]
  rw [hcomp, opTrace_unitaryConjugate_of_isTraceClass suzukiPositiveHalfLineUnitary _
    (isTraceClass_ccmFiniteCosineKernel_comp 0 u),
    SchurKernel.opTrace_comp_op _ _ (lintegral_ccmFiniteCosineKernel_sq_lt_top 0)
      (lintegral_ccmFiniteCosineKernel_sq_lt_top u)]
  simp only [ccmFiniteCosineKernel_toFun, ccmFiniteCosineKernelFun, Real.exp_zero, zero_div,
    mul_one]
  sorry

end RHTower
