import GaloisForLFunctions.RHTower.SuzukiDirichletDerivative
import GaloisForLFunctions.RHTower.SuzukiBoundaryLayerFormCore
import GaloisForLFunctions.RHTower.CCMArchimedeanFormDomainEquivalence
import GaloisForLFunctions.RHTower.SuzukiApertureL2Equivalence
import GaloisForLFunctions.RHTower.SuzukiWeilFriedrichsOperator

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

def suzukiApertureFourierPhase (a ξ : ℝ)
    (t : SuzukiApertureInterval a) : ℂ :=
  boundaryFourierPhase ξ (t : ℝ)

theorem integrable_suzukiApertureFourierPhase (a ξ : ℝ) :
    Integrable (suzukiApertureFourierPhase a ξ) := by
  have hmeas : AEStronglyMeasurable (suzukiApertureFourierPhase a ξ)
      (volume : Measure (SuzukiApertureInterval a)) :=
    ((continuous_boundaryFourierPhase ξ).comp continuous_subtype_val).aestronglyMeasurable
  have hmem : MemLp (suzukiApertureFourierPhase a ξ) 1 :=
    MemLp.of_bound hmeas 1 (ae_of_all _ fun t => by
      rw [suzukiApertureFourierPhase, norm_boundaryFourierPhase])
  exact hmem.integrable (by norm_num)

def suzukiH01FourierTriangleKernel (a ξ : ℝ)
    (f : SuzukiApertureIntervalL2 a)
    (p : SuzukiApertureInterval a × SuzukiApertureInterval a) : ℂ :=
  (suzukiApertureUpperKernel a).indicator
    (fun p => f p.1 * suzukiApertureFourierPhase a ξ p.2) p

theorem integrable_suzukiH01FourierTriangleKernel (a ξ : ℝ)
    (f : SuzukiApertureIntervalL2 a) :
    Integrable (suzukiH01FourierTriangleKernel a ξ f)
      ((volume : Measure (SuzukiApertureInterval a)).prod volume) := by
  exact (((Lp.memLp f).integrable (by norm_num)).mul_prod
    (integrable_suzukiApertureFourierPhase a ξ)).indicator
      (measurableSet_suzukiApertureUpperKernel a)

theorem suzukiApertureFourierPhase_mul_prefix_eq_integral_triangle
    (a ξ : ℝ) (f : SuzukiApertureIntervalL2 a)
    (t : SuzukiApertureInterval a) :
    suzukiApertureFourierPhase a ξ t * suzukiAperturePrefix a f t =
      ∫ u, suzukiH01FourierTriangleKernel a ξ f (u, t) ∂volume := by
  rw [suzukiAperturePrefix, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [suzukiH01FourierTriangleKernel, suzukiApertureUpperKernel,
    indicator_apply, mem_setOf_eq, mem_Iic]
  split_ifs <;> simp [mul_comm]

theorem suzukiAperture_mul_upperFourierPhase_eq_integral_triangle
    (a ξ : ℝ) (f : SuzukiApertureIntervalL2 a)
    (u : SuzukiApertureInterval a) :
    f u * (∫ t, (Ici u).indicator
      (suzukiApertureFourierPhase a ξ) t ∂volume) =
      ∫ t, suzukiH01FourierTriangleKernel a ξ f (u, t) ∂volume := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [suzukiH01FourierTriangleKernel, suzukiApertureUpperKernel,
    indicator_apply, mem_setOf_eq, mem_Ici]
  split_ifs <;> simp

theorem integral_phase_mul_suzukiAperturePrefix_eq_upper
    (a ξ : ℝ) (f : SuzukiApertureIntervalL2 a) :
    (∫ t, suzukiApertureFourierPhase a ξ t *
        suzukiAperturePrefix a f t ∂volume) =
      ∫ u, f u * (∫ t, (Ici u).indicator
        (suzukiApertureFourierPhase a ξ) t ∂volume) ∂volume := by
  have htri := integrable_suzukiH01FourierTriangleKernel a ξ f
  calc
    _ = ∫ t, ∫ u, suzukiH01FourierTriangleKernel a ξ f (u, t)
        ∂volume ∂volume := by
      apply integral_congr_ae
      exact ae_of_all _
        (suzukiApertureFourierPhase_mul_prefix_eq_integral_triangle a ξ f)
    _ = ∫ u, ∫ t, suzukiH01FourierTriangleKernel a ξ f (u, t)
        ∂volume ∂volume := by
      exact (integral_integral_swap
        (f := fun u t => suzukiH01FourierTriangleKernel a ξ f (u, t)) htri).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun u =>
        (suzukiAperture_mul_upperFourierPhase_eq_integral_triangle a ξ f u).symm

theorem integral_upper_suzukiApertureFourierPhase_eq_intervalIntegral
    (a : SuzukiPositiveAperture) (ξ : ℝ)
    (u : SuzukiApertureInterval a.1) :
    (∫ t, (Ici u).indicator
      (suzukiApertureFourierPhase a.1 ξ) t ∂volume) =
      ∫ x in (u : ℝ)..a.1, boundaryFourierPhase ξ x := by
  have hset : Ici (u : ℝ) ∩ Icc (-a.1) a.1 = Icc (u : ℝ) a.1 := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨hux, -, hxa⟩
      exact ⟨hux, hxa⟩
    · rintro ⟨hux, hxa⟩
      exact ⟨hux, le_trans u.property.1 hux, hxa⟩
  calc
    (∫ t : SuzukiApertureInterval a.1,
        (Ici u).indicator (suzukiApertureFourierPhase a.1 ξ) t ∂volume) =
      ∫ t : SuzukiApertureInterval a.1,
        (Ici (u : ℝ)).indicator (boundaryFourierPhase ξ) (t : ℝ) ∂volume := by
          apply integral_congr_ae
          filter_upwards with t
          simp only [indicator_apply, mem_Ici, suzukiApertureFourierPhase]
          rfl
    _ = ∫ x in Icc (-a.1) a.1,
        (Ici (u : ℝ)).indicator (boundaryFourierPhase ξ) x := by
          rw [← integral_subtype measurableSet_Icc]
    _ = ∫ x in Icc (u : ℝ) a.1, boundaryFourierPhase ξ x := by
          rw [integral_indicator measurableSet_Ici,
            Measure.restrict_restrict measurableSet_Ici, hset]
    _ = ∫ x in (u : ℝ)..a.1, boundaryFourierPhase ξ x := by
          rw [integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le u.property.2]

theorem norm_integral_upper_suzukiApertureFourierPhase_le
    (a : SuzukiPositiveAperture) (ξ : ℝ) (hξ : ξ ≠ 0)
    (u : SuzukiApertureInterval a.1) :
    ‖∫ t, (Ici u).indicator
      (suzukiApertureFourierPhase a.1 ξ) t ∂volume‖ ≤
      2 / (2 * Real.pi * |ξ|) := by
  rw [integral_upper_suzukiApertureFourierPhase_eq_intervalIntegral a ξ u]
  let c : ℂ := -(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ))
  have hc : c ≠ 0 := by
    dsimp [c]
    exact neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero) (ofReal_ne_zero.mpr hξ))
  have hphase : boundaryFourierPhase ξ = fun x : ℝ => Complex.exp (c * (x : ℂ)) := by
    funext x
    unfold boundaryFourierPhase
    congr 1
    dsimp [c]
    ring
  rw [hphase, integral_exp_mul_complex hc, norm_div]
  have hnum : ‖Complex.exp (c * (a.1 : ℂ)) -
      Complex.exp (c * ((u : ℝ) : ℂ))‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp (c * (a.1 : ℂ))‖ +
          ‖Complex.exp (c * ((u : ℝ) : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp, Complex.norm_exp]
        have hca : (c * (a.1 : ℂ)).re = 0 := by simp [c, Complex.mul_re]
        have hcu : (c * ((u : ℝ) : ℂ)).re = 0 := by simp [c, Complex.mul_re]
        rw [hca, hcu]
        norm_num
  have hden : ‖c‖ = 2 * Real.pi * |ξ| := by
    dsimp [c]
    rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [hden]
  exact div_le_div_of_nonneg_right hnum (by positivity)

theorem integrable_suzukiApertureZeroExtend
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    Integrable (suzukiApertureZeroExtend f) := by
  exact (integrableOn_suzukiApertureZeroExtend a f).integrable_of_forall_notMem_eq_zero
    fun x hx => suzukiApertureZeroExtend_eq_zero_of_notMem f hx

theorem fourier_suzukiApertureZeroExtend_primitive_eq_integral_prefix
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) (ξ : ℝ) :
    𝓕 (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)) ξ =
      ∫ t : SuzukiApertureInterval a.1,
        suzukiApertureFourierPhase a.1 ξ t *
          suzukiAperturePrefix a.1 f t ∂volume := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) •
        suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f) x) =
      ∫ x : ℝ, boundaryFourierPhase ξ x *
        suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f) x := by
      apply integral_congr_ae
      filter_upwards with x
      change Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) * _ = _
      congr 1
      unfold boundaryFourierPhase
      congr 1
      push_cast
      ring
    _ = ∫ x in Icc (-a.1) a.1, boundaryFourierPhase ξ x *
        suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f) x := by
      rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      rw [suzukiApertureZeroExtend_eq_zero_of_notMem _ hx, mul_zero]
    _ = ∫ t : SuzukiApertureInterval a.1,
        boundaryFourierPhase ξ (t : ℝ) *
          suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f) (t : ℝ)
          ∂volume := by
      rw [← integral_subtype measurableSet_Icc]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [suzukiApertureRepresentative_ae
          (suzukiAperturePrimitive a.1 f),
        suzukiAperturePrimitive_coeFn a.1 f] with t hrep hprim
      rw [suzukiApertureZeroExtend_apply, hrep, hprim]
      rfl

theorem norm_fourier_suzukiApertureZeroExtend_primitive_le_tail
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1)
    (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖𝓕 (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)) ξ‖ ≤
      (2 * (∫ t : SuzukiApertureInterval a.1, ‖f t‖ ∂volume)) /
        (2 * Real.pi * |ξ|) := by
  rw [fourier_suzukiApertureZeroExtend_primitive_eq_integral_prefix]
  rw [integral_phase_mul_suzukiAperturePrefix_eq_upper]
  calc
    ‖∫ u : SuzukiApertureInterval a.1, f u *
        (∫ t, (Ici u).indicator
          (suzukiApertureFourierPhase a.1 ξ) t ∂volume) ∂volume‖
        ≤ ∫ u : SuzukiApertureInterval a.1,
          ‖f u * (∫ t, (Ici u).indicator
            (suzukiApertureFourierPhase a.1 ξ) t ∂volume)‖ ∂volume :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : SuzukiApertureInterval a.1,
        ‖f u‖ * (2 / (2 * Real.pi * |ξ|)) ∂volume := by
      apply integral_mono_ae
      · exact ((integrable_suzukiH01FourierTriangleKernel a.1 ξ f).integral_prod_left.norm).congr
          (ae_of_all _ fun u => congrArg norm
            (suzukiAperture_mul_upperFourierPhase_eq_integral_triangle
              a.1 ξ f u).symm)
      · exact (((Lp.memLp f).integrable (by norm_num)).norm.const_mul
          (2 / (2 * Real.pi * |ξ|))).congr (ae_of_all _ fun u => by
            ring)
      · filter_upwards with u
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_integral_upper_suzukiApertureFourierPhase_le a ξ hξ u)
          (norm_nonneg _)
    _ = (2 * (∫ t : SuzukiApertureInterval a.1, ‖f t‖ ∂volume)) /
        (2 * Real.pi * |ξ|) := by
      rw [integral_mul_const]
      ring

/-- General finite-energy envelope: a measurable Fourier profile bounded both globally and by
`M / |ξ|` has finite Suzuki logarithmic energy. -/
theorem integrable_suzukiLogWeight_norm_sq_of_general_fourier_envelope
    (F : ℝ → ℂ) (C M : ℝ)
    (hF : AEStronglyMeasurable F (volume : Measure ℝ))
    (hbound : ∀ ξ, ξ ≠ 0 → ‖F ξ‖ ≤ min |C| (|M| / |ξ|)) :
    Integrable (fun ξ : ℝ => suzukiLogWeight ξ * ‖F ξ‖ ^ 2) := by
  let r : ℝ := max (|C| / 2) 1
  have hr : 0 < r := by
    dsimp [r]
    positivity
  let G : ℝ → ℂ := fun ξ => (r : ℂ)⁻¹ • F ξ
  have hGmeas : AEStronglyMeasurable G (volume : Measure ℝ) :=
    hF.const_smul ((r : ℂ)⁻¹)
  have hGbound : ∀ ξ, ξ ≠ 0 → ‖G ξ‖ ≤
      min (2 / (((0 : ℕ) : ℝ) + 1)) (|(M / r)| / |ξ|) := by
    intro ξ hξ
    have hb := hbound ξ hξ
    have hsmall0 : ‖F ξ‖ ≤ |C| := hb.trans (min_le_left _ _)
    have htail0 : ‖F ξ‖ ≤ |M| / |ξ| := hb.trans (min_le_right _ _)
    have hrC : |C| / 2 ≤ r := le_max_left _ _
    have hsmall : r⁻¹ * ‖F ξ‖ ≤ 2 := by
      rw [inv_mul_le_iff₀ hr]
      nlinarith
    have htail : r⁻¹ * ‖F ξ‖ ≤ |(M / r)| / |ξ| := by
      calc
        r⁻¹ * ‖F ξ‖ ≤ r⁻¹ * (|M| / |ξ|) :=
          mul_le_mul_of_nonneg_left htail0 (inv_nonneg.mpr hr.le)
        _ = |(M / r)| / |ξ| := by
          rw [abs_div, abs_of_pos hr]
          field_simp [ne_of_gt hr]
    change ‖(r : ℂ)⁻¹ • F ξ‖ ≤ _
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
    norm_num
    exact ⟨hsmall, htail⟩
  have hGenergy := integrable_suzukiLogWeight_norm_sq_of_fourier_envelope
    G 0 (M / r) hGmeas hGbound
  refine ((hGenergy.const_mul (r ^ 2)).congr ?_)
  filter_upwards with ξ
  dsimp [G]
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  have hrne : r ≠ 0 := ne_of_gt hr
  field_simp [hrne]

theorem integrable_suzukiAperturePrimitive_hlogEnergy
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    Integrable (fun ξ : ℝ => suzukiLogWeight ξ *
      ‖𝓕 (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)) ξ‖ ^ 2) := by
  let F := 𝓕 (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f))
  let C := ∫ x : ℝ, ‖suzukiApertureZeroExtend
    (suzukiAperturePrimitive a.1 f) x‖ ∂volume
  let M := (2 * (∫ t : SuzukiApertureInterval a.1, ‖f t‖ ∂volume)) /
    (2 * Real.pi)
  have hInt : Integrable
      (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)) :=
    integrable_suzukiApertureZeroExtend a (suzukiAperturePrimitive a.1 f)
  apply integrable_suzukiLogWeight_norm_sq_of_general_fourier_envelope F C M
    (GaloisForLFunctions.RHTower.continuous_fourier_of_integrable
      hInt).aestronglyMeasurable
  intro ξ hξ
  apply le_min
  · exact (GaloisForLFunctions.HTGeometry.norm_fourierReal_le_integral_norm
      (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)) ξ).trans_eq (by
        dsimp [C]
        rw [abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)])
  · have htail := norm_fourier_suzukiApertureZeroExtend_primitive_le_tail a f ξ hξ
    dsimp [M]
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    rw [abs_of_nonneg (mul_nonneg (by norm_num)
      (integral_nonneg fun _ => norm_nonneg _))]
    exact htail.trans_eq (by
      field_simp [abs_ne_zero.mpr hξ, Real.pi_ne_zero])

theorem indicator_suzukiApertureZeroExtend
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    (Icc (-a.1) a.1).indicator (suzukiApertureZeroExtend f) =
      suzukiApertureZeroExtend f := by
  funext x
  by_cases hx : x ∈ Icc (-a.1) a.1
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx,
      suzukiApertureZeroExtend_eq_zero_of_notMem f hx]

/-- Every literal Dirichlet primitive belongs to Suzuki's exact logarithmic form domain. -/
def suzukiAperturePrimitiveHlogFormVector
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    SuzukiHlogFormDomain a :=
  suzukiHlogFormVectorOfFunction a
    (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f))
    (integrable_suzukiApertureZeroExtend a (suzukiAperturePrimitive a.1 f))
    (suzukiApertureZeroExtend_memLp (suzukiAperturePrimitive a.1 f))
    (integrable_suzukiAperturePrimitive_hlogEnergy a f)
    (indicator_suzukiApertureZeroExtend a (suzukiAperturePrimitive a.1 f))

theorem suzukiHlogFormEmbedding_primitiveHlogFormVector
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    suzukiHlogFormEmbedding a (suzukiAperturePrimitiveHlogFormVector a f) =
      suzukiApertureZeroExtendL2 (suzukiAperturePrimitive a.1 f) := by
  exact suzukiHlogFormEmbedding_formVectorOfFunction a
    (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f))
    (integrable_suzukiApertureZeroExtend a (suzukiAperturePrimitive a.1 f))
    (suzukiApertureZeroExtend_memLp (suzukiAperturePrimitive a.1 f))
    (integrable_suzukiAperturePrimitive_hlogEnergy a f)
    (indicator_suzukiApertureZeroExtend a (suzukiAperturePrimitive a.1 f))

/-- Every literal Dirichlet primitive, transported to Connes--Consani's exact form domain. -/
def suzukiAperturePrimitiveCCMFormVector
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    CCMArchimedeanFormDomain a :=
  ccmLogFormToArchimedean a (suzukiAperturePrimitiveHlogFormVector a f)

theorem ccmArchimedeanFormToAperture_primitiveCCMFormVector
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    ccmArchimedeanFormToAperture a (suzukiAperturePrimitiveCCMFormVector a f) =
      suzukiApertureL2Equiv a (suzukiAperturePrimitive a.1 f) := by
  apply Subtype.ext
  change ccmArchimedeanFourierToTime
      (ccmLogToArchimedean (suzukiAperturePrimitiveHlogFormVector a f).1) =
    suzukiApertureZeroExtendL2 (suzukiAperturePrimitive a.1 f)
  rw [ccmArchimedeanFourierToTime_logToArchimedean]
  exact suzukiHlogFormEmbedding_primitiveHlogFormVector a f

/-- Linear inclusion of the derivative coordinate into Suzuki's exact logarithmic form domain. -/
def suzukiAperturePrimitiveHlogFormLM (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →ₗ[ℂ] SuzukiHlogFormDomain a where
  toFun := suzukiAperturePrimitiveHlogFormVector a
  map_add' f g := by
    apply suzukiHlogFormEmbedding_injective a
    rw [map_add, suzukiHlogFormEmbedding_primitiveHlogFormVector,
      suzukiHlogFormEmbedding_primitiveHlogFormVector,
      suzukiHlogFormEmbedding_primitiveHlogFormVector,
      suzukiAperturePrimitive_add, suzukiApertureZeroExtendL2_add]
  map_smul' c f := by
    apply suzukiHlogFormEmbedding_injective a
    rw [map_smul, suzukiHlogFormEmbedding_primitiveHlogFormVector,
      suzukiHlogFormEmbedding_primitiveHlogFormVector,
      suzukiAperturePrimitive_smul, suzukiApertureZeroExtendL2_smul]
    rfl

/-- Linear inclusion into the exact Connes--Consani/Suzuki form domain. -/
def suzukiAperturePrimitiveCCMFormLM (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →ₗ[ℂ] CCMArchimedeanFormDomain a :=
  (ccmLogFormToArchimedean a).toLinearMap.comp
    (suzukiAperturePrimitiveHlogFormLM a)

theorem suzukiAperturePrimitiveCCMFormLM_apply
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    suzukiAperturePrimitiveCCMFormLM a f =
      suzukiAperturePrimitiveCCMFormVector a f := rfl

def suzukiDirichletInverseRangeEquiv (a : SuzukiPositiveAperture) :
    SuzukiApertureZeroMean a ≃ₗ[ℂ] SuzukiApertureH01 a :=
  LinearEquiv.ofInjective (suzukiDirichletInverseCLM a).toLinearMap
    (suzukiDirichletInverseCLM_injective a)

def suzukiDirichletDomainToH01 (a : SuzukiPositiveAperture) :
    (suzukiDirichletDerivative a).domain →ₗ[ℂ] SuzukiApertureH01 a where
  toFun v := ⟨v.1, by
    rw [← suzukiDirichletDerivative_domain a]
    exact v.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exact form-domain lift of Suzuki's operator core `H₀¹(-a,a)`. -/
def suzukiDirichletDomainCCMFormLift (a : SuzukiPositiveAperture) :
    (suzukiDirichletDerivative a).domain →ₗ[ℂ] CCMArchimedeanFormDomain a :=
  (suzukiAperturePrimitiveCCMFormLM a).comp
    ((SuzukiApertureZeroMean a).subtype.comp
      ((suzukiDirichletInverseRangeEquiv a).symm.toLinearMap.comp
        (suzukiDirichletDomainToH01 a)))

theorem suzukiWeilIntervalFormEmbedding_dirichletDomainCCMFormLift
    (a : SuzukiPositiveAperture)
    (v : (suzukiDirichletDerivative a).domain) :
    suzukiWeilIntervalFormEmbedding a
        (suzukiDirichletDomainCCMFormLift a v) = v.1 := by
  let e := suzukiDirichletInverseRangeEquiv a
  let w : SuzukiApertureH01 a := suzukiDirichletDomainToH01 a v
  change suzukiPhysicalToApertureCLM a
      (ccmArchimedeanFormToAperture a
        (suzukiAperturePrimitiveCCMFormVector a ((e.symm w :
          SuzukiApertureZeroMean a) : SuzukiApertureIntervalL2 a.1))) = v.1
  rw [ccmArchimedeanFormToAperture_primitiveCCMFormVector]
  change (suzukiApertureL2Equiv a).symm
      (suzukiApertureL2Equiv a
        (suzukiAperturePrimitive a.1 ((e.symm w : SuzukiApertureZeroMean a) :
          SuzukiApertureIntervalL2 a.1))) = v.1
  rw [(suzukiApertureL2Equiv a).symm_apply_apply]
  have he := e.apply_symm_apply w
  exact congrArg Subtype.val he

def suzukiSquaredLogEnvelopeDom (C M ξ : ℝ) : ℝ :=
  (4 * C ^ 2 + 100 * M ^ 2) * (1 + |ξ|) ^ (-(3 / 2 : ℝ))

theorem integrable_suzukiSquaredLogEnvelopeDom (C M : ℝ) :
    Integrable (suzukiSquaredLogEnvelopeDom C M) := by
  unfold suzukiSquaredLogEnvelopeDom
  exact (integrable_one_add_norm (E := ℝ) (μ := volume)
    (show (Module.finrank ℝ ℝ : ℝ) < (3 / 2 : ℝ) by norm_num)).const_mul _

theorem one_add_log_sq_le_twentyFive_sqrt {x : ℝ} (hx : 1 ≤ x) :
    (1 + Real.log x) ^ 2 ≤ 25 * x ^ (1 / 2 : ℝ) := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog := Real.log_le_rpow_div hx0 (show 0 < (1 / 4 : ℝ) by norm_num)
  have hquarter : 1 ≤ x ^ (1 / 4 : ℝ) := by
    convert Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hx
      (by norm_num : (0 : ℝ) ≤ 1 / 4) using 1 <;> norm_num
  have hupper : 1 + Real.log x ≤ 5 * x ^ (1 / 4 : ℝ) := by
    rw [show x ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) = 4 * x ^ (1 / 4 : ℝ) by ring] at hlog
    linarith
  have hsquare : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hx0]
    norm_num
  rw [← hsquare]
  nlinarith [sq_nonneg (1 + Real.log x), sq_nonneg (x ^ (1 / 4 : ℝ))]

/-- A simultaneous global and inverse-linear Fourier envelope has square-logarithmic energy.
This is the operator-domain strengthening of the form-domain envelope. -/
theorem integrable_suzukiLogWeight_sq_norm_sq_of_general_fourier_envelope
    (F : ℝ → ℂ) (C M : ℝ)
    (hF : AEStronglyMeasurable F (volume : Measure ℝ))
    (hbound : ∀ ξ, ξ ≠ 0 → ‖F ξ‖ ≤ min |C| (|M| / |ξ|)) :
    Integrable (fun ξ : ℝ => suzukiLogWeight ξ ^ 2 * ‖F ξ‖ ^ 2) := by
  have hne : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
    rw [ae_iff]
    simp
  refine Integrable.mono' (integrable_suzukiSquaredLogEnvelopeDom C M)
    (measurable_suzukiLogWeight.aestronglyMeasurable.pow 2 |>.mul (hF.norm.pow 2)) ?_
  filter_upwards [hne] with ξ hξ
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  by_cases hsmall : |ξ| ≤ 1
  · have hlog : Real.log |ξ| ≤ 0 := Real.log_nonpos (abs_nonneg ξ) hsmall
    have hFle : ‖F ξ‖ ≤ |C| :=
      (hbound ξ hξ).trans (min_le_left _ _)
    have hFsq : ‖F ξ‖ ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs C]
      nlinarith [norm_nonneg (F ξ), abs_nonneg C]
    have hdom := one_fourth_le_one_add_rpow_neg_three_halves
      (abs_nonneg ξ) hsmall
    rw [suzukiLogWeight, max_eq_right hlog, add_zero, one_pow, one_mul]
    unfold suzukiSquaredLogEnvelopeDom
    have hcoeff : 4 * C ^ 2 ≤ 4 * C ^ 2 + 100 * M ^ 2 := by
      nlinarith [sq_nonneg M]
    calc
      ‖F ξ‖ ^ 2 ≤ C ^ 2 := hFsq
      _ = (4 * C ^ 2) * (1 / 4) := by ring
      _ ≤ (4 * C ^ 2) * (1 + |ξ|) ^ (-(3 / 2 : ℝ)) := by gcongr
      _ ≤ (4 * C ^ 2 + 100 * M ^ 2) *
          (1 + |ξ|) ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
  · have hlarge : 1 ≤ |ξ| := le_of_not_ge hsmall
    have hlog0 : 0 ≤ Real.log |ξ| := Real.log_nonneg hlarge
    have hFle : ‖F ξ‖ ≤ |M| / |ξ| :=
      (hbound ξ hξ).trans (min_le_right _ _)
    have habspos : 0 < |ξ| := abs_pos.mpr hξ
    have hFsq : ‖F ξ‖ ^ 2 ≤ M ^ 2 / |ξ| ^ 2 := by
      have hsq0 : ‖F ξ‖ ^ 2 ≤ (|M| / |ξ|) ^ 2 := by
        nlinarith [norm_nonneg (F ξ), abs_nonneg M,
          div_nonneg (abs_nonneg M) (abs_nonneg ξ)]
      calc
        ‖F ξ‖ ^ 2 ≤ (|M| / |ξ|) ^ 2 := hsq0
        _ = M ^ 2 / |ξ| ^ 2 := by rw [div_pow, sq_abs]
    have hlogSq := one_add_log_sq_le_twentyFive_sqrt hlarge
    have hrpow : |ξ| ^ (1 / 2 : ℝ) / |ξ| ^ 2 =
        |ξ| ^ (-(3 / 2 : ℝ)) := by
      rw [show |ξ| ^ 2 = |ξ| ^ (2 : ℝ) by norm_num [Real.rpow_natCast]]
      rw [← Real.rpow_sub habspos]
      norm_num
    have htail := one_fourth_mul_x_rpow_le_one_add_rpow_neg_three_halves hlarge
    rw [suzukiLogWeight, max_eq_left hlog0]
    unfold suzukiSquaredLogEnvelopeDom
    calc
      (1 + Real.log |ξ|) ^ 2 * ‖F ξ‖ ^ 2 ≤
          (25 * |ξ| ^ (1 / 2 : ℝ)) * (M ^ 2 / |ξ| ^ 2) := by gcongr
      _ = 25 * M ^ 2 * |ξ| ^ (-(3 / 2 : ℝ)) := by rw [← hrpow]; ring
      _ = (100 * M ^ 2) * ((1 / 4) * |ξ| ^ (-(3 / 2 : ℝ))) := by ring
      _ ≤ (100 * M ^ 2) * (1 + |ξ|) ^ (-(3 / 2 : ℝ)) := by gcongr
      _ ≤ (4 * C ^ 2 + 100 * M ^ 2) *
          (1 + |ξ|) ^ (-(3 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right
        · nlinarith [sq_nonneg C]
        · positivity

theorem integrable_suzukiAperturePrimitive_hlogEnergy_sq
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    Integrable (fun ξ : ℝ => suzukiLogWeight ξ ^ 2 *
      ‖𝓕 (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)) ξ‖ ^ 2) := by
  let F := 𝓕 (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f))
  let C := ∫ x : ℝ, ‖suzukiApertureZeroExtend
    (suzukiAperturePrimitive a.1 f) x‖ ∂volume
  let M := (2 * (∫ t : SuzukiApertureInterval a.1, ‖f t‖ ∂volume)) /
    (2 * Real.pi)
  have hInt : Integrable
      (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)) :=
    integrable_suzukiApertureZeroExtend a (suzukiAperturePrimitive a.1 f)
  apply integrable_suzukiLogWeight_sq_norm_sq_of_general_fourier_envelope F C M
    (GaloisForLFunctions.RHTower.continuous_fourier_of_integrable
      hInt).aestronglyMeasurable
  intro ξ hξ
  apply le_min
  · exact (GaloisForLFunctions.HTGeometry.norm_fourierReal_le_integral_norm
      (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)) ξ).trans_eq (by
        dsimp [C]
        rw [abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)])
  · have htail := norm_fourier_suzukiApertureZeroExtend_primitive_le_tail a f ξ hξ
    dsimp [M]
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    rw [abs_of_nonneg (mul_nonneg (by norm_num)
      (integral_nonneg fun _ => norm_nonneg _))]
    exact htail.trans_eq (by
      field_simp [abs_ne_zero.mpr hξ, Real.pi_ne_zero])

end RHTower
