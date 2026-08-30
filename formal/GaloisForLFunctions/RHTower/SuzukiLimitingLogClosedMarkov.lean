import GaloisForLFunctions.RHTower.SuzukiLimitingLogIrreducibilityCore
import GaloisForLFunctions.RHTower.SuzukiLimitingLogGroundIdentification
import GaloisForLFunctions.RHTower.CCMRestrictedWeilMixedSourceForm
import GaloisForLFunctions.HTGeometry.WeakSequentialCompactness
import GaloisForLFunctions.RHTower.SoninEulerQuadraticCorner
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiLimitingLogClosedMarkovLocalInst1 : SFinite ccmArchimedeanFormMeasure := by
  unfold ccmArchimedeanFormMeasure
  infer_instance

local instance suzukiLimitingLogClosedMarkovLocalInst2 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

/-- Smooth one-Lipschitz approximation to the real modulus, fixing zero. -/
def suzukiSmoothAbsolute (ε x : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + ε ^ 2) - ε

@[simp] theorem suzukiSmoothAbsolute_zero {ε : ℝ} (hε : 0 ≤ ε) :
    suzukiSmoothAbsolute ε 0 = 0 := by
  simp [suzukiSmoothAbsolute, Real.sqrt_sq hε]

theorem contDiff_suzukiSmoothAbsolute {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiSmoothAbsolute ε) := by
  unfold suzukiSmoothAbsolute
  apply ContDiff.sub
  · apply ContDiff.sqrt
      ((contDiff_id.pow 2).add (contDiff_const.pow 2))
    intro x hx
    have he2 : 0 < ε ^ 2 := sq_pos_of_ne_zero hε
    nlinarith [sq_nonneg x]
  · exact contDiff_const

theorem abs_le_sqrt_sq_add_sq (x ε : ℝ) :
    |x| ≤ Real.sqrt (x ^ 2 + ε ^ 2) := by
  rw [Real.le_sqrt (abs_nonneg x) (add_nonneg (sq_nonneg x) (sq_nonneg ε))]
  rw [sq_abs]
  exact le_add_of_nonneg_right (sq_nonneg ε)

theorem sqrt_sq_add_sq_le_abs_add {x ε : ℝ} (hε : 0 ≤ ε) :
    Real.sqrt (x ^ 2 + ε ^ 2) ≤ |x| + ε := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact add_nonneg (abs_nonneg x) hε
  · nlinarith [sq_abs x, mul_nonneg (abs_nonneg x) hε]

theorem suzukiSmoothAbsolute_nonneg {ε x : ℝ} (hε : 0 ≤ ε) :
  0 ≤ suzukiSmoothAbsolute ε x := by
  unfold suzukiSmoothAbsolute
  have h : ε ≤ Real.sqrt (x ^ 2 + ε ^ 2) := by
    simpa [abs_of_nonneg hε, add_comm] using abs_le_sqrt_sq_add_sq ε x
  nlinarith

theorem suzukiSmoothAbsolute_le_abs {ε x : ℝ} (hε : 0 ≤ ε) :
    suzukiSmoothAbsolute ε x ≤ |x| := by
  unfold suzukiSmoothAbsolute
  linarith [sqrt_sq_add_sq_le_abs_add (x := x) hε]

theorem abs_sub_suzukiSmoothAbsolute_le {ε x : ℝ} (hε : 0 ≤ ε) :
    |(|x| - suzukiSmoothAbsolute ε x)| ≤ ε := by
  have hupper := suzukiSmoothAbsolute_le_abs (x := x) hε
  have hlower := abs_le_sqrt_sq_add_sq x ε
  rw [abs_of_nonneg (sub_nonneg.mpr hupper)]
  unfold suzukiSmoothAbsolute
  linarith

theorem abs_suzukiSmoothAbsolute_le {ε x : ℝ} (hε : 0 ≤ ε) :
    |suzukiSmoothAbsolute ε x| ≤ |x| := by
  rw [abs_of_nonneg (suzukiSmoothAbsolute_nonneg (x := x) hε)]
  exact suzukiSmoothAbsolute_le_abs hε

theorem abs_suzukiSmoothAbsolute_sub_le {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    |suzukiSmoothAbsolute ε x - suzukiSmoothAbsolute ε y| ≤ |x - y| := by
  let A := Real.sqrt (x ^ 2 + ε ^ 2)
  let B := Real.sqrt (y ^ 2 + ε ^ 2)
  have hargA : 0 ≤ x ^ 2 + ε ^ 2 := add_nonneg (sq_nonneg x) (sq_nonneg ε)
  have hargB : 0 ≤ y ^ 2 + ε ^ 2 := add_nonneg (sq_nonneg y) (sq_nonneg ε)
  have hA2 : A ^ 2 = x ^ 2 + ε ^ 2 := Real.sq_sqrt hargA
  have hB2 : B ^ 2 = y ^ 2 + ε ^ 2 := Real.sq_sqrt hargB
  have hApos : 0 < A := Real.sqrt_pos.2 (by nlinarith [sq_pos_of_pos hε])
  have hBpos : 0 < B := Real.sqrt_pos.2 (by nlinarith [sq_pos_of_pos hε])
  have hden : 0 < A + B := add_pos hApos hBpos
  have hrat : A - B = (x - y) * (x + y) / (A + B) := by
    apply (eq_div_iff hden.ne').2
    nlinarith
  have hxy : |x + y| ≤ A + B := by
    calc
      |x + y| ≤ |x| + |y| := abs_add_le x y
      _ ≤ A + B := add_le_add (abs_le_sqrt_sq_add_sq x ε)
        (abs_le_sqrt_sq_add_sq y ε)
  change |(A - ε) - (B - ε)| ≤ |x - y|
  rw [sub_sub_sub_cancel_right, hrat, abs_div, abs_mul, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  exact mul_le_mul_of_nonneg_left hxy (abs_nonneg (x - y))

/-- Smooth source-core approximation to the modulus of a real Suzuki core vector. -/
def suzukiSmoothAbsoluteCore
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1)
    (ε : ℝ) (hε : 0 < ε) :
    GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1 where
  toFun := fun x => suzukiSmoothAbsolute ε (u x)
  smooth := (contDiff_suzukiSmoothAbsolute hε.ne').comp u.smooth
  supportRadius := u.supportRadius
  supportRadius_nonneg := u.supportRadius_nonneg
  supportRadius_lt_aperture := u.supportRadius_lt_aperture
  support_subset := by
    intro x hx
    apply u.support_subset
    intro hux
    apply hx
    simp [hux, suzukiSmoothAbsolute, Real.sqrt_sq hε.le]

@[simp] theorem suzukiSmoothAbsoluteCore_apply
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1)
    (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    suzukiSmoothAbsoluteCore u ε hε x = suzukiSmoothAbsolute ε (u x) := rfl

/-- Exact finite-part Markov estimate for any pair of smooth real core vectors related by a
zero-order contraction and a jump contraction. -/
theorem suzukiFinitePartEnergy_le_of_pointwise_contraction
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1)
    (hnorm : ∀ x, |v x| ≤ |u x|)
    (hjump : ∀ x y, |v x - v y| ≤ |u x - u y|) :
    suzukiFinitePartEnergy 1 v ≤ suzukiFinitePartEnergy 1 u := by
  have hvD := suzukiFinitePartDifferenceEnergy_intervalIntegrable
    (by norm_num : (0 : ℝ) < 1) v.smooth
  have huD := suzukiFinitePartDifferenceEnergy_intervalIntegrable
    (by norm_num : (0 : ℝ) < 1) u.smooth
  have hD : suzukiFinitePartDifferenceEnergy 1 v ≤
      suzukiFinitePartDifferenceEnergy 1 u := by
    unfold suzukiFinitePartDifferenceEnergy
    apply intervalIntegral.integral_mono_on (by norm_num) hvD.2 huD.2
    intro x hx
    apply intervalIntegral.integral_mono_on (by norm_num) (hvD.1 x hx) (huD.1 x hx)
    intro y _
    exact mul_le_mul_of_nonneg_right
      (sq_le_sq.mpr (hjump x y)) (inv_nonneg.mpr (abs_nonneg _))
  have hvP := suzukiFinitePartLogPotential_integrable_upper
    (by norm_num : (0 : ℝ) < 1) v.supportRadius_nonneg
      v.supportRadius_lt_aperture v.continuous v.support_subset
  have huP := suzukiFinitePartLogPotential_integrable_upper
    (by norm_num : (0 : ℝ) < 1) u.supportRadius_nonneg
      u.supportRadius_lt_aperture u.continuous u.support_subset
  have hP : suzukiFinitePartLogPotential 1 u ≤
      suzukiFinitePartLogPotential 1 v := by
    unfold suzukiFinitePartLogPotential
    apply intervalIntegral.integral_mono_on (by norm_num) huP.1 hvP.1
    intro x hx
    have hxabs : |x| ≤ 1 := (abs_le).2 hx
    have harg0 : 0 ≤ (1 : ℝ) ^ 2 - x ^ 2 := by
      have hsq : x ^ 2 ≤ (1 : ℝ) ^ 2 := by
        rw [sq_le_sq]
        simpa using hxabs
      nlinarith
    have harg1 : (1 : ℝ) ^ 2 - x ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg x]
    have hlog : Real.log ((1 : ℝ) ^ 2 - x ^ 2) ≤ 0 :=
      Real.log_nonpos harg0 harg1
    exact mul_le_mul_of_nonpos_left (sq_le_sq.mpr (hnorm x)) hlog
  unfold suzukiFinitePartEnergy
  nlinarith

theorem suzukiFinitePartEnergy_smoothAbsolute_le
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1)
    (ε : ℝ) (hε : 0 < ε) :
    suzukiFinitePartEnergy 1 (suzukiSmoothAbsoluteCore u ε hε) ≤
      suzukiFinitePartEnergy 1 u := by
  apply suzukiFinitePartEnergy_le_of_pointwise_contraction
  · intro x
    exact abs_suzukiSmoothAbsolute_le hε.le
  · intro x y
    exact abs_suzukiSmoothAbsolute_sub_le hε (u x) (u y)

theorem suzukiSmoothAbsoluteCore_mass_le
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1)
    (ε : ℝ) (hε : 0 < ε) :
    (∫ x in (-1 : ℝ)..1, (suzukiSmoothAbsoluteCore u ε hε x) ^ 2) ≤
      ∫ x in (-1 : ℝ)..1, u x ^ 2 := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (((suzukiSmoothAbsoluteCore u ε hε).continuous.pow 2).intervalIntegrable
      (-1 : ℝ) 1)
    ((u.continuous.pow 2).intervalIntegrable (-1 : ℝ) 1)
  intro x _
  exact sq_le_sq.mpr (abs_suzukiSmoothAbsolute_le hε.le)

def suzukiSmoothAbsoluteScale (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

theorem suzukiSmoothAbsoluteScale_pos (n : ℕ) :
    0 < suzukiSmoothAbsoluteScale n := by
  unfold suzukiSmoothAbsoluteScale
  positivity

theorem tendsto_suzukiSmoothAbsoluteScale_zero :
    Tendsto suzukiSmoothAbsoluteScale atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

def suzukiCoreAbsoluteIntervalContinuous
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    C(SuzukiApertureInterval 1, ℂ) where
  toFun x := ((|u (x : ℝ)| : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (u.continuous.comp continuous_subtype_val).abs

def suzukiCoreSmoothAbsoluteIntervalContinuous
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1)
    (ε : ℝ) : C(SuzukiApertureInterval 1, ℂ) where
  toFun x := (suzukiSmoothAbsolute ε (u (x : ℝ)) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    ((Real.continuous_sqrt.comp
      (((u.continuous.comp continuous_subtype_val).pow 2).add continuous_const)).sub
        continuous_const)

theorem norm_suzukiCoreSmoothAbsoluteIntervalContinuous_sub_le
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ‖suzukiCoreSmoothAbsoluteIntervalContinuous u ε -
        suzukiCoreAbsoluteIntervalContinuous u‖ ≤ ε := by
  rw [ContinuousMap.norm_le _ hε]
  intro x
  change ‖(suzukiSmoothAbsolute ε (u (x : ℝ)) : ℂ) -
    ((|u (x : ℝ)| : ℝ) : ℂ)‖ ≤ ε
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  exact abs_sub_suzukiSmoothAbsolute_le hε

theorem tendsto_suzukiCoreSmoothAbsoluteIntervalContinuous
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    Tendsto (fun n => suzukiCoreSmoothAbsoluteIntervalContinuous u
      (suzukiSmoothAbsoluteScale n)) atTop
      (nhds (suzukiCoreAbsoluteIntervalContinuous u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero
  · exact fun n => norm_nonneg _
  · exact fun n => norm_suzukiCoreSmoothAbsoluteIntervalContinuous_sub_le u
      (suzukiSmoothAbsoluteScale_pos n).le
  · exact tendsto_suzukiSmoothAbsoluteScale_zero

def suzukiCoreAbsoluteIntervalVector
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    SuzukiApertureIntervalL2 1 :=
  ContinuousMap.toLp 2 volume ℂ (suzukiCoreAbsoluteIntervalContinuous u)

theorem suzukiCoreAbsoluteIntervalVector_coeFn
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    (suzukiCoreAbsoluteIntervalVector u : SuzukiApertureInterval 1 → ℂ)
      =ᵐ[volume] fun x => ((|u (x : ℝ)| : ℝ) : ℂ) := by
  exact ContinuousMap.coeFn_toLp volume (suzukiCoreAbsoluteIntervalContinuous u)

def suzukiSmoothAbsoluteCoreFormVector
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) (n : ℕ) :
    CCMArchimedeanFormDomain suzukiLimitingUnitAperture :=
  suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture
    (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
      (suzukiSmoothAbsoluteScale_pos n))

theorem suzukiLimitingLogFormEmbedding_smoothAbsoluteCoreFormVector
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) (n : ℕ) :
    suzukiLimitingLogFormEmbedding (suzukiSmoothAbsoluteCoreFormVector u n) =
      ContinuousMap.toLp 2 volume ℂ
        (suzukiCoreSmoothAbsoluteIntervalContinuous u
          (suzukiSmoothAbsoluteScale n)) := by
  unfold suzukiSmoothAbsoluteCoreFormVector
  rw [← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
  apply MeasureTheory.Lp.ext
  filter_upwards [
    suzukiLimitingCoreIntervalVector_coeFn
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n)),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (volume : Measure (SuzukiApertureInterval 1))
      (suzukiCoreSmoothAbsoluteIntervalContinuous u
        (suzukiSmoothAbsoluteScale n))] with x hx hsmooth
  rw [hx, hsmooth]
  rfl

theorem tendsto_suzukiLimitingLogFormEmbedding_smoothAbsoluteCoreFormVector
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    Tendsto (fun n => suzukiLimitingLogFormEmbedding
      (suzukiSmoothAbsoluteCoreFormVector u n)) atTop
      (nhds (suzukiCoreAbsoluteIntervalVector u)) := by
  have h := (ContinuousMap.toLp 2
      (volume : Measure (SuzukiApertureInterval 1)) ℂ).continuous.tendsto
    (suzukiCoreAbsoluteIntervalContinuous u)
  have hc : Tendsto (fun n => ContinuousMap.toLp 2
      (volume : Measure (SuzukiApertureInterval 1)) ℂ
        (suzukiCoreSmoothAbsoluteIntervalContinuous u
          (suzukiSmoothAbsoluteScale n))) atTop
      (nhds (ContinuousMap.toLp 2
        (volume : Measure (SuzukiApertureInterval 1)) ℂ
          (suzukiCoreAbsoluteIntervalContinuous u))) :=
    h.comp (tendsto_suzukiCoreSmoothAbsoluteIntervalContinuous u)
  simpa only [suzukiCoreAbsoluteIntervalVector,
    suzukiLimitingLogFormEmbedding_smoothAbsoluteCoreFormVector] using hc

theorem norm_sq_suzukiLimitingLogFormEmbedding_coreFormVector
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    ‖suzukiLimitingLogFormEmbedding
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)‖ ^ 2 =
        ∫ x in (-1 : ℝ)..1, u x ^ 2 := by
  rw [← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
  have hnorm : ‖suzukiLimitingCoreIntervalVector u‖ ^ 2 =
      suzukiCoreAutocorrelation u 0 := by
    have h := congrArg Complex.re
      (inner_suzukiLimitingCoreIntervalVector_self u)
    rw [inner_self_eq_norm_sq_to_K] at h
    exact_mod_cast h
  have hmass :=
    integral_interval_sq_suzukiRestrictedWeilCore_eq_autocorrelation_zero
      suzukiLimitingUnitAperture u
  dsimp only [suzukiLimitingUnitAperture] at hmass
  exact hnorm.trans hmass.symm

theorem suzukiLimitingLogFormRiesz_diagonal_re
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    (inner ℂ
      (boundedPerturbedFormRiesz suzukiLimitingLogFormEmbedding
        suzukiLimitingLogBoundedRemainder q) q).re =
      (suzukiLimitingLogClosedForm q q).re +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          ‖suzukiLimitingLogFormEmbedding q‖ ^ 2 := by
  rw [boundedPerturbedFormRiesz_apply, inner_add_left, inner_add_left,
    inner_smul_left, suzukiLimitingLogFormEmbedding.adjoint_inner_left,
    suzukiLimitingLogFormEmbedding.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K]
  have hstar : (starRingEnd ℂ)
      (boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder : ℂ) =
      (boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder : ℂ) := by
    simp
  rw [hstar, inner_self_eq_norm_sq_to_K]
  have hqq : inner ℂ q q = (‖q‖ : ℂ) ^ 2 :=
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) q
  unfold suzukiLimitingLogClosedForm
  rw [hqq]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  norm_cast

theorem norm_sq_suzukiSmoothAbsoluteCoreFormVector_le
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) (n : ℕ) :
    ‖suzukiSmoothAbsoluteCoreFormVector u n‖ ^ 2 ≤
      suzukiFinitePartEnergy 1 u +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          (∫ x in (-1 : ℝ)..1, u x ^ 2) := by
  let ε := suzukiSmoothAbsoluteScale n
  have hε : 0 < ε := suzukiSmoothAbsoluteScale_pos n
  let v := suzukiSmoothAbsoluteCore u ε hε
  let qv := suzukiSmoothAbsoluteCoreFormVector u n
  have hcoer := boundedPerturbedFormRiesz_coercive
    suzukiLimitingLogFormEmbedding suzukiLimitingLogBoundedRemainder qv
  rw [suzukiLimitingLogFormRiesz_diagonal_re] at hcoer
  have hform : (suzukiLimitingLogClosedForm qv qv).re =
      suzukiFinitePartEnergy 1 v := by
    change (suzukiLimitingLogClosedForm
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v)
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v)).re = _
    rw [suzukiLimitingLogClosedForm_core_eq_weilFinitePartBlock,
      Complex.ofReal_re]
    simpa only [suzukiLimitingUnitAperture] using
      (suzukiWeilFinitePartBlock_eq_energy suzukiLimitingUnitAperture v)
  have hmass : ‖suzukiLimitingLogFormEmbedding qv‖ ^ 2 =
      ∫ x in (-1 : ℝ)..1, v x ^ 2 := by
    change ‖suzukiLimitingLogFormEmbedding
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v)‖ ^ 2 = _
    exact norm_sq_suzukiLimitingLogFormEmbedding_coreFormVector v
  rw [hform, hmass] at hcoer
  have henergy : suzukiFinitePartEnergy 1 v ≤ suzukiFinitePartEnergy 1 u := by
    exact suzukiFinitePartEnergy_smoothAbsolute_le u ε hε
  have hmassle : (∫ x in (-1 : ℝ)..1, v x ^ 2) ≤
      ∫ x in (-1 : ℝ)..1, u x ^ 2 := by
    exact suzukiSmoothAbsoluteCore_mass_le u ε hε
  have hshift : 0 ≤ boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder :=
    (boundedPerturbedFormShift_pos suzukiLimitingLogBoundedRemainder).le
  calc
    ‖qv‖ ^ 2 ≤ suzukiFinitePartEnergy 1 v +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          (∫ x in (-1 : ℝ)..1, v x ^ 2) := hcoer
    _ ≤ suzukiFinitePartEnergy 1 u +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          (∫ x in (-1 : ℝ)..1, u x ^ 2) :=
      add_le_add henergy (mul_le_mul_of_nonneg_left hmassle hshift)

/-- A bounded sequence in the limiting form domain has a weakly convergent subsequence whose
physical representatives converge strongly by compactness of the form embedding. -/
theorem exists_suzukiLimitingLogForm_weakSubseq
    (u : ℕ → CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (M : ℝ) (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ‖w‖ ≤ M ∧
        (∀ y, Tendsto (fun n => inner ℂ (u (φ n)) y) atTop
          (nhds (inner ℂ w y))) ∧
        Tendsto (fun n => ‖suzukiLimitingLogFormEmbedding (u (φ n)) -
          suzukiLimitingLogFormEmbedding w‖) atTop (nhds 0) := by
  obtain ⟨w, φ, hφ, hwM, hweak⟩ :=
    exists_weaklyConvergent_subseq_of_bounded u M hM
  refine ⟨w, φ, hφ, hwM, hweak, ?_⟩
  let f : ℕ → CCMArchimedeanFormDomain suzukiLimitingUnitAperture :=
    fun n => u (φ n) - w
  have hfM : ∀ n, ‖f n‖ ≤ M + ‖w‖ := by
    intro n
    calc
      ‖f n‖ ≤ ‖u (φ n)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ M + ‖w‖ := by linarith [hM (φ n)]
  have hfweak : ∀ ℓ :
      CCMArchimedeanFormDomain suzukiLimitingUnitAperture →L[ℂ] ℂ,
      Tendsto (fun n => ℓ (f n)) atTop (nhds 0) := by
    intro ℓ
    let y := (InnerProductSpace.toDual ℂ
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)).symm ℓ
    have hstar := (hweak y).star
    have hlin : Tendsto (fun n => ℓ (u (φ n))) atTop (nhds (ℓ w)) := by
      convert hstar using 1
      · funext n
        calc
          ℓ (u (φ n)) = inner ℂ y (u (φ n)) := by
            change ℓ (u (φ n)) =
              (InnerProductSpace.toDual ℂ
                (CCMArchimedeanFormDomain suzukiLimitingUnitAperture) y) (u (φ n))
            rw [(InnerProductSpace.toDual ℂ
              (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)).apply_symm_apply]
          _ = star (inner ℂ (u (φ n)) y) :=
            (inner_conj_symm (𝕜 := ℂ) y (u (φ n))).symm
      · change nhds (ℓ w) = nhds (star (inner ℂ w y))
        congr 1
        calc
          ℓ w = inner ℂ y w := by
            change ℓ w =
              (InnerProductSpace.toDual ℂ
                (CCMArchimedeanFormDomain suzukiLimitingUnitAperture) y) w
            rw [(InnerProductSpace.toDual ℂ
              (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)).apply_symm_apply]
          _ = star (inner ℂ w y) :=
            (inner_conj_symm (𝕜 := ℂ) y w).symm
    have hsub := hlin.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ℓ w) atTop (nhds (ℓ w)))
    simpa only [f, map_sub, sub_self] using hsub
  have hcompact :=
    IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null
      suzukiLimitingLogFormEmbedding
      isCompactOperator_suzukiLimitingLogFormEmbedding f (M + ‖w‖) hfM hfweak
  simpa only [f, map_sub] using hcompact

def suzukiLimitingLogShiftedEnergy
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) : ℝ :=
  (suzukiLimitingLogClosedForm q q).re +
    boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
      ‖suzukiLimitingLogFormEmbedding q‖ ^ 2

theorem suzukiLimitingLogShiftedEnergy_eq_riesz
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiLimitingLogShiftedEnergy q =
      (inner ℂ
        (boundedPerturbedFormRiesz suzukiLimitingLogFormEmbedding
          suzukiLimitingLogBoundedRemainder q) q).re := by
  exact (suzukiLimitingLogFormRiesz_diagonal_re q).symm

/-- Weak lower semicontinuity of the exact shifted limiting form, proved directly from positivity
of its Riesz operator and weak convergence. -/
theorem suzukiLimitingLogShiftedEnergy_le_of_weak_limit_uniform_bound
    (u : ℕ → CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hweak : ∀ y, Tendsto (fun n => inner ℂ (u n) y) atTop
      (nhds (inner ℂ w y)))
    (C : ℝ) (hC : ∀ n, suzukiLimitingLogShiftedEnergy (u n) ≤ C) :
    suzukiLimitingLogShiftedEnergy w ≤ C := by
  let R := boundedPerturbedFormRiesz suzukiLimitingLogFormEmbedding
    suzukiLimitingLogBoundedRemainder
  have hRself : IsSelfAdjoint R :=
    boundedPerturbedFormRiesz_isSelfAdjoint
      suzukiLimitingLogFormEmbedding suzukiLimitingLogBoundedRemainder
        suzukiLimitingLogBoundedRemainder_isSelfAdjoint
  let d : ℕ → CCMArchimedeanFormDomain suzukiLimitingUnitAperture :=
    fun n => u n - w
  have hdweak : Tendsto (fun n => inner ℂ (d n) (R w)) atTop (nhds 0) := by
    have hsub := (hweak (R w)).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℂ w (R w)) atTop
        (nhds (inner ℂ w (R w))))
    simpa only [d, inner_sub_left, sub_self] using hsub
  have hcross : Tendsto (fun n => (inner ℂ (d n) (R w)).re) atTop (nhds 0) := by
    have h := (Complex.continuous_re.tendsto 0).comp hdweak
    change Tendsto (Complex.re ∘ fun n => inner ℂ (d n) (R w)) atTop (nhds 0)
    simpa only [Complex.zero_re] using h
  have hexpand (n : ℕ) :
      (inner ℂ (R (u n)) (u n)).re =
        (inner ℂ (R w) w).re + (inner ℂ (R (d n)) (d n)).re +
          2 * (inner ℂ (d n) (R w)).re := by
    have hud : u n = w + d n := by
      dsimp only [d]
      abel
    have hsymm : inner ℂ (R (d n)) w = inner ℂ (d n) (R w) :=
      hRself.isSymmetric (d n) w
    have hconj : (inner ℂ (R w) (d n)).re =
        (inner ℂ (d n) (R w)).re := by
      calc
        (inner ℂ (R w) (d n)).re =
            ((starRingEnd ℂ) (inner ℂ (R w) (d n))).re :=
          (Complex.conj_re _).symm
        _ = (inner ℂ (d n) (R w)).re := by
          exact congrArg Complex.re
            (inner_conj_symm (𝕜 := ℂ) (d n) (R w))
    rw [hud, map_add, inner_add_left, inner_add_right, inner_add_right,
      Complex.add_re, Complex.add_re, Complex.add_re, hsymm, hconj]
    ring
  have hnonneg (n : ℕ) : 0 ≤ (inner ℂ (R (d n)) (d n)).re := by
    exact (sq_nonneg ‖d n‖).trans
      (boundedPerturbedFormRiesz_coercive
        suzukiLimitingLogFormEmbedding suzukiLimitingLogBoundedRemainder (d n))
  have hpoint (n : ℕ) :
      (inner ℂ (R w) w).re + 2 * (inner ℂ (d n) (R w)).re ≤ C := by
    have huC : (inner ℂ (R (u n)) (u n)).re ≤ C := by
      rw [← suzukiLimitingLogShiftedEnergy_eq_riesz]
      exact hC n
    rw [hexpand] at huC
    linarith [hnonneg n]
  have hlim : Tendsto (fun n =>
      (inner ℂ (R w) w).re + 2 * (inner ℂ (d n) (R w)).re)
      atTop (nhds ((inner ℂ (R w) w).re)) := by
    simpa using tendsto_const_nhds.add (hcross.const_mul 2)
  have := le_of_tendsto' hlim hpoint
  rwa [← suzukiLimitingLogShiftedEnergy_eq_riesz] at this

def suzukiCoreShiftedEnergy
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) : ℝ :=
  suzukiFinitePartEnergy 1 u +
    boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
      (∫ x in (-1 : ℝ)..1, u x ^ 2)

theorem suzukiLimitingLogShiftedEnergy_smoothAbsoluteCoreFormVector_le
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) (n : ℕ) :
    suzukiLimitingLogShiftedEnergy (suzukiSmoothAbsoluteCoreFormVector u n) ≤
      suzukiCoreShiftedEnergy u := by
  let ε := suzukiSmoothAbsoluteScale n
  have hε : 0 < ε := suzukiSmoothAbsoluteScale_pos n
  let v := suzukiSmoothAbsoluteCore u ε hε
  have hform : (suzukiLimitingLogClosedForm
      (suzukiSmoothAbsoluteCoreFormVector u n)
      (suzukiSmoothAbsoluteCoreFormVector u n)).re =
      suzukiFinitePartEnergy 1 v := by
    change (suzukiLimitingLogClosedForm
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v)
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v)).re = _
    rw [suzukiLimitingLogClosedForm_core_eq_weilFinitePartBlock,
      Complex.ofReal_re]
    simpa only [suzukiLimitingUnitAperture] using
      (suzukiWeilFinitePartBlock_eq_energy suzukiLimitingUnitAperture v)
  have hmass : ‖suzukiLimitingLogFormEmbedding
      (suzukiSmoothAbsoluteCoreFormVector u n)‖ ^ 2 =
      ∫ x in (-1 : ℝ)..1, v x ^ 2 := by
    change ‖suzukiLimitingLogFormEmbedding
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v)‖ ^ 2 = _
    exact norm_sq_suzukiLimitingLogFormEmbedding_coreFormVector v
  have henergy := suzukiFinitePartEnergy_smoothAbsolute_le u ε hε
  have hmassle := suzukiSmoothAbsoluteCore_mass_le u ε hε
  have hshift : 0 ≤ boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder :=
    (boundedPerturbedFormShift_pos suzukiLimitingLogBoundedRemainder).le
  unfold suzukiLimitingLogShiftedEnergy suzukiCoreShiftedEnergy
  rw [hform, hmass]
  exact add_le_add henergy (mul_le_mul_of_nonneg_left hmassle hshift)

theorem suzukiCoreShiftedEnergy_nonneg
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    0 ≤ suzukiCoreShiftedEnergy u := by
  exact (sq_nonneg ‖suzukiSmoothAbsoluteCoreFormVector u 0‖).trans (by
    simpa only [suzukiCoreShiftedEnergy] using
      norm_sq_suzukiSmoothAbsoluteCoreFormVector_le u 0)

theorem norm_suzukiSmoothAbsoluteCoreFormVector_le_sqrt
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) (n : ℕ) :
    ‖suzukiSmoothAbsoluteCoreFormVector u n‖ ≤
      Real.sqrt (suzukiCoreShiftedEnergy u) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (suzukiCoreShiftedEnergy_nonneg u)]
  simpa only [suzukiCoreShiftedEnergy] using
    norm_sq_suzukiSmoothAbsoluteCoreFormVector_le u n

theorem norm_suzukiCoreAbsoluteIntervalVector_eq_coreIntervalVector
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    ‖suzukiCoreAbsoluteIntervalVector u‖ =
      ‖suzukiLimitingCoreIntervalVector u‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [suzukiCoreAbsoluteIntervalVector_coeFn u,
    suzukiLimitingCoreIntervalVector_coeFn u] with x habs hcore
  rw [habs, hcore]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_abs]

theorem norm_sq_suzukiCoreAbsoluteIntervalVector
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    ‖suzukiCoreAbsoluteIntervalVector u‖ ^ 2 =
      ∫ x in (-1 : ℝ)..1, u x ^ 2 := by
  rw [norm_suzukiCoreAbsoluteIntervalVector_eq_coreIntervalVector,
    suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
  exact norm_sq_suzukiLimitingLogFormEmbedding_coreFormVector u

/-- Closed-domain modulus theorem for every literal real Suzuki source-core vector. The modulus
is produced inside the complete CCM form domain, not assumed to have logarithmic regularity. -/
theorem exists_suzukiCoreAbsoluteFormVector
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    ∃ w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      suzukiLimitingLogFormEmbedding w = suzukiCoreAbsoluteIntervalVector u ∧
      (suzukiLimitingLogClosedForm w w).re ≤ suzukiFinitePartEnergy 1 u := by
  let q : ℕ → CCMArchimedeanFormDomain suzukiLimitingUnitAperture :=
    fun n => suzukiSmoothAbsoluteCoreFormVector u n
  let M := Real.sqrt (suzukiCoreShiftedEnergy u)
  obtain ⟨w, φ, hφ, _hwM, hweak, hcompact⟩ :=
    exists_suzukiLimitingLogForm_weakSubseq q M
      (norm_suzukiSmoothAbsoluteCoreFormVector_le_sqrt u)
  have hphysicalW : Tendsto (fun n => suzukiLimitingLogFormEmbedding (q (φ n)))
      atTop (nhds (suzukiLimitingLogFormEmbedding w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact hcompact
  have hphysicalAbs : Tendsto
      (fun n => suzukiLimitingLogFormEmbedding (q (φ n))) atTop
      (nhds (suzukiCoreAbsoluteIntervalVector u)) := by
    exact (tendsto_suzukiLimitingLogFormEmbedding_smoothAbsoluteCoreFormVector u).comp
      hφ.tendsto_atTop
  have hrep : suzukiLimitingLogFormEmbedding w =
      suzukiCoreAbsoluteIntervalVector u :=
    tendsto_nhds_unique hphysicalW hphysicalAbs
  have hshifted : suzukiLimitingLogShiftedEnergy w ≤ suzukiCoreShiftedEnergy u := by
    apply suzukiLimitingLogShiftedEnergy_le_of_weak_limit_uniform_bound
      (fun n => q (φ n)) w hweak
    intro n
    exact suzukiLimitingLogShiftedEnergy_smoothAbsoluteCoreFormVector_le u (φ n)
  refine ⟨w, hrep, ?_⟩
  unfold suzukiLimitingLogShiftedEnergy suzukiCoreShiftedEnergy at hshifted
  rw [hrep, norm_sq_suzukiCoreAbsoluteIntervalVector] at hshifted
  linarith

theorem inner_suzukiLimitingIntervalPolarOperator_realCore_mixed_im_eq_zero
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    (inner ℂ
      (suzukiLimitingIntervalPolarOperator
        (suzukiLimitingCoreIntervalVector u))
      (suzukiLimitingCoreIntervalVector v)).im = 0 := by
  let a := suzukiLimitingUnitAperture
  let qu := suzukiRestrictedWeilCoreCCMFormVector a u
  let qv := suzukiRestrictedWeilCoreCCMFormVector a v
  let f := ccmArchimedeanFormToAperture a qu
  let g := ccmArchimedeanFormToAperture a qv
  let e := suzukiApertureL2Equiv a
  have hfu : suzukiLimitingCoreIntervalVector u = e.symm f :=
    suzukiLimitingCoreIntervalVector_eq_formEmbedding u
  have hfv : suzukiLimitingCoreIntervalVector v = e.symm g :=
    suzukiLimitingCoreIntervalVector_eq_formEmbedding v
  rw [hfu, hfv]
  change (inner ℂ (e.symm (ccmPolarOperator a (e (e.symm f)))) (e.symm g)).im = 0
  rw [e.apply_symm_apply, e.symm.inner_map_map, inner_ccmPolarOperator_mixed]
  dsimp only [f, g, qu, qv]
  simp_rw [inner_ccmPolarApertureVector_suzukiRestrictedWeilCoreCCMFormVector_eq_ofReal]
  simp

theorem inner_suzukiLimitingLogBoundedRemainder_realCore_mixed_im_eq_zero
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    (inner ℂ
      (suzukiLimitingLogBoundedRemainder
        (suzukiLimitingCoreIntervalVector u))
      (suzukiLimitingCoreIntervalVector v)).im = 0 := by
  have hmass := inner_suzukiLimitingCoreIntervalVector_mixed_im_eq_zero u v
  have hpolar :=
    inner_suzukiLimitingIntervalPolarOperator_realCore_mixed_im_eq_zero u v
  have horigin :=
    inner_suzukiLimitingOriginKernelOperator_realCore_mixed_im_eq_zero u v
  unfold suzukiLimitingLogBoundedRemainder
  rw [add_apply, add_apply, smul_apply, one_apply_eq_self,
    inner_add_left, inner_add_left, inner_smul_left, star_suzukiLimitingScalar]
  simp only [Complex.add_im, Complex.mul_im]
  have hscalarIm : suzukiLimitingScalar.im = 0 := by
    have hstar := star_suzukiLimitingScalar
    exact Complex.conj_eq_iff_im.mp hstar
  rw [hscalarIm, zero_mul, add_zero, hmass, mul_zero, hpolar, horigin]
  ring

/-- Native CCM form-domain inner products of real Suzuki core vectors are real. This identifies
the canonical real Hilbert structure underlying the complex closed form. -/
theorem inner_suzukiRestrictedWeilCoreCCMFormVector_im_eq_zero
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    (inner ℂ
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v)).im = 0 := by
  have hclosed := suzukiLimitingLogClosedForm_realCore_mixed_im_eq_zero u v
  have hB := inner_suzukiLimitingLogBoundedRemainder_realCore_mixed_im_eq_zero u v
  unfold suzukiLimitingLogClosedForm at hclosed
  rw [← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding u,
    ← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding v] at hclosed
  rw [Complex.add_im, hB, add_zero] at hclosed
  exact hclosed

def suzukiLimitingRealTestFormVector
    (u : SuzukiRestrictedWeilRealTest 1) :
    CCMArchimedeanFormDomain suzukiLimitingUnitAperture :=
  suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture
    (suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture u)

theorem suzukiLimitingLogFormEmbedding_realTestFormVector_coeFn
    (u : SuzukiRestrictedWeilRealTest 1) :
    (suzukiLimitingLogFormEmbedding (suzukiLimitingRealTestFormVector u) :
      SuzukiApertureInterval 1 → ℂ) =ᵐ[volume]
        fun x => ((u (x : ℝ) : ℝ) : ℂ) := by
  unfold suzukiLimitingRealTestFormVector
  rw [← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
  exact suzukiLimitingCoreIntervalVector_coeFn
    (suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture u)

def suzukiLimitingRealTestFormLinearMap :
    SuzukiRestrictedWeilRealTest 1 →ₗ[ℝ]
      CCMArchimedeanFormDomain suzukiLimitingUnitAperture where
  toFun := suzukiLimitingRealTestFormVector
  map_add' u v := by
    apply suzukiLimitingLogFormEmbedding_injective
    rw [map_add]
    apply MeasureTheory.Lp.ext
    filter_upwards [
      suzukiLimitingLogFormEmbedding_realTestFormVector_coeFn (u + v),
      suzukiLimitingLogFormEmbedding_realTestFormVector_coeFn u,
      suzukiLimitingLogFormEmbedding_realTestFormVector_coeFn v,
      MeasureTheory.Lp.coeFn_add
        (suzukiLimitingLogFormEmbedding (suzukiLimitingRealTestFormVector u))
        (suzukiLimitingLogFormEmbedding (suzukiLimitingRealTestFormVector v))]
      with x huv hu hv hadd
    rw [huv, hadd, Pi.add_apply, hu, hv]
    change (((u (x : ℝ) + v (x : ℝ) : ℝ) : ℂ)) =
      (u (x : ℝ) : ℂ) + (v (x : ℝ) : ℂ)
    push_cast
    rfl
  map_smul' c u := by
    apply suzukiLimitingLogFormEmbedding_injective
    change suzukiLimitingLogFormEmbedding (suzukiLimitingRealTestFormVector (c • u)) =
      suzukiLimitingLogFormEmbedding
        ((c : ℂ) • suzukiLimitingRealTestFormVector u)
    rw [map_smul]
    apply MeasureTheory.Lp.ext
    filter_upwards [
      suzukiLimitingLogFormEmbedding_realTestFormVector_coeFn (c • u),
      suzukiLimitingLogFormEmbedding_realTestFormVector_coeFn u,
      MeasureTheory.Lp.coeFn_smul (c : ℂ)
        (suzukiLimitingLogFormEmbedding (suzukiLimitingRealTestFormVector u))]
      with x hcu hu hsmul
    rw [hcu, hsmul, Pi.smul_apply, hu]
    change (((c * u (x : ℝ) : ℝ) : ℂ)) =
      (c : ℂ) • (u (x : ℝ) : ℂ)
    push_cast
    simp [smul_eq_mul]

def suzukiLimitingRealCoreSubmodule :
    Submodule ℝ (CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :=
  LinearMap.range suzukiLimitingRealTestFormLinearMap

/-- Closed real form domain generated by Suzuki's literal real test core. -/
def SuzukiLimitingRealFormDomain :
    Submodule ℝ (CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :=
  suzukiLimitingRealCoreSubmodule.topologicalClosure

theorem isClosed_suzukiLimitingRealFormDomain :
    IsClosed (SuzukiLimitingRealFormDomain :
      Set (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)) :=
  Submodule.isClosed_topologicalClosure _

def suzukiInnerImaginaryRightKernel
    (y : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    Submodule ℝ (CCMArchimedeanFormDomain suzukiLimitingUnitAperture) where
  carrier := {x | (inner ℂ x y).im = 0}
  zero_mem' := by simp
  add_mem' {x z} hx hz := by
    rw [Set.mem_setOf_eq, inner_add_left, Complex.add_im, hx, hz, add_zero]
  smul_mem' c x hx := by
    rw [Set.mem_setOf_eq]
    change (inner ℂ x y).im = 0 at hx
    change (inner ℂ ((c : ℂ) • x) y).im = 0
    rw [inner_smul_left x y (c : ℂ), Complex.conj_ofReal]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    exact mul_eq_zero.mpr (Or.inr hx)

theorem isClosed_suzukiInnerImaginaryRightKernel
    (y : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    IsClosed (suzukiInnerImaginaryRightKernel y :
      Set (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)) := by
  apply isClosed_eq
  · exact Complex.continuous_im.comp
      ((continuous_id : Continuous (fun x :
        CCMArchimedeanFormDomain suzukiLimitingUnitAperture => x)).inner
          (𝕜 := ℂ) continuous_const)
  · exact continuous_const

def suzukiInnerImaginaryLeftKernel
    (x : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    Submodule ℝ (CCMArchimedeanFormDomain suzukiLimitingUnitAperture) where
  carrier := {y | (inner ℂ x y).im = 0}
  zero_mem' := by simp
  add_mem' {y z} hy hz := by
    rw [Set.mem_setOf_eq, inner_add_right, Complex.add_im, hy, hz, add_zero]
  smul_mem' c y hy := by
    rw [Set.mem_setOf_eq]
    change (inner ℂ x y).im = 0 at hy
    change (inner ℂ x ((c : ℂ) • y)).im = 0
    rw [inner_smul_right x y (c : ℂ)]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    exact mul_eq_zero.mpr (Or.inr hy)

theorem isClosed_suzukiInnerImaginaryLeftKernel
    (x : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    IsClosed (suzukiInnerImaginaryLeftKernel x :
      Set (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)) := by
  apply isClosed_eq
  · exact Complex.continuous_im.comp
      ((continuous_const : Continuous (fun _ :
        CCMArchimedeanFormDomain suzukiLimitingUnitAperture => x)).inner
          (𝕜 := ℂ) continuous_id)
  · exact continuous_const

theorem inner_im_eq_zero_of_mem_realCoreSubmodule
    {x y : CCMArchimedeanFormDomain suzukiLimitingUnitAperture}
    (hx : x ∈ suzukiLimitingRealCoreSubmodule)
    (hy : y ∈ suzukiLimitingRealCoreSubmodule) :
    (inner ℂ x y).im = 0 := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  exact inner_suzukiRestrictedWeilCoreCCMFormVector_im_eq_zero
    (suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture u)
    (suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture v)

theorem inner_im_eq_zero_of_mem_realFormDomain_right_core
    {x y : CCMArchimedeanFormDomain suzukiLimitingUnitAperture}
    (hx : x ∈ SuzukiLimitingRealFormDomain)
    (hy : y ∈ suzukiLimitingRealCoreSubmodule) :
    (inner ℂ x y).im = 0 := by
  have hle : suzukiLimitingRealCoreSubmodule ≤
      suzukiInnerImaginaryRightKernel y := by
    intro z hz
    exact inner_im_eq_zero_of_mem_realCoreSubmodule hz hy
  exact Submodule.topologicalClosure_minimal _ hle
    (isClosed_suzukiInnerImaginaryRightKernel y) hx

/-- The complete limiting form domain generated by real tests carries a genuine real Hilbert
structure: every native complex inner product of two real-domain vectors is real. -/
theorem inner_im_eq_zero_of_mem_suzukiLimitingRealFormDomain
    {x y : CCMArchimedeanFormDomain suzukiLimitingUnitAperture}
    (hx : x ∈ SuzukiLimitingRealFormDomain)
    (hy : y ∈ SuzukiLimitingRealFormDomain) :
    (inner ℂ x y).im = 0 := by
  have hle : suzukiLimitingRealCoreSubmodule ≤
      suzukiInnerImaginaryLeftKernel x := by
    intro z hz
    exact inner_im_eq_zero_of_mem_realFormDomain_right_core hx hz
  exact Submodule.topologicalClosure_minimal _ hle
    (isClosed_suzukiInnerImaginaryLeftKernel x) hy

end RHTower

namespace RHTower

open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiLimitingLogClosedMarkovLocalInst3 : SFinite ccmArchimedeanFormMeasure := by
  unfold ccmArchimedeanFormMeasure
  infer_instance

local instance suzukiLimitingLogClosedMarkovLocalInst4 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

private local instance suzukiFormDomainRealInnerProduct :
    InnerProductSpace ℝ
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :=
  InnerProductSpace.complexToReal

/-- A complex-weak limit of vectors in a real linear subspace belongs to its norm closure. -/
theorem mem_topologicalClosure_of_complexWeak_limit
    (K : Submodule ℝ
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture))
    (u : ℕ → CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hu : ∀ n, u n ∈ K)
    (hweak : ∀ y, Tendsto (fun n => inner ℂ (u n) y) atTop
      (nhds (inner ℂ w y))) :
    w ∈ K.topologicalClosure := by
  let L := K.topologicalClosure
  let p : CCMArchimedeanFormDomain suzukiLimitingUnitAperture :=
    L.starProjection w
  let d : CCMArchimedeanFormDomain suzukiLimitingUnitAperture := w - p
  have hp : p ∈ L := L.starProjection_apply_mem w
  have hd : d ∈ Lᗮ := L.sub_starProjection_mem_orthogonal w
  have hd' := (Submodule.mem_orthogonal' L d).mp hd
  have hzero (n : ℕ) : inner ℝ (u n) d = 0 := by
    rw [real_inner_comm]
    exact hd' (u n) (K.le_topologicalClosure (hu n))
  have hseq : Tendsto (fun n => inner ℝ (u n) d) atTop
      (nhds (inner ℝ w d)) := by
    change Tendsto (fun n => (inner ℂ (u n) d).re) atTop
      (nhds ((inner ℂ w d).re))
    exact (Complex.continuous_re.tendsto _).comp (hweak d)
  have hconst : Tendsto (fun n => inner ℝ (u n) d) atTop (nhds 0) := by
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hwd : inner ℝ w d = 0 := tendsto_nhds_unique hseq hconst
  have hpd : inner ℝ p d = 0 := by
    rw [real_inner_comm]
    exact hd' p hp
  have hdecomp : w = p + d := by
    dsimp only [d]
    abel
  have hdd : inner ℝ d d = 0 := by
    rw [hdecomp, inner_add_left, hpd, zero_add] at hwd
    exact hwd
  have hd0 : d = 0 := inner_self_eq_zero.mp hdd
  have hwp : w = p := by
    dsimp only [d] at hd0
    exact sub_eq_zero.mp hd0
  rw [hwp]
  exact hp

/-- Every literal smooth core is canonically a Mathlib test function on the open aperture. -/
def suzukiRestrictedWeilCoreToRealTest
    (a : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) :
    SuzukiRestrictedWeilRealTest a.1 where
  toFun := u
  contDiff' := u.smooth
  hasCompactSupport' := u.hasCompactSupport
  tsupport_subset' := by
    refine (closure_minimal u.support_subset isClosed_Icc).trans ?_
    intro x hx
    constructor <;> linarith [hx.1, hx.2, u.supportRadius_lt_aperture]

@[simp] theorem suzukiRestrictedWeilCoreToRealTest_apply
    (a : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) (x : ℝ) :
    suzukiRestrictedWeilCoreToRealTest a u x = u x := rfl

/-- The complete-form vector of every literal real source core lies in the canonical real core
submodule, including smooth contraction approximants constructed outside `TestFunction`. -/
theorem suzukiRestrictedWeilCoreCCMFormVector_mem_realCoreSubmodule
    (u : SuzukiRestrictedWeilCore 1) :
    suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u ∈
      suzukiLimitingRealCoreSubmodule := by
  change ∃ t : SuzukiRestrictedWeilRealTest 1,
    suzukiLimitingRealTestFormLinearMap t =
      suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u
  refine ⟨suzukiRestrictedWeilCoreToRealTest suzukiLimitingUnitAperture u, ?_⟩
  apply suzukiLimitingLogFormEmbedding_injective
  apply MeasureTheory.Lp.ext
  filter_upwards [
    suzukiLimitingLogFormEmbedding_realTestFormVector_coeFn
      (suzukiRestrictedWeilCoreToRealTest suzukiLimitingUnitAperture u),
    suzukiLimitingCoreIntervalVector_coeFn u] with x htest hcore
  change (suzukiLimitingLogFormEmbedding
    (suzukiLimitingRealTestFormVector
      (suzukiRestrictedWeilCoreToRealTest suzukiLimitingUnitAperture u))) x =
    (suzukiLimitingLogFormEmbedding
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)) x
  rw [htest]
  rw [← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding u, hcore]
  rfl

/-- Literal pointwise modulus on the physical interval `L²` space. -/
def suzukiIntervalL2Modulus (f : SuzukiApertureIntervalL2 1) :
    SuzukiApertureIntervalL2 1 :=
  ((MeasureTheory.Lp.memLp f).norm.ofReal (K := ℂ)).toLp
    (fun x => ((‖f x‖ : ℝ) : ℂ))

theorem suzukiIntervalL2Modulus_coeFn (f : SuzukiApertureIntervalL2 1) :
    (suzukiIntervalL2Modulus f : SuzukiApertureInterval 1 → ℂ) =ᵐ[volume]
      fun x => ((‖f x‖ : ℝ) : ℂ) := by
  exact ((MeasureTheory.Lp.memLp f).norm.ofReal (K := ℂ)).coeFn_toLp

theorem norm_suzukiIntervalL2Modulus (f : SuzukiApertureIntervalL2 1) :
    ‖suzukiIntervalL2Modulus f‖ = ‖f‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [suzukiIntervalL2Modulus_coeFn f] with x hmod
  rw [hmod]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]

/-- Pointwise modulus is a genuine contraction on Suzuki's physical interval `L²`. -/
theorem norm_suzukiIntervalL2Modulus_sub_le
    (f g : SuzukiApertureIntervalL2 1) :
    ‖suzukiIntervalL2Modulus f - suzukiIntervalL2Modulus g‖ ≤ ‖f - g‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  apply ENNReal.toReal_mono (MeasureTheory.Lp.eLpNorm_ne_top (f - g))
  apply eLpNorm_mono_ae
  filter_upwards [
    suzukiIntervalL2Modulus_coeFn f,
    suzukiIntervalL2Modulus_coeFn g,
    MeasureTheory.Lp.coeFn_sub (suzukiIntervalL2Modulus f)
      (suzukiIntervalL2Modulus g),
    MeasureTheory.Lp.coeFn_sub f g] with x hf hg hmodsub hfgsub
  rw [hmodsub, hfgsub, Pi.sub_apply, Pi.sub_apply, hf, hg]
  rw [← Complex.ofReal_sub]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    (abs_norm_sub_norm_le (f x) (g x))

theorem lipschitzWith_suzukiIntervalL2Modulus :
    LipschitzWith 1 suzukiIntervalL2Modulus := by
  apply LipschitzWith.mk_one
  intro f g
  simpa only [dist_eq_norm] using norm_suzukiIntervalL2Modulus_sub_le f g

theorem continuous_suzukiIntervalL2Modulus :
    Continuous suzukiIntervalL2Modulus :=
  lipschitzWith_suzukiIntervalL2Modulus.continuous

theorem suzukiCoreAbsoluteIntervalVector_eq_modulus
    (u : SuzukiRestrictedWeilCore 1) :
    suzukiCoreAbsoluteIntervalVector u =
      suzukiIntervalL2Modulus (suzukiLimitingCoreIntervalVector u) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [suzukiCoreAbsoluteIntervalVector_coeFn u,
    suzukiIntervalL2Modulus_coeFn (suzukiLimitingCoreIntervalVector u),
    suzukiLimitingCoreIntervalVector_coeFn u] with x habs hmod hcore
  rw [habs, hmod, hcore]
  simp only [Complex.norm_real, Real.norm_eq_abs]

theorem suzukiLimitingLogShiftedEnergy_coreFormVector_eq_coreShiftedEnergy
    (u : SuzukiRestrictedWeilCore 1) :
    suzukiLimitingLogShiftedEnergy
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u) =
        suzukiCoreShiftedEnergy u := by
  unfold suzukiLimitingLogShiftedEnergy suzukiCoreShiftedEnergy
  rw [suzukiLimitingLogClosedForm_core_eq_weilFinitePartBlock,
    Complex.ofReal_re,
    norm_sq_suzukiLimitingLogFormEmbedding_coreFormVector]
  congr 1
  simpa only [suzukiLimitingUnitAperture] using
    suzukiWeilFinitePartBlock_eq_energy suzukiLimitingUnitAperture u

/-- Core modulus theorem strengthened with membership in Suzuki's canonical closed real form
domain and with the exact shifted-energy contraction needed for closure. -/
theorem exists_suzukiCoreModulusRealFormVector
    (u : SuzukiRestrictedWeilCore 1) :
    ∃ w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      w ∈ SuzukiLimitingRealFormDomain ∧
      suzukiLimitingLogFormEmbedding w =
        suzukiIntervalL2Modulus (suzukiLimitingCoreIntervalVector u) ∧
      suzukiLimitingLogShiftedEnergy w ≤
        suzukiLimitingLogShiftedEnergy
          (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u) := by
  let q : ℕ → CCMArchimedeanFormDomain suzukiLimitingUnitAperture :=
    fun n => suzukiSmoothAbsoluteCoreFormVector u n
  let M := Real.sqrt (suzukiCoreShiftedEnergy u)
  obtain ⟨w, φ, hφ, _hwM, hweak, hcompact⟩ :=
    exists_suzukiLimitingLogForm_weakSubseq q M
      (norm_suzukiSmoothAbsoluteCoreFormVector_le_sqrt u)
  have hqmem (n : ℕ) : q n ∈ suzukiLimitingRealCoreSubmodule := by
    exact suzukiRestrictedWeilCoreCCMFormVector_mem_realCoreSubmodule
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n))
  have hwreal : w ∈ SuzukiLimitingRealFormDomain := by
    exact mem_topologicalClosure_of_complexWeak_limit
      suzukiLimitingRealCoreSubmodule (fun n => q (φ n)) w
        (fun n => hqmem (φ n)) hweak
  have hphysicalW : Tendsto (fun n => suzukiLimitingLogFormEmbedding (q (φ n)))
      atTop (nhds (suzukiLimitingLogFormEmbedding w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact hcompact
  have hphysicalAbs : Tendsto
      (fun n => suzukiLimitingLogFormEmbedding (q (φ n))) atTop
      (nhds (suzukiCoreAbsoluteIntervalVector u)) := by
    exact (tendsto_suzukiLimitingLogFormEmbedding_smoothAbsoluteCoreFormVector u).comp
      hφ.tendsto_atTop
  have hrepAbs : suzukiLimitingLogFormEmbedding w =
      suzukiCoreAbsoluteIntervalVector u :=
    tendsto_nhds_unique hphysicalW hphysicalAbs
  have hshifted : suzukiLimitingLogShiftedEnergy w ≤ suzukiCoreShiftedEnergy u := by
    apply suzukiLimitingLogShiftedEnergy_le_of_weak_limit_uniform_bound
      (fun n => q (φ n)) w hweak
    intro n
    exact suzukiLimitingLogShiftedEnergy_smoothAbsoluteCoreFormVector_le u (φ n)
  refine ⟨w, hwreal, ?_, ?_⟩
  · rw [hrepAbs, suzukiCoreAbsoluteIntervalVector_eq_modulus]
  · calc
      suzukiLimitingLogShiftedEnergy w ≤ suzukiCoreShiftedEnergy u := hshifted
      _ = suzukiLimitingLogShiftedEnergy
          (suzukiRestrictedWeilCoreCCMFormVector
            suzukiLimitingUnitAperture u) :=
        (suzukiLimitingLogShiftedEnergy_coreFormVector_eq_coreShiftedEnergy u).symm

/-- Weak lower semicontinuity with a convergent moving upper bound. This retains the exact
energy of the strong approximating sequence instead of replacing it by a coarse constant. -/
theorem suzukiLimitingLogShiftedEnergy_le_of_weak_limit_upper_tendsto
    (u : ℕ → CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hweak : ∀ y, Tendsto (fun n => inner ℂ (u n) y) atTop
      (nhds (inner ℂ w y)))
    (b : ℕ → ℝ) (B : ℝ) (hb : Tendsto b atTop (nhds B))
    (hupper : ∀ n, suzukiLimitingLogShiftedEnergy (u n) ≤ b n) :
    suzukiLimitingLogShiftedEnergy w ≤ B := by
  let R := boundedPerturbedFormRiesz suzukiLimitingLogFormEmbedding
    suzukiLimitingLogBoundedRemainder
  have hRself : IsSelfAdjoint R :=
    boundedPerturbedFormRiesz_isSelfAdjoint
      suzukiLimitingLogFormEmbedding suzukiLimitingLogBoundedRemainder
        suzukiLimitingLogBoundedRemainder_isSelfAdjoint
  let d : ℕ → CCMArchimedeanFormDomain suzukiLimitingUnitAperture :=
    fun n => u n - w
  have hdweak : Tendsto (fun n => inner ℂ (d n) (R w)) atTop (nhds 0) := by
    have hsub := (hweak (R w)).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℂ w (R w)) atTop
        (nhds (inner ℂ w (R w))))
    simpa only [d, inner_sub_left, sub_self] using hsub
  have hcross : Tendsto (fun n => (inner ℂ (d n) (R w)).re) atTop (nhds 0) := by
    have h := (Complex.continuous_re.tendsto 0).comp hdweak
    change Tendsto (Complex.re ∘ fun n => inner ℂ (d n) (R w)) atTop (nhds 0)
    simpa only [Complex.zero_re] using h
  have hexpand (n : ℕ) :
      (inner ℂ (R (u n)) (u n)).re =
        (inner ℂ (R w) w).re + (inner ℂ (R (d n)) (d n)).re +
          2 * (inner ℂ (d n) (R w)).re := by
    have hud : u n = w + d n := by
      dsimp only [d]
      abel
    have hsymm : inner ℂ (R (d n)) w = inner ℂ (d n) (R w) :=
      hRself.isSymmetric (d n) w
    have hconj : (inner ℂ (R w) (d n)).re =
        (inner ℂ (d n) (R w)).re := by
      calc
        (inner ℂ (R w) (d n)).re =
            ((starRingEnd ℂ) (inner ℂ (R w) (d n))).re :=
          (Complex.conj_re _).symm
        _ = (inner ℂ (d n) (R w)).re := by
          exact congrArg Complex.re
            (inner_conj_symm (𝕜 := ℂ) (d n) (R w))
    rw [hud, map_add, inner_add_left, inner_add_right, inner_add_right,
      Complex.add_re, Complex.add_re, Complex.add_re, hsymm, hconj]
    ring
  have hnonneg (n : ℕ) : 0 ≤ (inner ℂ (R (d n)) (d n)).re := by
    exact (sq_nonneg ‖d n‖).trans
      (boundedPerturbedFormRiesz_coercive
        suzukiLimitingLogFormEmbedding suzukiLimitingLogBoundedRemainder (d n))
  have hpoint (n : ℕ) :
      (inner ℂ (R w) w).re + 2 * (inner ℂ (d n) (R w)).re ≤ b n := by
    have huB : (inner ℂ (R (u n)) (u n)).re ≤ b n := by
      rw [← suzukiLimitingLogShiftedEnergy_eq_riesz]
      exact hupper n
    rw [hexpand] at huB
    linarith [hnonneg n]
  have hleft : Tendsto (fun n =>
      (inner ℂ (R w) w).re + 2 * (inner ℂ (d n) (R w)).re)
      atTop (nhds ((inner ℂ (R w) w).re)) := by
    simpa using tendsto_const_nhds.add (hcross.const_mul 2)
  have hlimit : (inner ℂ (R w) w).re ≤ B :=
    le_of_tendsto_of_tendsto' hleft hb hpoint
  rwa [← suzukiLimitingLogShiftedEnergy_eq_riesz] at hlimit

theorem continuous_suzukiLimitingLogShiftedEnergy :
    Continuous suzukiLimitingLogShiftedEnergy := by
  let R := boundedPerturbedFormRiesz suzukiLimitingLogFormEmbedding
    suzukiLimitingLogBoundedRemainder
  have hfun : suzukiLimitingLogShiftedEnergy =
      fun q => (inner ℂ (R q) q).re := by
    funext q
    exact suzukiLimitingLogShiftedEnergy_eq_riesz q
  rw [hfun]
  exact Complex.continuous_re.comp
    (R.continuous.inner (𝕜 := ℂ) continuous_id)

/-- Exact closed-domain modulus contraction for Suzuki's canonical real form domain. No
regularity of the pointwise modulus is assumed: it is obtained by smooth core approximation,
weak compactness in the form norm, compact physical embedding, and sharp moving-bound lower
semicontinuity. -/
theorem exists_suzukiRealFormDomainModulus
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain) :
    ∃ w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      w ∈ SuzukiLimitingRealFormDomain ∧
      suzukiLimitingLogFormEmbedding w =
        suzukiIntervalL2Modulus (suzukiLimitingLogFormEmbedding q) ∧
      suzukiLimitingLogShiftedEnergy w ≤ suzukiLimitingLogShiftedEnergy q := by
  change q ∈ closure
    (suzukiLimitingRealCoreSubmodule : Set
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)) at hq
  obtain ⟨z, hzcore, hzlim⟩ := mem_closure_iff_seq_limit.mp hq
  have htests (n : ℕ) : ∃ t : SuzukiRestrictedWeilRealTest 1,
      suzukiLimitingRealTestFormLinearMap t = z n := hzcore n
  choose t ht using htests
  let u : ℕ → SuzukiRestrictedWeilCore 1 := fun n =>
    suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture (t n)
  have hzform (n : ℕ) : z n =
      suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture (u n) := by
    rw [← ht n]
    rfl
  have hmodExists (n : ℕ) := exists_suzukiCoreModulusRealFormVector (u n)
  choose v hvreal hvrep hvenergy using hmodExists
  have hzenergy : Tendsto (fun n => suzukiLimitingLogShiftedEnergy (z n)) atTop
      (nhds (suzukiLimitingLogShiftedEnergy q)) :=
    (continuous_suzukiLimitingLogShiftedEnergy.tendsto q).comp hzlim
  have hzenergyBounded : Bornology.IsBounded
      (Set.range (fun n : ℕ => suzukiLimitingLogShiftedEnergy (z n)) : Set ℝ) :=
    Metric.isBounded_range_of_tendsto
      (fun n => suzukiLimitingLogShiftedEnergy (z n)) hzenergy
  obtain ⟨C, hCrange⟩ :=
    (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp hzenergyBounded
  have hCpos : 0 < C := by
    exact lt_of_le_of_lt dist_nonneg (hCrange ⟨0, rfl⟩)
  have hzenergy_le (n : ℕ) : suzukiLimitingLogShiftedEnergy (z n) ≤ C := by
    calc
      suzukiLimitingLogShiftedEnergy (z n) ≤
          |suzukiLimitingLogShiftedEnergy (z n)| := le_abs_self _
      _ = dist (suzukiLimitingLogShiftedEnergy (z n)) 0 := by
        rw [Real.dist_eq, sub_zero]
      _ ≤ C := (hCrange ⟨n, rfl⟩).le
  have hvenergy_z (n : ℕ) :
      suzukiLimitingLogShiftedEnergy (v n) ≤
        suzukiLimitingLogShiftedEnergy (z n) := by
    calc
      suzukiLimitingLogShiftedEnergy (v n) ≤
          suzukiLimitingLogShiftedEnergy
            (suzukiRestrictedWeilCoreCCMFormVector
              suzukiLimitingUnitAperture (u n)) := hvenergy n
      _ = suzukiLimitingLogShiftedEnergy (z n) := congrArg
        suzukiLimitingLogShiftedEnergy (hzform n).symm
  have hvnorm (n : ℕ) : ‖v n‖ ≤ Real.sqrt C := by
    have hcoer : ‖v n‖ ^ 2 ≤ suzukiLimitingLogShiftedEnergy (v n) := by
      have h := boundedPerturbedFormRiesz_coercive
        suzukiLimitingLogFormEmbedding suzukiLimitingLogBoundedRemainder (v n)
      rwa [← suzukiLimitingLogShiftedEnergy_eq_riesz] at h
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hCpos.le]
    exact hcoer.trans ((hvenergy_z n).trans (hzenergy_le n))
  obtain ⟨w, φ, hφ, _hwC, hweak, hcompact⟩ :=
    exists_suzukiLimitingLogForm_weakSubseq v (Real.sqrt C) hvnorm
  have hwrealClosure : w ∈ SuzukiLimitingRealFormDomain.topologicalClosure :=
    mem_topologicalClosure_of_complexWeak_limit SuzukiLimitingRealFormDomain
      (fun n => v (φ n)) w (fun n => hvreal (φ n)) hweak
  have hwreal : w ∈ SuzukiLimitingRealFormDomain := by
    rw [isClosed_suzukiLimitingRealFormDomain.submodule_topologicalClosure_eq]
      at hwrealClosure
    exact hwrealClosure
  have hphysicalW : Tendsto
      (fun n => suzukiLimitingLogFormEmbedding (v (φ n))) atTop
      (nhds (suzukiLimitingLogFormEmbedding w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact hcompact
  have hzsub : Tendsto (fun n => z (φ n)) atTop (nhds q) :=
    hzlim.comp hφ.tendsto_atTop
  have hzphysical : Tendsto
      (fun n => suzukiLimitingLogFormEmbedding (z (φ n))) atTop
      (nhds (suzukiLimitingLogFormEmbedding q)) :=
    (suzukiLimitingLogFormEmbedding.continuous.tendsto q).comp hzsub
  have hmodphysical : Tendsto
      (fun n => suzukiIntervalL2Modulus
        (suzukiLimitingLogFormEmbedding (z (φ n)))) atTop
      (nhds (suzukiIntervalL2Modulus
        (suzukiLimitingLogFormEmbedding q))) :=
    (continuous_suzukiIntervalL2Modulus.tendsto
      (suzukiLimitingLogFormEmbedding q)).comp hzphysical
  have hvphysical : Tendsto
      (fun n => suzukiLimitingLogFormEmbedding (v (φ n))) atTop
      (nhds (suzukiIntervalL2Modulus
        (suzukiLimitingLogFormEmbedding q))) := by
    convert hmodphysical using 1
    funext n
    rw [hvrep (φ n), hzform (φ n),
      suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
  have hrep : suzukiLimitingLogFormEmbedding w =
      suzukiIntervalL2Modulus (suzukiLimitingLogFormEmbedding q) :=
    tendsto_nhds_unique hphysicalW hvphysical
  have henergySub : Tendsto
      (fun n => suzukiLimitingLogShiftedEnergy (z (φ n))) atTop
      (nhds (suzukiLimitingLogShiftedEnergy q)) :=
    hzenergy.comp hφ.tendsto_atTop
  have hwenergy : suzukiLimitingLogShiftedEnergy w ≤
      suzukiLimitingLogShiftedEnergy q := by
    apply suzukiLimitingLogShiftedEnergy_le_of_weak_limit_upper_tendsto
      (fun n => v (φ n)) w hweak
      (fun n => suzukiLimitingLogShiftedEnergy (z (φ n)))
      (suzukiLimitingLogShiftedEnergy q) henergySub
    intro n
    exact hvenergy_z (φ n)
  exact ⟨w, hwreal, hrep, hwenergy⟩

/-- Exact unshifted closed-form modulus contraction. The shift cancels because physical modulus
preserves the `L²` norm. -/
theorem exists_suzukiRealFormDomainModulus_closedForm
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain) :
    ∃ w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      w ∈ SuzukiLimitingRealFormDomain ∧
      suzukiLimitingLogFormEmbedding w =
        suzukiIntervalL2Modulus (suzukiLimitingLogFormEmbedding q) ∧
      (suzukiLimitingLogClosedForm w w).re ≤
        (suzukiLimitingLogClosedForm q q).re := by
  obtain ⟨w, hwreal, hrep, hshift⟩ := exists_suzukiRealFormDomainModulus q hq
  refine ⟨w, hwreal, hrep, ?_⟩
  unfold suzukiLimitingLogShiftedEnergy at hshift
  rw [hrep, norm_suzukiIntervalL2Modulus] at hshift
  exact (add_le_add_iff_right
    (boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
      ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)).mp hshift

/-- Smooth approximation to the positive part, normalized to fix zero. -/
def suzukiSmoothPositive (ε x : ℝ) : ℝ :=
  (x + suzukiSmoothAbsolute ε x) / 2

@[simp] theorem suzukiSmoothPositive_zero {ε : ℝ} (hε : 0 ≤ ε) :
    suzukiSmoothPositive ε 0 = 0 := by
  simp [suzukiSmoothPositive, suzukiSmoothAbsolute_zero hε]

theorem contDiff_suzukiSmoothPositive {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiSmoothPositive ε) := by
  unfold suzukiSmoothPositive
  exact (contDiff_id.add (contDiff_suzukiSmoothAbsolute hε)).div_const 2

theorem abs_suzukiSmoothPositive_sub_le {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    |suzukiSmoothPositive ε x - suzukiSmoothPositive ε y| ≤ |x - y| := by
  unfold suzukiSmoothPositive
  rw [show (x + suzukiSmoothAbsolute ε x) / 2 -
      (y + suzukiSmoothAbsolute ε y) / 2 =
      ((x - y) + (suzukiSmoothAbsolute ε x - suzukiSmoothAbsolute ε y)) / 2 by
        ring,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    |(x - y) + (suzukiSmoothAbsolute ε x - suzukiSmoothAbsolute ε y)| / 2 ≤
        (|x - y| +
          |suzukiSmoothAbsolute ε x - suzukiSmoothAbsolute ε y|) / 2 :=
      div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ ≤ |x - y| := by
      linarith [abs_suzukiSmoothAbsolute_sub_le hε x y]

/-- Smooth approximation to `x ↦ min x 1`, translated to fix zero exactly. -/
def suzukiSmoothCap (ε x : ℝ) : ℝ :=
  (x + 1 - suzukiSmoothAbsolute ε (x - 1)) / 2 -
    (1 - suzukiSmoothAbsolute ε (-1)) / 2

@[simp] theorem suzukiSmoothCap_zero (ε : ℝ) :
    suzukiSmoothCap ε 0 = 0 := by
  unfold suzukiSmoothCap
  norm_num

theorem contDiff_suzukiSmoothCap {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiSmoothCap ε) := by
  unfold suzukiSmoothCap
  have hs : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ => suzukiSmoothAbsolute ε (x - 1)) :=
    (contDiff_suzukiSmoothAbsolute hε).comp (contDiff_id.sub contDiff_const)
  exact (((contDiff_id.add contDiff_const).sub hs).div_const 2).sub contDiff_const

theorem abs_suzukiSmoothCap_sub_le {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    |suzukiSmoothCap ε x - suzukiSmoothCap ε y| ≤ |x - y| := by
  unfold suzukiSmoothCap
  rw [show ((x + 1 - suzukiSmoothAbsolute ε (x - 1)) / 2 -
        (1 - suzukiSmoothAbsolute ε (-1)) / 2) -
      ((y + 1 - suzukiSmoothAbsolute ε (y - 1)) / 2 -
        (1 - suzukiSmoothAbsolute ε (-1)) / 2) =
      ((x - y) - (suzukiSmoothAbsolute ε (x - 1) -
        suzukiSmoothAbsolute ε (y - 1))) / 2 by ring,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    |(x - y) - (suzukiSmoothAbsolute ε (x - 1) -
        suzukiSmoothAbsolute ε (y - 1))| / 2 ≤
      (|x - y| + |suzukiSmoothAbsolute ε (x - 1) -
        suzukiSmoothAbsolute ε (y - 1)|) / 2 :=
      div_le_div_of_nonneg_right (abs_sub _ _) (by norm_num)
    _ ≤ |x - y| := by
      have hs := abs_suzukiSmoothAbsolute_sub_le hε (x - 1) (y - 1)
      rw [sub_sub_sub_cancel_right] at hs
      linarith

/-- Smooth normal-contraction approximation to Suzuki's truncation
`x ↦ min 1 (max 0 x)`, fixing zero exactly. -/
def suzukiSmoothNormalContraction (ε x : ℝ) : ℝ :=
  suzukiSmoothCap ε (suzukiSmoothPositive ε x)

@[simp] theorem suzukiSmoothNormalContraction_zero {ε : ℝ} (hε : 0 ≤ ε) :
    suzukiSmoothNormalContraction ε 0 = 0 := by
  simp [suzukiSmoothNormalContraction, suzukiSmoothPositive_zero hε]

theorem contDiff_suzukiSmoothNormalContraction {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiSmoothNormalContraction ε) := by
  exact (contDiff_suzukiSmoothCap hε).comp (contDiff_suzukiSmoothPositive hε)

theorem abs_suzukiSmoothNormalContraction_sub_le
    {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    |suzukiSmoothNormalContraction ε x -
      suzukiSmoothNormalContraction ε y| ≤ |x - y| := by
  exact (abs_suzukiSmoothCap_sub_le hε
    (suzukiSmoothPositive ε x) (suzukiSmoothPositive ε y)).trans
      (abs_suzukiSmoothPositive_sub_le hε x y)

theorem abs_suzukiSmoothNormalContraction_le_abs
    {ε x : ℝ} (hε : 0 < ε) :
    |suzukiSmoothNormalContraction ε x| ≤ |x| := by
  simpa only [suzukiSmoothNormalContraction_zero hε.le, sub_zero] using
    abs_suzukiSmoothNormalContraction_sub_le hε x 0

def suzukiNormalContraction (x : ℝ) : ℝ :=
  min 1 (max 0 x)

theorem max_zero_eq_add_abs_div_two (x : ℝ) :
    max 0 x = (x + |x|) / 2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_right hx, abs_of_nonneg hx]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_left hx', abs_of_nonpos hx']
    ring

theorem min_one_eq_sub_abs_div_two (x : ℝ) :
    min x 1 = (x + 1 - |x - 1|) / 2 := by
  by_cases hx : x ≤ 1
  · rw [min_eq_left hx, abs_of_nonpos (sub_nonpos.mpr hx)]
    ring
  · have hx' : 1 ≤ x := le_of_not_ge hx
    rw [min_eq_right hx', abs_of_nonneg (sub_nonneg.mpr hx')]
    ring

theorem abs_suzukiSmoothPositive_sub_max_le
    {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    |suzukiSmoothPositive ε x - max 0 x| ≤ ε / 2 := by
  rw [max_zero_eq_add_abs_div_two]
  unfold suzukiSmoothPositive
  rw [show (x + suzukiSmoothAbsolute ε x) / 2 - (x + |x|) / 2 =
      (suzukiSmoothAbsolute ε x - |x|) / 2 by ring,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right
    (by simpa only [abs_sub_comm] using abs_sub_suzukiSmoothAbsolute_le (x := x) hε)
    (by norm_num)

theorem abs_suzukiSmoothCapRaw_sub_min_le
    {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    |(x + 1 - suzukiSmoothAbsolute ε (x - 1)) / 2 - min x 1| ≤ ε / 2 := by
  rw [min_one_eq_sub_abs_div_two]
  rw [show (x + 1 - suzukiSmoothAbsolute ε (x - 1)) / 2 -
      (x + 1 - |x - 1|) / 2 =
      (|x - 1| - suzukiSmoothAbsolute ε (x - 1)) / 2 by ring,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right
    (abs_sub_suzukiSmoothAbsolute_le (x := x - 1) hε) (by norm_num)

theorem abs_suzukiSmoothCap_sub_min_le
    {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    |suzukiSmoothCap ε x - min x 1| ≤ ε := by
  have hx := abs_suzukiSmoothCapRaw_sub_min_le hε x
  have hzero := abs_suzukiSmoothCapRaw_sub_min_le hε 0
  rw [min_eq_left (by norm_num : (0 : ℝ) ≤ 1), sub_zero] at hzero
  norm_num at hzero
  unfold suzukiSmoothCap
  rw [show (x + 1 - suzukiSmoothAbsolute ε (x - 1)) / 2 -
      (1 - suzukiSmoothAbsolute ε (-1)) / 2 - min x 1 =
      ((x + 1 - suzukiSmoothAbsolute ε (x - 1)) / 2 - min x 1) -
        ((1 - suzukiSmoothAbsolute ε (-1)) / 2) by ring]
  calc
    |(x + 1 - suzukiSmoothAbsolute ε (x - 1)) / 2 - min x 1 -
        (1 - suzukiSmoothAbsolute ε (-1)) / 2| ≤
      |(x + 1 - suzukiSmoothAbsolute ε (x - 1)) / 2 - min x 1| +
        |(1 - suzukiSmoothAbsolute ε (-1)) / 2| := abs_sub _ _
    _ ≤ ε := by linarith

theorem abs_min_sub_min_one_le (x y : ℝ) :
    |min x 1 - min y 1| ≤ |x - y| := by
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (x - y))] using
    (abs_min_sub_min_le_max x 1 y 1)

theorem abs_suzukiSmoothNormalContraction_sub_normal_le
    {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    |suzukiSmoothNormalContraction ε x - suzukiNormalContraction x| ≤
      3 * ε / 2 := by
  have hcap := abs_suzukiSmoothCap_sub_min_le hε
    (suzukiSmoothPositive ε x)
  have hpos := abs_suzukiSmoothPositive_sub_max_le hε x
  have hmin := abs_min_sub_min_one_le (suzukiSmoothPositive ε x) (max 0 x)
  have hsplit :
      |suzukiSmoothNormalContraction ε x - suzukiNormalContraction x| ≤
        |suzukiSmoothCap ε (suzukiSmoothPositive ε x) -
          min (suzukiSmoothPositive ε x) 1| +
        |min (suzukiSmoothPositive ε x) 1 - min (max 0 x) 1| := by
    unfold suzukiSmoothNormalContraction suzukiNormalContraction
    rw [min_comm 1 (max 0 x)]
    rw [show suzukiSmoothCap ε (suzukiSmoothPositive ε x) - min (max 0 x) 1 =
      (suzukiSmoothCap ε (suzukiSmoothPositive ε x) -
        min (suzukiSmoothPositive ε x) 1) +
      (min (suzukiSmoothPositive ε x) 1 - min (max 0 x) 1) by ring]
    exact abs_add_le _ _
  exact hsplit.trans (by linarith)

theorem abs_suzukiNormalContraction_sub_le (x y : ℝ) :
    |suzukiNormalContraction x - suzukiNormalContraction y| ≤ |x - y| := by
  have hmin := abs_min_sub_min_le_max 1 (max 0 x) 1 (max 0 y)
  have hmax := abs_max_sub_max_le_abs x y 0
  unfold suzukiNormalContraction
  rw [max_comm 0 x, max_comm 0 y]
  have hmin' : |min 1 (max x 0) - min 1 (max y 0)| ≤
      |max x 0 - max y 0| := by
    simpa [max_comm] using hmin
  exact hmin'.trans hmax

def suzukiComplexNormalContraction (z : ℂ) : ℂ :=
  (suzukiNormalContraction z.re : ℂ)

@[simp] theorem suzukiComplexNormalContraction_zero :
    suzukiComplexNormalContraction 0 = 0 := by
  simp [suzukiComplexNormalContraction, suzukiNormalContraction]

theorem lipschitzWith_suzukiComplexNormalContraction :
    LipschitzWith 1 suzukiComplexNormalContraction := by
  apply LipschitzWith.mk_one
  intro z w
  rw [dist_eq_norm, dist_eq_norm]
  unfold suzukiComplexNormalContraction
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc
    |suzukiNormalContraction z.re - suzukiNormalContraction w.re| ≤
        |z.re - w.re| := abs_suzukiNormalContraction_sub_le z.re w.re
    _ = |(z - w).re| := by rw [Complex.sub_re]
    _ ≤ ‖z - w‖ := abs_re_le_norm _

/-- Suzuki's literal normal contraction on physical interval `L²`, applied to the real part. -/
def suzukiIntervalL2NormalContraction (f : SuzukiApertureIntervalL2 1) :
    SuzukiApertureIntervalL2 1 :=
  (lipschitzWith_suzukiComplexNormalContraction.comp_memLp
    suzukiComplexNormalContraction_zero (MeasureTheory.Lp.memLp f)).toLp
      (suzukiComplexNormalContraction ∘ fun x => f x)

theorem suzukiIntervalL2NormalContraction_coeFn
    (f : SuzukiApertureIntervalL2 1) :
    (suzukiIntervalL2NormalContraction f : SuzukiApertureInterval 1 → ℂ) =ᵐ[volume]
      suzukiComplexNormalContraction ∘ fun x => f x := by
  exact (lipschitzWith_suzukiComplexNormalContraction.comp_memLp
    suzukiComplexNormalContraction_zero (MeasureTheory.Lp.memLp f)).coeFn_toLp

theorem norm_suzukiIntervalL2NormalContraction_sub_le
    (f g : SuzukiApertureIntervalL2 1) :
    ‖suzukiIntervalL2NormalContraction f -
      suzukiIntervalL2NormalContraction g‖ ≤ ‖f - g‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  apply ENNReal.toReal_mono (MeasureTheory.Lp.eLpNorm_ne_top (f - g))
  apply eLpNorm_mono_ae
  filter_upwards [
    suzukiIntervalL2NormalContraction_coeFn f,
    suzukiIntervalL2NormalContraction_coeFn g,
    MeasureTheory.Lp.coeFn_sub (suzukiIntervalL2NormalContraction f)
      (suzukiIntervalL2NormalContraction g),
    MeasureTheory.Lp.coeFn_sub f g] with x hf hg hnormalSub hfgSub
  rw [hnormalSub, hfgSub, Pi.sub_apply, Pi.sub_apply, hf, hg]
  simpa only [Function.comp_apply, NNReal.coe_one, one_mul] using
    lipschitzWith_suzukiComplexNormalContraction.norm_sub_le (f x) (g x)

theorem lipschitzWith_suzukiIntervalL2NormalContraction :
    LipschitzWith 1 suzukiIntervalL2NormalContraction := by
  apply LipschitzWith.mk_one
  intro f g
  simpa only [dist_eq_norm] using
    norm_suzukiIntervalL2NormalContraction_sub_le f g

theorem continuous_suzukiIntervalL2NormalContraction :
    Continuous suzukiIntervalL2NormalContraction :=
  lipschitzWith_suzukiIntervalL2NormalContraction.continuous

@[simp] theorem suzukiIntervalL2NormalContraction_zero :
    suzukiIntervalL2NormalContraction (0 : SuzukiApertureIntervalL2 1) = 0 := by
  apply MeasureTheory.Lp.ext
  filter_upwards [suzukiIntervalL2NormalContraction_coeFn
    (0 : SuzukiApertureIntervalL2 1), MeasureTheory.Lp.coeFn_zero ℂ 2 volume]
      with x hnormal hzero
  rw [hnormal, Function.comp_apply, hzero, Pi.zero_apply,
    suzukiComplexNormalContraction_zero]

theorem norm_suzukiIntervalL2NormalContraction_le
    (f : SuzukiApertureIntervalL2 1) :
    ‖suzukiIntervalL2NormalContraction f‖ ≤ ‖f‖ := by
  simpa only [suzukiIntervalL2NormalContraction_zero, sub_zero] using
    norm_suzukiIntervalL2NormalContraction_sub_le f 0

def suzukiSmoothNormalContractionCore
    (u : SuzukiRestrictedWeilCore 1) (ε : ℝ) (hε : 0 < ε) :
    SuzukiRestrictedWeilCore 1 where
  toFun := fun x => suzukiSmoothNormalContraction ε (u x)
  smooth := (contDiff_suzukiSmoothNormalContraction hε.ne').comp u.smooth
  supportRadius := u.supportRadius
  supportRadius_nonneg := u.supportRadius_nonneg
  supportRadius_lt_aperture := u.supportRadius_lt_aperture
  support_subset := by
    intro x hx
    apply u.support_subset
    intro hux
    apply hx
    simp [hux, suzukiSmoothNormalContraction_zero hε.le]

@[simp] theorem suzukiSmoothNormalContractionCore_apply
    (u : SuzukiRestrictedWeilCore 1) (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    suzukiSmoothNormalContractionCore u ε hε x =
      suzukiSmoothNormalContraction ε (u x) := rfl

theorem suzukiFinitePartEnergy_smoothNormalContraction_le
    (u : SuzukiRestrictedWeilCore 1) (ε : ℝ) (hε : 0 < ε) :
    suzukiFinitePartEnergy 1 (suzukiSmoothNormalContractionCore u ε hε) ≤
      suzukiFinitePartEnergy 1 u := by
  apply suzukiFinitePartEnergy_le_of_pointwise_contraction
  · intro x
    exact abs_suzukiSmoothNormalContraction_le_abs hε
  · intro x y
    exact abs_suzukiSmoothNormalContraction_sub_le hε (u x) (u y)

theorem suzukiSmoothNormalContractionCore_mass_le
    (u : SuzukiRestrictedWeilCore 1) (ε : ℝ) (hε : 0 < ε) :
    (∫ x in (-1 : ℝ)..1,
      (suzukiSmoothNormalContractionCore u ε hε x) ^ 2) ≤
        ∫ x in (-1 : ℝ)..1, u x ^ 2 := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (((suzukiSmoothNormalContractionCore u ε hε).continuous.pow 2).intervalIntegrable
      (-1 : ℝ) 1)
    ((u.continuous.pow 2).intervalIntegrable (-1 : ℝ) 1)
  intro x _
  exact sq_le_sq.mpr (abs_suzukiSmoothNormalContraction_le_abs hε)

def suzukiCoreNormalIntervalContinuous (u : SuzukiRestrictedWeilCore 1) :
    C(SuzukiApertureInterval 1, ℂ) where
  toFun x := (suzukiNormalContraction (u (x : ℝ)) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (continuous_const.min
      (continuous_const.max (u.continuous.comp continuous_subtype_val)))

def suzukiCoreSmoothNormalIntervalContinuous
    (u : SuzukiRestrictedWeilCore 1) (ε : ℝ) (hε : ε ≠ 0) :
    C(SuzukiApertureInterval 1, ℂ) where
  toFun x := (suzukiSmoothNormalContraction ε (u (x : ℝ)) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    ((contDiff_suzukiSmoothNormalContraction hε).continuous.comp
      (u.continuous.comp continuous_subtype_val))

theorem norm_suzukiCoreSmoothNormalIntervalContinuous_sub_le
    (u : SuzukiRestrictedWeilCore 1) {ε : ℝ} (hε : 0 < ε) :
    ‖suzukiCoreSmoothNormalIntervalContinuous u ε hε.ne' -
      suzukiCoreNormalIntervalContinuous u‖ ≤ 3 * ε / 2 := by
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro x
  change ‖(suzukiSmoothNormalContraction ε (u (x : ℝ)) : ℂ) -
    (suzukiNormalContraction (u (x : ℝ)) : ℂ)‖ ≤ 3 * ε / 2
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_suzukiSmoothNormalContraction_sub_normal_le hε.le (u (x : ℝ))

theorem tendsto_suzukiCoreSmoothNormalIntervalContinuous
    (u : SuzukiRestrictedWeilCore 1) :
    Tendsto (fun n => suzukiCoreSmoothNormalIntervalContinuous u
      (suzukiSmoothAbsoluteScale n) (suzukiSmoothAbsoluteScale_pos n).ne') atTop
      (nhds (suzukiCoreNormalIntervalContinuous u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero
  · exact fun n => norm_nonneg _
  · exact fun n => norm_suzukiCoreSmoothNormalIntervalContinuous_sub_le u
      (suzukiSmoothAbsoluteScale_pos n)
  · have hconst : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (nhds 3) :=
      tendsto_const_nhds
    have h := hconst.mul tendsto_suzukiSmoothAbsoluteScale_zero
    have h' := h.div_const (2 : ℝ)
    simpa using h'

def suzukiCoreNormalIntervalVector (u : SuzukiRestrictedWeilCore 1) :
    SuzukiApertureIntervalL2 1 :=
  ContinuousMap.toLp 2 volume ℂ (suzukiCoreNormalIntervalContinuous u)

theorem suzukiCoreNormalIntervalVector_coeFn (u : SuzukiRestrictedWeilCore 1) :
    (suzukiCoreNormalIntervalVector u : SuzukiApertureInterval 1 → ℂ) =ᵐ[volume]
      fun x => (suzukiNormalContraction (u (x : ℝ)) : ℂ) := by
  exact ContinuousMap.coeFn_toLp volume (suzukiCoreNormalIntervalContinuous u)

theorem suzukiCoreNormalIntervalVector_eq_normalContraction
    (u : SuzukiRestrictedWeilCore 1) :
    suzukiCoreNormalIntervalVector u =
      suzukiIntervalL2NormalContraction (suzukiLimitingCoreIntervalVector u) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [suzukiCoreNormalIntervalVector_coeFn u,
    suzukiIntervalL2NormalContraction_coeFn (suzukiLimitingCoreIntervalVector u),
    suzukiLimitingCoreIntervalVector_coeFn u] with x hnormal hLp hcore
  rw [hnormal, hLp, Function.comp_apply, hcore]
  rfl

def suzukiSmoothNormalCoreFormVector
    (u : SuzukiRestrictedWeilCore 1) (n : ℕ) :
    CCMArchimedeanFormDomain suzukiLimitingUnitAperture :=
  suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture
    (suzukiSmoothNormalContractionCore u (suzukiSmoothAbsoluteScale n)
      (suzukiSmoothAbsoluteScale_pos n))

theorem suzukiLimitingLogFormEmbedding_smoothNormalCoreFormVector
    (u : SuzukiRestrictedWeilCore 1) (n : ℕ) :
    suzukiLimitingLogFormEmbedding (suzukiSmoothNormalCoreFormVector u n) =
      ContinuousMap.toLp 2 volume ℂ
        (suzukiCoreSmoothNormalIntervalContinuous u
          (suzukiSmoothAbsoluteScale n) (suzukiSmoothAbsoluteScale_pos n).ne') := by
  unfold suzukiSmoothNormalCoreFormVector
  rw [← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
  apply MeasureTheory.Lp.ext
  filter_upwards [
    suzukiLimitingCoreIntervalVector_coeFn
      (suzukiSmoothNormalContractionCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n)),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (volume : Measure (SuzukiApertureInterval 1))
      (suzukiCoreSmoothNormalIntervalContinuous u
        (suzukiSmoothAbsoluteScale n) (suzukiSmoothAbsoluteScale_pos n).ne')]
      with x hcore hsmooth
  rw [hcore, hsmooth]
  rfl

theorem tendsto_suzukiLimitingLogFormEmbedding_smoothNormalCoreFormVector
    (u : SuzukiRestrictedWeilCore 1) :
    Tendsto (fun n => suzukiLimitingLogFormEmbedding
      (suzukiSmoothNormalCoreFormVector u n)) atTop
      (nhds (suzukiCoreNormalIntervalVector u)) := by
  have h := (ContinuousMap.toLp 2
      (volume : Measure (SuzukiApertureInterval 1)) ℂ).continuous.tendsto
    (suzukiCoreNormalIntervalContinuous u)
  have hc : Tendsto (fun n => ContinuousMap.toLp 2
      (volume : Measure (SuzukiApertureInterval 1)) ℂ
        (suzukiCoreSmoothNormalIntervalContinuous u
          (suzukiSmoothAbsoluteScale n) (suzukiSmoothAbsoluteScale_pos n).ne')) atTop
      (nhds (ContinuousMap.toLp 2
        (volume : Measure (SuzukiApertureInterval 1)) ℂ
          (suzukiCoreNormalIntervalContinuous u))) :=
    h.comp (tendsto_suzukiCoreSmoothNormalIntervalContinuous u)
  simpa only [suzukiCoreNormalIntervalVector,
    suzukiLimitingLogFormEmbedding_smoothNormalCoreFormVector] using hc

theorem norm_sq_suzukiCoreFormVector_le_coreShiftedEnergy
    (u v : SuzukiRestrictedWeilCore 1)
    (henergy : suzukiFinitePartEnergy 1 v ≤ suzukiFinitePartEnergy 1 u)
    (hmass : (∫ x in (-1 : ℝ)..1, v x ^ 2) ≤
      ∫ x in (-1 : ℝ)..1, u x ^ 2) :
    ‖suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v‖ ^ 2 ≤
      suzukiCoreShiftedEnergy u := by
  let qv := suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v
  have hcoer := boundedPerturbedFormRiesz_coercive
    suzukiLimitingLogFormEmbedding suzukiLimitingLogBoundedRemainder qv
  rw [suzukiLimitingLogFormRiesz_diagonal_re] at hcoer
  have hform : (suzukiLimitingLogClosedForm qv qv).re =
      suzukiFinitePartEnergy 1 v := by
    change (suzukiLimitingLogClosedForm
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v)
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v)).re = _
    rw [suzukiLimitingLogClosedForm_core_eq_weilFinitePartBlock,
      Complex.ofReal_re]
    simpa only [suzukiLimitingUnitAperture] using
      suzukiWeilFinitePartBlock_eq_energy suzukiLimitingUnitAperture v
  have hmassv : ‖suzukiLimitingLogFormEmbedding qv‖ ^ 2 =
      ∫ x in (-1 : ℝ)..1, v x ^ 2 := by
    exact norm_sq_suzukiLimitingLogFormEmbedding_coreFormVector v
  rw [hform, hmassv] at hcoer
  have hshift : 0 ≤ boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder :=
    (boundedPerturbedFormShift_pos suzukiLimitingLogBoundedRemainder).le
  unfold suzukiCoreShiftedEnergy
  exact hcoer.trans
    (add_le_add henergy (mul_le_mul_of_nonneg_left hmass hshift))

theorem norm_suzukiSmoothNormalCoreFormVector_le_sqrt
    (u : SuzukiRestrictedWeilCore 1) (n : ℕ) :
    ‖suzukiSmoothNormalCoreFormVector u n‖ ≤
      Real.sqrt (suzukiCoreShiftedEnergy u) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (suzukiCoreShiftedEnergy_nonneg u)]
  exact norm_sq_suzukiCoreFormVector_le_coreShiftedEnergy u
    (suzukiSmoothNormalContractionCore u (suzukiSmoothAbsoluteScale n)
      (suzukiSmoothAbsoluteScale_pos n))
    (suzukiFinitePartEnergy_smoothNormalContraction_le u
      (suzukiSmoothAbsoluteScale n) (suzukiSmoothAbsoluteScale_pos n))
    (suzukiSmoothNormalContractionCore_mass_le u
      (suzukiSmoothAbsoluteScale n) (suzukiSmoothAbsoluteScale_pos n))

theorem suzukiLimitingLogShiftedEnergy_smoothNormalCoreFormVector_le
    (u : SuzukiRestrictedWeilCore 1) (n : ℕ) :
    suzukiLimitingLogShiftedEnergy (suzukiSmoothNormalCoreFormVector u n) ≤
      suzukiCoreShiftedEnergy u := by
  let v := suzukiSmoothNormalContractionCore u (suzukiSmoothAbsoluteScale n)
    (suzukiSmoothAbsoluteScale_pos n)
  have hform : (suzukiLimitingLogClosedForm
      (suzukiSmoothNormalCoreFormVector u n)
      (suzukiSmoothNormalCoreFormVector u n)).re =
      suzukiFinitePartEnergy 1 v := by
    change (suzukiLimitingLogClosedForm
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v)
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v)).re = _
    rw [suzukiLimitingLogClosedForm_core_eq_weilFinitePartBlock,
      Complex.ofReal_re]
    simpa only [suzukiLimitingUnitAperture] using
      suzukiWeilFinitePartBlock_eq_energy suzukiLimitingUnitAperture v
  have hmass : ‖suzukiLimitingLogFormEmbedding
      (suzukiSmoothNormalCoreFormVector u n)‖ ^ 2 =
      ∫ x in (-1 : ℝ)..1, v x ^ 2 := by
    exact norm_sq_suzukiLimitingLogFormEmbedding_coreFormVector v
  have henergy := suzukiFinitePartEnergy_smoothNormalContraction_le u
    (suzukiSmoothAbsoluteScale n) (suzukiSmoothAbsoluteScale_pos n)
  have hmassle := suzukiSmoothNormalContractionCore_mass_le u
    (suzukiSmoothAbsoluteScale n) (suzukiSmoothAbsoluteScale_pos n)
  have hshift : 0 ≤ boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder :=
    (boundedPerturbedFormShift_pos suzukiLimitingLogBoundedRemainder).le
  unfold suzukiLimitingLogShiftedEnergy suzukiCoreShiftedEnergy
  rw [hform, hmass]
  exact add_le_add henergy (mul_le_mul_of_nonneg_left hmassle hshift)

/-- Exact smooth-core construction of Suzuki's literal normal contraction inside the complete
real form domain. -/
theorem exists_suzukiCoreNormalRealFormVector
    (u : SuzukiRestrictedWeilCore 1) :
    ∃ w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      w ∈ SuzukiLimitingRealFormDomain ∧
      suzukiLimitingLogFormEmbedding w =
        suzukiIntervalL2NormalContraction (suzukiLimitingCoreIntervalVector u) ∧
      (suzukiLimitingLogClosedForm w w).re ≤
        (suzukiLimitingLogClosedForm
          (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)
          (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)).re ∧
      suzukiLimitingLogShiftedEnergy w ≤
        suzukiLimitingLogShiftedEnergy
          (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u) := by
  let q : ℕ → CCMArchimedeanFormDomain suzukiLimitingUnitAperture :=
    fun n => suzukiSmoothNormalCoreFormVector u n
  let M := Real.sqrt (suzukiCoreShiftedEnergy u)
  obtain ⟨w, φ, hφ, _hwM, hweak, hcompact⟩ :=
    exists_suzukiLimitingLogForm_weakSubseq q M
      (norm_suzukiSmoothNormalCoreFormVector_le_sqrt u)
  have hqmem (n : ℕ) : q n ∈ suzukiLimitingRealCoreSubmodule := by
    exact suzukiRestrictedWeilCoreCCMFormVector_mem_realCoreSubmodule
      (suzukiSmoothNormalContractionCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n))
  have hwreal : w ∈ SuzukiLimitingRealFormDomain :=
    mem_topologicalClosure_of_complexWeak_limit
      suzukiLimitingRealCoreSubmodule (fun n => q (φ n)) w
        (fun n => hqmem (φ n)) hweak
  have hphysicalW : Tendsto (fun n => suzukiLimitingLogFormEmbedding (q (φ n)))
      atTop (nhds (suzukiLimitingLogFormEmbedding w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact hcompact
  have hphysicalNormal : Tendsto
      (fun n => suzukiLimitingLogFormEmbedding (q (φ n))) atTop
      (nhds (suzukiCoreNormalIntervalVector u)) :=
    (tendsto_suzukiLimitingLogFormEmbedding_smoothNormalCoreFormVector u).comp
      hφ.tendsto_atTop
  have hrepCore : suzukiLimitingLogFormEmbedding w =
      suzukiCoreNormalIntervalVector u :=
    tendsto_nhds_unique hphysicalW hphysicalNormal
  have hclosed_q (n : ℕ) :
      (suzukiLimitingLogClosedForm (q n) (q n)).re =
        suzukiFinitePartEnergy 1
          (suzukiSmoothNormalContractionCore u (suzukiSmoothAbsoluteScale n)
            (suzukiSmoothAbsoluteScale_pos n)) := by
    change (suzukiLimitingLogClosedForm
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture
        (suzukiSmoothNormalContractionCore u (suzukiSmoothAbsoluteScale n)
          (suzukiSmoothAbsoluteScale_pos n)))
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture
        (suzukiSmoothNormalContractionCore u (suzukiSmoothAbsoluteScale n)
          (suzukiSmoothAbsoluteScale_pos n)))).re = _
    rw [suzukiLimitingLogClosedForm_core_eq_weilFinitePartBlock,
      Complex.ofReal_re]
    simpa only [suzukiLimitingUnitAperture] using
      suzukiWeilFinitePartBlock_eq_energy suzukiLimitingUnitAperture
        (suzukiSmoothNormalContractionCore u (suzukiSmoothAbsoluteScale n)
          (suzukiSmoothAbsoluteScale_pos n))
  have hclosed_q_le (n : ℕ) :
      (suzukiLimitingLogClosedForm (q n) (q n)).re ≤
        suzukiFinitePartEnergy 1 u := by
    rw [hclosed_q]
    exact suzukiFinitePartEnergy_smoothNormalContraction_le u
      (suzukiSmoothAbsoluteScale n) (suzukiSmoothAbsoluteScale_pos n)
  have hnormT : Tendsto
      (fun n => ‖suzukiLimitingLogFormEmbedding (q (φ n))‖) atTop
      (nhds ‖suzukiCoreNormalIntervalVector u‖) :=
    (continuous_norm.tendsto _).comp hphysicalNormal
  have hnormT_sq : Tendsto
      (fun n => ‖suzukiLimitingLogFormEmbedding (q (φ n))‖ ^ 2) atTop
      (nhds (‖suzukiCoreNormalIntervalVector u‖ ^ 2)) := hnormT.pow 2
  have hboundTend : Tendsto (fun n =>
      suzukiFinitePartEnergy 1 u +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          ‖suzukiLimitingLogFormEmbedding (q (φ n))‖ ^ 2) atTop
      (nhds (suzukiFinitePartEnergy 1 u +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          ‖suzukiCoreNormalIntervalVector u‖ ^ 2)) := by
    exact tendsto_const_nhds.add (tendsto_const_nhds.mul hnormT_sq)
  have hshiftedSharp : suzukiLimitingLogShiftedEnergy w ≤
      suzukiFinitePartEnergy 1 u +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          ‖suzukiCoreNormalIntervalVector u‖ ^ 2 := by
    apply suzukiLimitingLogShiftedEnergy_le_of_weak_limit_upper_tendsto
      (fun n => q (φ n)) w hweak _ _ hboundTend
    intro n
    unfold suzukiLimitingLogShiftedEnergy
    exact add_le_add (hclosed_q_le (φ n)) le_rfl
  have hclosed : (suzukiLimitingLogClosedForm w w).re ≤
      suzukiFinitePartEnergy 1 u := by
    unfold suzukiLimitingLogShiftedEnergy at hshiftedSharp
    rw [hrepCore] at hshiftedSharp
    exact (add_le_add_iff_right
      (boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
        ‖suzukiCoreNormalIntervalVector u‖ ^ 2)).mp hshiftedSharp
  have hclosedCore :
      (suzukiLimitingLogClosedForm
        (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)
        (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)).re =
          suzukiFinitePartEnergy 1 u := by
    rw [suzukiLimitingLogClosedForm_core_eq_weilFinitePartBlock,
      Complex.ofReal_re]
    simpa only [suzukiLimitingUnitAperture] using
      suzukiWeilFinitePartBlock_eq_energy suzukiLimitingUnitAperture u
  have hclosedForm : (suzukiLimitingLogClosedForm w w).re ≤
      (suzukiLimitingLogClosedForm
        (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)
        (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)).re := by
    rw [hclosedCore]
    exact hclosed
  have hnorm : ‖suzukiLimitingLogFormEmbedding w‖ ≤
      ‖suzukiLimitingLogFormEmbedding
        (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)‖ := by
    rw [hrepCore, ← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
    rw [suzukiCoreNormalIntervalVector_eq_normalContraction]
    exact norm_suzukiIntervalL2NormalContraction_le _
  have hshift : 0 ≤ boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder :=
    (boundedPerturbedFormShift_pos suzukiLimitingLogBoundedRemainder).le
  have hshifted : suzukiLimitingLogShiftedEnergy w ≤
      suzukiLimitingLogShiftedEnergy
        (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u) := by
    unfold suzukiLimitingLogShiftedEnergy
    exact add_le_add hclosedForm
      (mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm) hshift)
  refine ⟨w, hwreal, ?_, hclosedForm, hshifted⟩
  · rw [hrepCore, suzukiCoreNormalIntervalVector_eq_normalContraction]

theorem continuous_suzukiLimitingLogClosedEnergy :
    Continuous (fun q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture =>
      (suzukiLimitingLogClosedForm q q).re) := by
  have hfun : (fun q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture =>
      (suzukiLimitingLogClosedForm q q).re) = fun q =>
        suzukiLimitingLogShiftedEnergy q -
          boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
            ‖suzukiLimitingLogFormEmbedding q‖ ^ 2 := by
    funext q
    unfold suzukiLimitingLogShiftedEnergy
    ring
  rw [hfun]
  exact continuous_suzukiLimitingLogShiftedEnergy.sub
    (continuous_const.mul
      ((continuous_norm.comp suzukiLimitingLogFormEmbedding.continuous).pow 2))

/-- Closure principle for exact real normal contractions: a continuous physical contraction whose
smooth real-core lifts contract both closed and shifted energies extends to the entire canonical
closed real form domain, retaining the exact unshifted energy inequality. -/
theorem exists_suzukiRealFormDomainContraction_of_core
    (T : SuzukiApertureIntervalL2 1 → SuzukiApertureIntervalL2 1)
    (hT : Continuous T)
    (hcore : ∀ u : SuzukiRestrictedWeilCore 1,
      ∃ w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
        w ∈ SuzukiLimitingRealFormDomain ∧
        suzukiLimitingLogFormEmbedding w = T (suzukiLimitingCoreIntervalVector u) ∧
        (suzukiLimitingLogClosedForm w w).re ≤
          (suzukiLimitingLogClosedForm
            (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)
            (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)).re ∧
        suzukiLimitingLogShiftedEnergy w ≤
          suzukiLimitingLogShiftedEnergy
            (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u))
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain) :
    ∃ w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      w ∈ SuzukiLimitingRealFormDomain ∧
      suzukiLimitingLogFormEmbedding w = T (suzukiLimitingLogFormEmbedding q) ∧
      (suzukiLimitingLogClosedForm w w).re ≤
        (suzukiLimitingLogClosedForm q q).re := by
  change q ∈ closure
    (suzukiLimitingRealCoreSubmodule : Set
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)) at hq
  obtain ⟨z, hzcore, hzlim⟩ := mem_closure_iff_seq_limit.mp hq
  have htests (n : ℕ) : ∃ t : SuzukiRestrictedWeilRealTest 1,
      suzukiLimitingRealTestFormLinearMap t = z n := hzcore n
  choose t ht using htests
  let u : ℕ → SuzukiRestrictedWeilCore 1 := fun n =>
    suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture (t n)
  have hzform (n : ℕ) : z n =
      suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture (u n) := by
    rw [← ht n]
    rfl
  have hcoreExists (n : ℕ) := hcore (u n)
  choose v hvreal hvrep hvclosed hvshifted using hcoreExists
  have hzshifted : Tendsto (fun n => suzukiLimitingLogShiftedEnergy (z n)) atTop
      (nhds (suzukiLimitingLogShiftedEnergy q)) :=
    (continuous_suzukiLimitingLogShiftedEnergy.tendsto q).comp hzlim
  have hzenergyBounded : Bornology.IsBounded
      (Set.range (fun n : ℕ => suzukiLimitingLogShiftedEnergy (z n)) : Set ℝ) :=
    Metric.isBounded_range_of_tendsto
      (fun n => suzukiLimitingLogShiftedEnergy (z n)) hzshifted
  obtain ⟨C, hCrange⟩ :=
    (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp hzenergyBounded
  have hCpos : 0 < C :=
    lt_of_le_of_lt dist_nonneg (hCrange ⟨0, rfl⟩)
  have hzshifted_le (n : ℕ) : suzukiLimitingLogShiftedEnergy (z n) ≤ C := by
    calc
      suzukiLimitingLogShiftedEnergy (z n) ≤
          |suzukiLimitingLogShiftedEnergy (z n)| := le_abs_self _
      _ = dist (suzukiLimitingLogShiftedEnergy (z n)) 0 := by
        rw [Real.dist_eq, sub_zero]
      _ ≤ C := (hCrange ⟨n, rfl⟩).le
  have hvshifted_z (n : ℕ) : suzukiLimitingLogShiftedEnergy (v n) ≤
      suzukiLimitingLogShiftedEnergy (z n) := by
    calc
      suzukiLimitingLogShiftedEnergy (v n) ≤
          suzukiLimitingLogShiftedEnergy
            (suzukiRestrictedWeilCoreCCMFormVector
              suzukiLimitingUnitAperture (u n)) := hvshifted n
      _ = suzukiLimitingLogShiftedEnergy (z n) :=
        congrArg suzukiLimitingLogShiftedEnergy (hzform n).symm
  have hvnorm (n : ℕ) : ‖v n‖ ≤ Real.sqrt C := by
    have hcoer : ‖v n‖ ^ 2 ≤ suzukiLimitingLogShiftedEnergy (v n) := by
      have h := boundedPerturbedFormRiesz_coercive
        suzukiLimitingLogFormEmbedding suzukiLimitingLogBoundedRemainder (v n)
      rwa [← suzukiLimitingLogShiftedEnergy_eq_riesz] at h
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hCpos.le]
    exact hcoer.trans ((hvshifted_z n).trans (hzshifted_le n))
  obtain ⟨w, φ, hφ, _hwC, hweak, hcompact⟩ :=
    exists_suzukiLimitingLogForm_weakSubseq v (Real.sqrt C) hvnorm
  have hwrealClosure : w ∈ SuzukiLimitingRealFormDomain.topologicalClosure :=
    mem_topologicalClosure_of_complexWeak_limit SuzukiLimitingRealFormDomain
      (fun n => v (φ n)) w (fun n => hvreal (φ n)) hweak
  have hwreal : w ∈ SuzukiLimitingRealFormDomain := by
    rw [isClosed_suzukiLimitingRealFormDomain.submodule_topologicalClosure_eq]
      at hwrealClosure
    exact hwrealClosure
  have hphysicalW : Tendsto
      (fun n => suzukiLimitingLogFormEmbedding (v (φ n))) atTop
      (nhds (suzukiLimitingLogFormEmbedding w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact hcompact
  have hzsub : Tendsto (fun n => z (φ n)) atTop (nhds q) :=
    hzlim.comp hφ.tendsto_atTop
  have hzphysical : Tendsto
      (fun n => suzukiLimitingLogFormEmbedding (z (φ n))) atTop
      (nhds (suzukiLimitingLogFormEmbedding q)) :=
    (suzukiLimitingLogFormEmbedding.continuous.tendsto q).comp hzsub
  have hTphysical : Tendsto
      (fun n => T (suzukiLimitingLogFormEmbedding (z (φ n)))) atTop
      (nhds (T (suzukiLimitingLogFormEmbedding q))) :=
    (hT.tendsto (suzukiLimitingLogFormEmbedding q)).comp hzphysical
  have hvphysical : Tendsto
      (fun n => suzukiLimitingLogFormEmbedding (v (φ n))) atTop
      (nhds (T (suzukiLimitingLogFormEmbedding q))) := by
    convert hTphysical using 1
    funext n
    rw [hvrep (φ n), hzform (φ n),
      suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
  have hrep : suzukiLimitingLogFormEmbedding w =
      T (suzukiLimitingLogFormEmbedding q) :=
    tendsto_nhds_unique hphysicalW hvphysical
  have hzclosed : Tendsto
      (fun n => (suzukiLimitingLogClosedForm (z n) (z n)).re) atTop
      (nhds (suzukiLimitingLogClosedForm q q).re) :=
    (continuous_suzukiLimitingLogClosedEnergy.tendsto q).comp hzlim
  have hzclosedSub : Tendsto
      (fun n => (suzukiLimitingLogClosedForm (z (φ n)) (z (φ n))).re) atTop
      (nhds (suzukiLimitingLogClosedForm q q).re) :=
    hzclosed.comp hφ.tendsto_atTop
  have hTnorm : Tendsto
      (fun n => ‖T (suzukiLimitingLogFormEmbedding (z (φ n)))‖) atTop
      (nhds ‖T (suzukiLimitingLogFormEmbedding q)‖) :=
    (continuous_norm.tendsto _).comp hTphysical
  have hTnormSq := hTnorm.pow 2
  have hboundTend : Tendsto (fun n =>
      (suzukiLimitingLogClosedForm (z (φ n)) (z (φ n))).re +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          ‖T (suzukiLimitingLogFormEmbedding (z (φ n)))‖ ^ 2) atTop
      (nhds ((suzukiLimitingLogClosedForm q q).re +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          ‖T (suzukiLimitingLogFormEmbedding q)‖ ^ 2)) := by
    exact hzclosedSub.add (tendsto_const_nhds.mul hTnormSq)
  have hshiftedSharp : suzukiLimitingLogShiftedEnergy w ≤
      (suzukiLimitingLogClosedForm q q).re +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          ‖T (suzukiLimitingLogFormEmbedding q)‖ ^ 2 := by
    apply suzukiLimitingLogShiftedEnergy_le_of_weak_limit_upper_tendsto
      (fun n => v (φ n)) w hweak _ _ hboundTend
    intro n
    unfold suzukiLimitingLogShiftedEnergy
    rw [hvrep (φ n), hzform (φ n),
      suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
    exact add_le_add (hvclosed (φ n)) le_rfl
  have hwclosed : (suzukiLimitingLogClosedForm w w).re ≤
      (suzukiLimitingLogClosedForm q q).re := by
    unfold suzukiLimitingLogShiftedEnergy at hshiftedSharp
    rw [hrep] at hshiftedSharp
    exact (add_le_add_iff_right
      (boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
        ‖T (suzukiLimitingLogFormEmbedding q)‖ ^ 2)).mp hshiftedSharp
  exact ⟨w, hwreal, hrep, hwclosed⟩

/-- Suzuki's exact closed-form normal-contraction theorem on the complete real form domain. -/
theorem exists_suzukiRealFormDomainNormalContraction
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain) :
    ∃ w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      w ∈ SuzukiLimitingRealFormDomain ∧
      suzukiLimitingLogFormEmbedding w =
        suzukiIntervalL2NormalContraction (suzukiLimitingLogFormEmbedding q) ∧
      (suzukiLimitingLogClosedForm w w).re ≤
        (suzukiLimitingLogClosedForm q q).re := by
  exact exists_suzukiRealFormDomainContraction_of_core
    suzukiIntervalL2NormalContraction
    continuous_suzukiIntervalL2NormalContraction
    exists_suzukiCoreNormalRealFormVector q hq

end RHTower
