import GaloisForLFunctions.RHTower.SelbergScatteringCutoffDerivatives
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMHeightLaplacian
import GaloisForLFunctions.RHTower.SelbergScatteringEntireOperator
import GaloisForLFunctions.HTGeometry.CfcEigenvector

/-!
# Actual native constant mode and the mean of an occurrence residual

Original smooth modular cutoffs converge to the literal constant vector and
have vanishing Laplacian error in native norm. The closed graph therefore gives
A1=1. Continuous functional calculus and the exact symbol at zero give C1=1/3
and T1=1 in the actual entire graph. Every bounded occurrence residual has the
exact mean (1-mu)/3 times its source mean and a corresponding native norm bound.

The original constant component can be separated exactly. Centering commutes
with the actual covariance and preserves the remaining residual equation; its
vanishing is not asserted.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped InnerProductSpace ContDiff
namespace RHTower.SelbergNativeConstantMode
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries D4BMJointSource
open SelbergScatteringSourceApproximation SelbergScatteringCutoffDerivatives
open SelbergScatteringEntireOperator SelbergScatteringEntireTransform
noncomputable section

local instance : IsometricContinuousFunctionalCalculus ℝ (Space →L[ℂ] Space) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

/-- The literal constant function in the original finite-volume native Hilbert space. -/
def constantVector : Space := (memLp_const (μ:=measure) (p:=2) (1:ℂ)).toLp (fun _ => 1)

theorem constantVector_coe : (constantVector : UpperHalfPlane → ℂ) =ᵐ[measure] (fun _ => 1) :=
  (memLp_const (μ:=measure) (p:=2) (1:ℂ)).coeFn_toLp

/-- Original smooth modular cutoffs give compact approximants to the constant mode. -/
def constantCore (n : ℕ) : CoreField where
  field := modularCutoff n
  smooth := modularCutoff_smooth n
  invariant := modularCutoff_invariant n
  compact := modularCutoff_compact n

def constantApproxDomain (n : ℕ) : energyOperator.domain :=
  ⟨fieldVector (constantCore n),(constantCore n).mem_energyOperator_domain⟩

theorem constantApproxDomain_coe (n : ℕ) :
    ((constantApproxDomain n : Space) : UpperHalfPlane → ℂ) =ᵐ[measure] modularCutoff n :=
  (core_field_memLp (constantCore n).field (constantCore n).smooth (constantCore n).compact).coeFn_toLp

private def heightProfile (n : ℕ) (y : ℝ) : ℂ := (heightWeight n y : ℂ)

private theorem weight_smooth (n : ℕ) : ContDiff ℝ ∞ (heightWeight n) := smoothWeight_contDiff _ _

private theorem profile_smooth (n : ℕ) : ContDiff ℝ ∞ (heightProfile n) :=
  Complex.ofRealCLM.contDiff.comp (weight_smooth n)

private theorem profile_deriv (n : ℕ) :
    deriv (heightProfile n) = (fun y => ((deriv (heightWeight n) y : ℝ) : ℂ)) := by
  funext y
  exact (((weight_smooth n).differentiable (by simp) y).hasDerivAt.ofReal_comp).deriv

private theorem profile_second (n : ℕ) (y : ℝ) :
    deriv (deriv (heightProfile n)) y = ((iteratedDeriv 2 (heightWeight n) y : ℝ) : ℂ) := by
  rw [profile_deriv,iteratedDeriv_succ,iteratedDeriv_one]
  have hs := (contDiff_infty_iff_deriv.mp (weight_smooth n)).2
  exact ((hs.differentiable (by simp) y).hasDerivAt.ofReal_comp).deriv

/-- The actual constant approximants retain their complete cutoff Laplacian. -/
theorem constantCore_laplacian_on_fd (n : ℕ) (z : UpperHalfPlane) (hz : z ∈ fd) :
    chartLaplacian (constantCore n).field z = cutoffDerivative 2 n z := by
  change chartLaplacian (modularCutoff n) z = _
  rw [chartLaplacian_congr (modularCutoff_germ n z hz)]
  change chartLaplacian (fun w => heightProfile n w.im) z = _
  have he := chartLaplacian_coordinates (fun w : Fin 2 → ℝ => heightProfile n (w 1)) z
  change chartLaplacian (fun w => heightProfile n w.im) z = _ at he
  rw [he,D4BMCuspProjection.height_laplacian _ (profile_smooth n),profile_second]
  simp only [cutoffDerivative,Complex.ofReal_mul,Complex.ofReal_pow]
  rfl

/-- Exact original operator image, including the cutoff error. -/
theorem constantApproxDomain_operator (n : ℕ) :
    energyOperator (constantApproxDomain n) =
      (constantApproxDomain n : Space)-cutoffDerivativeOperator 2 n constantVector := by
  apply Lp.ext
  filter_upwards [(constantCore n).energyOperator_coe,
    Lp.coeFn_sub (constantApproxDomain n : Space) (cutoffDerivativeOperator 2 n constantVector),
    constantApproxDomain_coe n,cutoffDerivativeOperator_coe 2 n constantVector,
    constantVector_coe,ae_restrict_mem isClosed_fd.measurableSet] with z hA hs hc hd h1 hz
  change energyOperator (constantApproxDomain n) z = _ at hA
  simp only [Pi.sub_apply] at hs
  rw [hA,hs,hc,hd,h1,mul_one,constantCore_laplacian_on_fd n z hz]
  rfl

/-- Constant approximants converge in the original native norm. -/
theorem constantApproxDomain_tendsto :
    Tendsto (fun n : ℕ => (constantApproxDomain n : Space)) atTop (𝓝 constantVector) := by
  have hm (n : ℕ) : Measurable (modularCutoff n) :=
    (ChartSmooth.continuous (modularCutoff_smooth n)).measurable
  have h0 : (0:ℝ) ≤ 1 := by norm_num
  have h1 (z : UpperHalfPlane) : ‖(1:ℂ)‖ ≤ (1:ℝ) := by simp
  have hpt (z : UpperHalfPlane) : Tendsto (fun n => modularCutoff n z) atTop (𝓝 (1:ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [modularCutoff_eventually_one z] with n hn
    exact hn.symm
  have ht := tendsto_lpBoundedMulCLM_apply (μ:=measure) hm measurable_const h0
    modularCutoff_norm_le h1 hpt constantVector
  have he (n : ℕ) : lpBoundedMulCLM (p:=2) (μ:=measure) (hm n) h0
      (modularCutoff_norm_le n) constantVector = (constantApproxDomain n : Space) := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p:=2) (μ:=measure) (hm n) h0
      (modularCutoff_norm_le n) constantVector,constantVector_coe,constantApproxDomain_coe n]
      with z hz h1 hc
    rw [hz,h1,hc,mul_one]
  have he1 : lpBoundedMulCLM (p:=2) (μ:=measure) measurable_const h0 h1 constantVector =
      constantVector := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p:=2) (μ:=measure) measurable_const h0 h1 constantVector]
      with z hz
    rw [hz,one_mul]
  simpa only [he,he1] using ht

/-- The cutoff Laplacian vanishes in the original graph limit. -/
theorem constantApproxDomain_operator_tendsto :
    Tendsto (fun n => energyOperator (constantApproxDomain n)) atTop (𝓝 constantVector) := by
  have h := constantApproxDomain_tendsto.sub
    (cutoffDerivativeOperator_tendsto_zero 2 (by norm_num) constantVector)
  simpa only [constantApproxDomain_operator,sub_zero] using h

/-- The actual native covariance fixes the original constant mode. -/
theorem nativeCovariance_constantVector : nativeCovariance constantVector = constantVector := by
  have ht := (nativeCovariance.continuous.tendsto constantVector).comp
    constantApproxDomain_operator_tendsto
  have hb (n : ℕ) : nativeCovariance (energyOperator (constantApproxDomain n)) =
      (constantApproxDomain n : Space) :=
    closedDenseInverse_C_apply nativeCovariance nativeCovariance_injective (constantApproxDomain n)
  exact tendsto_nhds_unique (ht.congr hb) constantApproxDomain_tendsto

/-- The literal constant vector belongs to the full native energy graph. -/
theorem constantVector_mem_energyOperator_domain : constantVector ∈ energyOperator.domain := by
  rw [← nativeCovariance_constantVector]
  exact (closedDenseInverse_apply_C nativeCovariance nativeCovariance_injective constantVector).1

def constantEnergyDomain : energyOperator.domain := ⟨constantVector,constantVector_mem_energyOperator_domain⟩

theorem constantEnergyDomain_operator : energyOperator constantEnergyDomain = constantVector := by
  have h := closedDenseInverse_apply_C nativeCovariance nativeCovariance_injective constantVector
  have he : constantEnergyDomain = ⟨nativeCovariance constantVector,h.1⟩ :=
    Subtype.ext nativeCovariance_constantVector.symm
  rw [he]
  exact h.2

/-- The exact entire transform at the native constant Casimir. -/
theorem casimirTransform_zero : casimirTransform 0 = 1 := by
  have hsqrt : Real.sqrt (1/4:ℝ) = 1/2 := by
    norm_num
  rw [show (0:ℂ)=(0:ℝ) by rfl,casimirTransform_of_le_quarter 0 (by norm_num)]
  have harg : 8*Real.pi*Real.sqrt (1/4-(0:ℝ)) = (2:ℕ)*(2*Real.pi) := by
    rw [sub_zero,hsqrt]
    norm_num
    ring
  rw [harg,Real.cos_nat_mul_two_pi]
  rfl

theorem entireCovarianceSymbol_one : entireCovarianceSymbol 1 = 1/3 := by
  norm_num [entireCovarianceSymbol,casimirTransform_zero]

/-- The actual entire covariance acts on the native constant mode by one third. -/
theorem entireCovariance_constantVector :
    entireCovariance constantVector = (1/3:ℂ) • constantVector := by
  by_cases hv : constantVector=0
  · simp [hv]
  have hs : (1:ℝ) ∈ spectrum ℝ nativeCovariance := by
    rw [spectrum.mem_iff]
    rintro ⟨u,hu⟩
    have hz : (u : Space →L[ℂ] Space) constantVector = 0 := by
      rw [hu]
      simp [nativeCovariance_constantVector]
    have hi := congrArg (fun w : Space => (↑u⁻¹ : Space →L[ℂ] Space) w) hz
    have hm : (↑u⁻¹ : Space →L[ℂ] Space) ((u:Space →L[ℂ] Space) constantVector) =
        constantVector := by
      change ((↑u⁻¹ : Space →L[ℂ] Space)*(u:Space →L[ℂ] Space)) constantVector = _
      simp
    exact hv (by simpa only [hm,map_zero] using hi)
  have he : nativeCovariance constantVector = ((1:ℝ):ℂ) • constantVector := by
    simpa using nativeCovariance_constantVector
  have h := cfc_apply_eigenvector nativeCovariance_selfAdjoint he hs entireCovarianceSymbol
    continuous_entireCovarianceSymbol.continuousOn
  convert h using 1 <;> norm_num [entireCovarianceSymbol_one,entireCovariance]
  rfl

/-- The native constant mode belongs to the entire graph, through its actual covariance range. -/
theorem constantVector_mem_entireOperator_domain : constantVector ∈ entireOperator.domain := by
  have he : entireCovariance ((3:ℂ) • constantVector) = constantVector := by
    rw [map_smul,entireCovariance_constantVector,smul_smul]
    norm_num
  rw [← he]
  exact entireCovariance_mem_domain _

def constantEntireDomain : entireOperator.domain := ⟨constantVector,constantVector_mem_entireOperator_domain⟩

/-- The original constant mode has entire eigenvalue one in the actual closed operator. -/
theorem constantEntireDomain_operator : entireOperator constantEntireDomain = constantVector := by
  have he : entireCovariance ((3:ℂ) • constantVector) = constantVector := by
    rw [map_smul,entireCovariance_constantVector,smul_smul]
    norm_num
  have hd : constantEntireDomain =
      ⟨entireCovariance ((3:ℂ) • constantVector),entireCovariance_mem_domain _⟩ :=
    Subtype.ext he.symm
  rw [hd,entireOperator_apply_covariance,he]
  module

/-- Pairing with the original constant vector is exactly integration in the native measure. -/
theorem inner_constantVector (v : Space) : inner ℂ constantVector v = ∫ z, v z ∂measure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [constantVector_coe] with z hz
  simp [hz]

/-- The actual entire covariance scales every original native mean by one third. -/
theorem integral_entireCovariance (v : Space) :
    (∫ z, (entireCovariance v) z ∂measure) = (1/3:ℂ)*(∫ z, v z ∂measure) := by
  rw [← inner_constantVector,← inner_constantVector]
  have h := entireCovariance_selfAdjoint.isSymmetric constantVector v
  change inner ℂ (entireCovariance constantVector) v = inner ℂ constantVector (entireCovariance v) at h
  rw [entireCovariance_constantVector,inner_smul_left] at h
  have hc : (starRingEnd ℂ) (1/3:ℂ) = (1/3:ℂ) := by
    rw [map_div₀,map_one,map_ofNat]
  rw [hc] at h
  exact h.symm

/-- The exact bounded residual whose vanishing is required for native entire occurrence. -/
def boundedDefect (μ : ℂ) (v : Space) : Space := v-(2+μ) • entireCovariance v

/-- The original mean detects an exact component of every native occurrence residual. -/
theorem integral_boundedDefect (μ : ℂ) (v : Space) :
    (∫ z, (boundedDefect μ v) z ∂measure) =
      ((1-μ)/3)*(∫ z, v z ∂measure) := by
  rw [← inner_constantVector,boundedDefect,inner_sub_right,inner_smul_right,
    inner_constantVector,inner_constantVector,integral_entireCovariance]
  ring

/-- The complete residual has a quantitative lower demand set by its actual native mean. -/
theorem boundedDefect_norm_lower (μ : ℂ) (v : Space) :
    ‖1-μ‖*‖∫ z, v z ∂measure‖ ≤ 3*‖constantVector‖*‖boundedDefect μ v‖ := by
  have h := norm_inner_le_norm (𝕜:=ℂ) constantVector (boundedDefect μ v)
  rw [inner_constantVector,integral_boundedDefect,norm_mul,norm_div] at h
  norm_num at h
  nlinarith

/-- A nonzero native mean excludes zero residual at every target other than one. -/
theorem boundedDefect_ne_zero_of_integral_ne_zero (μ : ℂ) (hμ : μ ≠ 1) (v : Space)
    (hv : (∫ z, v z ∂measure) ≠ 0) : boundedDefect μ v ≠ 0 := by
  intro he
  have h := integral_boundedDefect μ v
  rw [he,integral_congr_ae (Lp.coeFn_zero ℂ 2 measure)] at h
  simp only [Pi.zero_apply,integral_zero] at h
  have hc : (1-μ)/3 ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hμ)) (by norm_num)
  exact (mul_ne_zero hc hv) h.symm

/-- The actual constant component, with its original finite-volume normalization. -/
def constantComponent (v : Space) : Space :=
  (inner ℂ constantVector v / inner ℂ constantVector constantVector) • constantVector

def centered (v : Space) : Space := v-constantComponent v

/-- Removing the actual constant component gives exactly zero native mean. -/
theorem integral_centered (v : Space) : (∫ z, (centered v) z ∂measure) = 0 := by
  rw [← inner_constantVector,centered,constantComponent,inner_sub_right,inner_smul_right]
  by_cases hc : constantVector=0
  · simp [hc]
  · rw [div_mul_cancel₀ _ (inner_self_ne_zero.mpr hc),sub_self]

/-- Centering commutes with the actual entire covariance, preserving the remaining occurrence test. -/
theorem entireCovariance_centered (v : Space) :
    entireCovariance (centered v) = centered (entireCovariance v) := by
  unfold centered constantComponent
  rw [map_sub,map_smul,entireCovariance_constantVector,smul_smul,
    inner_constantVector (entireCovariance v),integral_entireCovariance,inner_constantVector v]
  congr 1
  congr 1
  ring

/-- Exact surviving source decomposition after separating the detected constant obstruction. -/
theorem boundedDefect_decomposition (μ : ℂ) (v : Space) :
    boundedDefect μ v = boundedDefect μ (centered v)+((1-μ)/3) • constantComponent v := by
  unfold boundedDefect centered constantComponent
  rw [map_sub,map_smul,entireCovariance_constantVector]
  module

end
end RHTower.SelbergNativeConstantMode
