import GaloisForLFunctions.RHTower.WeilWorkExposingRaySeparatorExtension
import GaloisForLFunctions.RHTower.WeilPositivityRegularPerturbationRigidity
import GaloisForLFunctions.RHTower.DigammaVerticalLogGrowth
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Actual source estimates for weighted exact-fibre recovery

Every compact complex C2 source has integrable density against
`1 + log(2 + |t|)^beta` for `0 <= beta <= 1`. Actual polar multiplicative
resonators obey a uniform mass-times-log-power budget, derived from the
proved gamma bound and the scalar concavity tangent. Zero Fourier mass
requires no division or separate positivity premise.

Actual far-polar corrections converge in this weighted L1 norm, with an
explicit error factor tending to zero. They cancel both poles but do not
preserve integer atoms. The arithmetic averaging and exact-fibre assembly
are separate outstanding steps; no WP02 energy lower bound is asserted.

Paper: docs/reports/weil-work/results/02-exposing-ray/SUBHALF-LOG-FIBRE-PROOF.md.
-/

open MeasureTheory Filter Topology Set Complex Zeta23
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilSpectral WeilOneSided

/-- Spectral weight for the sublogarithmic recovery problem. -/
def logSpectralWeight (β τ : ℝ) : ℝ := 1 + Real.log (2+|τ|)^β

private theorem log_pos (τ : ℝ) : 0 < Real.log (2+|τ|) :=
  Real.log_pos (by linarith [abs_nonneg τ])

private theorem continuous_logWeight (β : ℝ) : Continuous (logSpectralWeight β) := by
  unfold logSpectralWeight
  exact continuous_const.add (((continuous_const.add continuous_abs).log
    (fun τ => (show 0 < 2+|τ| by positivity).ne')).rpow_const (fun τ => Or.inl (log_pos τ).ne'))

private theorem rpow_le_one_add {β x : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hx : 0 ≤ x) : x^β ≤ 1+x := by
  have h := rpow_one_add_le_one_add_mul_self (s := x-1) (by linarith) hβ hβ1
  rw [show 1+(x-1)=x by ring] at h
  have hm := mul_le_mul_of_nonneg_right hβ1 hx
  nlinarith

private theorem weight_linear_bound {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (τ : ℝ) :
    |logSpectralWeight β τ| ≤ 3*(1+|τ|) := by
  have hl := log_pos τ
  have hp := Real.rpow_nonneg hl.le β
  rw [abs_of_nonneg (by unfold logSpectralWeight; positivity)]
  have h := rpow_le_one_add hβ hβ1 hl.le
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 2+|τ|)
  unfold logSpectralWeight
  linarith [abs_nonneg τ]

private theorem source_aperture {f : ℝ → ℂ} (hs : HasCompactSupport f) :
    ∃ a : ℝ, tsupport f ⊆ Icc (-a) a := by
  obtain ⟨a, ha⟩ := exists_abs_bound_of_hasCompactSupport hs
  exact ⟨a, closure_minimal (fun x hx => abs_le.mp (ha x hx)) isClosed_Icc⟩

/-- Every actual source has a finite sublogarithmic weighted spectral mass. -/
theorem integrable_logWeighted_density {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (f : WeilTestFn) :
    Integrable (fun τ : ℝ => ‖paperFT f.1 τ‖^2*logSpectralWeight β τ) := by
  obtain ⟨a, ha⟩ := source_aperture f.2.2
  exact integrable_normSq_paperFT_mul_of_linear f.2.1 ha (continuous_logWeight β)
    (weight_linear_bound hβ hβ1)

private theorem integrable_log_density (f : WeilTestFn) :
    Integrable (fun τ : ℝ => ‖paperFT f.1 τ‖^2*Real.log (2+|τ|)) := by
  obtain ⟨a, ha⟩ := source_aperture f.2.2
  apply integrable_normSq_paperFT_mul_of_linear f.2.1 ha
    ((continuous_const.add continuous_abs).log (fun τ => (show 0 < 2+|τ| by positivity).ne')) (Mp := 1)
  intro τ
  change |Real.log (2+|τ|)| ≤ 1*(1+|τ|)
  rw [abs_of_pos (log_pos τ), one_mul]
  have := Real.log_le_sub_one_of_pos (by positivity : 0 < 2+|τ|)
  linarith

private theorem integrable_rpow_log_density {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (f : WeilTestFn) :
    Integrable (fun τ : ℝ => ‖paperFT f.1 τ‖^2*Real.log (2+|τ|)^β) := by
  obtain ⟨a, ha⟩ := source_aperture f.2.2
  have h := (integrable_logWeighted_density hβ hβ1 f).sub
    (integrable_normSq_paperFT f.2.1 ha)
  convert h using 1
  ext τ
  simp only [Pi.sub_apply, logSpectralWeight]
  ring

private theorem concave_power_tangent {β x H : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hx : 0 ≤ x) (hH : 0 < H) :
    x^β ≤ ((1-β)*H^β)+(β*H^β/H)*x := by
  have h := rpow_one_add_le_one_add_mul_self (s := x/H-1)
    (by linarith [div_nonneg hx hH.le]) hβ hβ1
  rw [show 1+(x/H-1)=x/H by ring, Real.div_rpow hx hH.le] at h
  have hp := Real.rpow_pos_of_pos hH β
  have hh := (div_le_iff₀ hp).mp h
  calc x^β ≤ (1+β*(x/H-1))*H^β := hh
    _ = _ := by ring

private theorem integral_rpow_log_le {β H : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hH : 0 < H) (f : WeilTestFn)
    (hb : (∫ τ : ℝ, ‖paperFT f.1 τ‖^2*Real.log (2+|τ|)) ≤
      H*(∫ τ : ℝ, ‖paperFT f.1 τ‖^2)) :
    (∫ τ : ℝ, ‖paperFT f.1 τ‖^2*Real.log (2+|τ|)^β) ≤
      H^β*(∫ τ : ℝ, ‖paperFT f.1 τ‖^2) := by
  obtain ⟨a, ha⟩ := source_aperture f.2.2
  have i0 := integrable_normSq_paperFT f.2.1 ha
  have i1 := integrable_log_density f
  let A := (1-β)*H^β
  let B := β*H^β/H
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (τ : ℝ) : ‖paperFT f.1 τ‖^2*Real.log (2+|τ|)^β ≤
      A*‖paperFT f.1 τ‖^2+B*(‖paperFT f.1 τ‖^2*Real.log (2+|τ|)) := by
    have h := mul_le_mul_of_nonneg_left
      (concave_power_tangent hβ hβ1 (log_pos τ).le hH) (sq_nonneg ‖paperFT f.1 τ‖)
    calc
      _ ≤ ‖paperFT f.1 τ‖^2*(((1-β)*H^β)+(β*H^β/H)*Real.log (2+|τ|)) := h
      _ = _ := by dsimp [A,B]; ring
  calc _ ≤ ∫ τ : ℝ, A*‖paperFT f.1 τ‖^2+B*(‖paperFT f.1 τ‖^2*Real.log (2+|τ|)) :=
      integral_mono (integrable_rpow_log_density hβ hβ1 f)
        ((i0.const_mul A).add (i1.const_mul B)) hpoint
    _ = A*(∫ τ : ℝ, ‖paperFT f.1 τ‖^2)+
        B*(∫ τ : ℝ, ‖paperFT f.1 τ‖^2*Real.log (2+|τ|)) := by
      rw [integral_add (i0.const_mul A) (i1.const_mul B), integral_const_mul,
        integral_const_mul]
    _ ≤ A*(∫ τ : ℝ, ‖paperFT f.1 τ‖^2)+
        B*(H*(∫ τ : ℝ, ‖paperFT f.1 τ‖^2)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hb hB)
    _ = _ := by dsimp [A,B]; field_simp; ring

private def logGammaConstant : ℝ :=
  digammaVerticalCoercivityConst (1/4)+Real.log 2+Real.log Real.pi

private theorem log_le_gamma_add (τ : ℝ) :
    Real.log (2+|τ|) ≤ archimedeanWeilSymbol (τ/(2*Real.pi))+logGammaConstant := by
  have hd := re_digamma_vertical_ge (a := 1/4) (by norm_num) (by norm_num) (τ/2)
  have hl : Real.log (2+|τ|) ≤ Real.log 2+Real.log (2+|τ/2|) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [abs_nonneg τ]
  rw [archimedeanWeilSymbol_eq]
  have he : Real.pi*(τ/(2*Real.pi))=τ/2 := by field_simp
  rw [he]
  dsimp [logGammaConstant]
  linarith

/-- Uniform source constant in the weighted resonator budget. -/
def sublogResonatorConstant : ℝ :=
  |WeilWorkPBAP.resonatorGammaConstant+logGammaConstant|+1

theorem one_le_sublogResonatorConstant : 1 ≤ sublogResonatorConstant := by
  unfold sublogResonatorConstant
  linarith [abs_nonneg (WeilWorkPBAP.resonatorGammaConstant+logGammaConstant)]

/-- Actual polar resonators have a logarithmic-power weighted mass budget.
No coefficient-growth or energy-positivity premise is used. -/
theorem resonator_logWeighted_mass_bound {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℂ) (hc : ∀ m, N < m → c m = 0) :
    (∫ τ : ℝ, ‖paperFT (resonator N c (1/((N:ℝ)+1))) τ‖^2 * logSpectralWeight β τ) ≤
      (2*Real.pi*WeilWorkPBAP.resonatorMass N*∑ m ∈ Finset.Icc 1 N, ‖c m‖^2)*
        (1+(Real.log N+sublogResonatorConstant)^β) := by
  let f : WeilTestFn := ⟨resonator N c (1/((N:ℝ)+1)), contDiff_resonator _ _ _ 2,
    WeilWorkPBAP.hasCompactSupport_resonator c (by positivity)⟩
  obtain ⟨a,ha⟩ := source_aperture f.2.2
  have i0 := integrable_normSq_paperFT f.2.1 ha
  have iA := integrable_normSq_paperFT_mul_arch f.2.1 ha
  have hm := (WeilWorkPBAP.resonator_fourier_mass_and_arch_bound hN c hc).1
  have hA := (WeilWorkPBAP.resonator_fourier_mass_and_arch_bound hN c hc).2
  let M := ∫ τ : ℝ, ‖paperFT f.1 τ‖^2
  have hM : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  have hAm : (∫ τ : ℝ, ‖paperFT f.1 τ‖^2*archimedeanWeilSymbol (τ/(2*Real.pi))) ≤
      M*(Real.log N+WeilWorkPBAP.resonatorGammaConstant) := by
    change _ ≤ (∫ τ : ℝ, ‖paperFT (resonator N c (1/((N:ℝ)+1))) τ‖^2)*_
    rw [hm]
    convert hA using 1; ring
  have hC : WeilWorkPBAP.resonatorGammaConstant+logGammaConstant ≤ sublogResonatorConstant := by
    exact (le_abs_self _).trans (by unfold sublogResonatorConstant; linarith)
  have hH : 0 < Real.log (N:ℝ)+sublogResonatorConstant := by
    have hn := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN)
    unfold sublogResonatorConstant
    linarith [abs_nonneg (WeilWorkPBAP.resonatorGammaConstant+logGammaConstant)]
  have hlog : (∫ τ : ℝ, ‖paperFT f.1 τ‖^2*Real.log (2+|τ|)) ≤
      (Real.log N+sublogResonatorConstant)*M := by
    calc
      _ ≤ (∫ τ : ℝ, ‖paperFT f.1 τ‖^2*archimedeanWeilSymbol (τ/(2*Real.pi))+
          logGammaConstant*‖paperFT f.1 τ‖^2) := by
        apply integral_mono (integrable_log_density f) (iA.add (i0.const_mul _))
        intro τ
        have h := mul_le_mul_of_nonneg_left (log_le_gamma_add τ) (sq_nonneg ‖paperFT f.1 τ‖)
        simp only [Pi.add_apply]
        nlinarith only [h]
      _ = (∫ τ : ℝ, ‖paperFT f.1 τ‖^2*archimedeanWeilSymbol (τ/(2*Real.pi)))+
          logGammaConstant*M := by rw [integral_add iA (i0.const_mul _), integral_const_mul]
      _ ≤ M*(Real.log N+WeilWorkPBAP.resonatorGammaConstant)+logGammaConstant*M :=
        add_le_add hAm le_rfl
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hC hM]
  have hp := integral_rpow_log_le hβ hβ1 hH f hlog
  have ie : (∫ τ : ℝ, ‖paperFT f.1 τ‖^2*logSpectralWeight β τ) =
      M+(∫ τ : ℝ, ‖paperFT f.1 τ‖^2*Real.log (2+|τ|)^β) := by
    simp only [logSpectralWeight, mul_add, mul_one]
    exact integral_add i0 (integrable_rpow_log_density hβ hβ1 f)
  change (∫ τ : ℝ, ‖paperFT f.1 τ‖^2*logSpectralWeight β τ) ≤ _
  rw [ie, ← hm]
  change M+_ ≤ M*(1+_)
  nlinarith

/-- Actual weighted density represented in ordinary real L1. -/
def logDensityL1 {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (f : WeilTestFn) :
    Lp ℝ 1 (volume : Measure ℝ) :=
  (integrable_logWeighted_density hβ hβ1 f).toL1
    (fun τ : ℝ => ‖paperFT f.1 τ‖^2*logSpectralWeight β τ)

theorem norm_logDensityL1 {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (f : WeilTestFn) :
    ‖logDensityL1 hβ hβ1 f‖ =
      ∫ τ : ℝ, ‖paperFT f.1 τ‖^2*logSpectralWeight β τ := by
  rw [logDensityL1, L1.norm_of_fun_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [] with τ
  rw [Real.norm_eq_abs, abs_of_nonneg]
  unfold logSpectralWeight
  have hp := Real.rpow_nonneg (log_pos τ).le β
  positivity

private theorem weighted_density_error_pointwise {β : ℝ} (f : WeilTestFn) (X τ : ℝ) :
    |‖paperFT (farTest X f).1 τ‖^2*logSpectralWeight β τ-
      ‖paperFT f.1 τ‖^2*logSpectralWeight β τ| ≤
      (2*farPolarCoeff X+farPolarCoeff X^2)*
        (‖paperFT f.1 τ‖^2*logSpectralWeight β τ) := by
  have he : ‖paperFT (farTest X f).1 τ‖^2 =
      ‖paperFT f.1 τ‖^2*(1-farPolarCoeff X*Real.cos (X*τ))^2 := by
    change ‖paperFT (farSource X f.1) τ‖^2 = _
    rw [paperFT_farSource f.2.1.continuous f.2.2, norm_mul, mul_pow]
    congr 1
    have hc : 1-(farPolarCoeff X : ℂ)*Complex.cos ((X : ℂ)*τ) =
        ((1-farPolarCoeff X*Real.cos (X*τ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_cos]; push_cast; rfl
    rw [hc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hr := farPolarCoeff_nonneg X
  let z := farPolarCoeff X*Real.cos (X*τ)
  have hz : |z| ≤ farPolarCoeff X := by
    dsimp [z]; rw [abs_mul, abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hr).trans_eq (mul_one _)
  have hz' := abs_le.mp hz
  have hzz : z^2 ≤ farPolarCoeff X^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz'.2) (show 0 ≤ farPolarCoeff X+z by linarith)]
  have hfactor : |(1-z)^2-1| ≤ 2*farPolarCoeff X+farPolarCoeff X^2 := by
    apply abs_le.mpr; constructor <;> nlinarith [sq_nonneg z]
  have hw : 0 ≤ ‖paperFT f.1 τ‖^2*logSpectralWeight β τ := by
    unfold logSpectralWeight
    have hp := Real.rpow_nonneg (log_pos τ).le β
    positivity
  rw [he]
  change |‖paperFT f.1 τ‖^2*(1-z)^2*logSpectralWeight β τ-
    ‖paperFT f.1 τ‖^2*logSpectralWeight β τ| ≤ _
  rw [show ‖paperFT f.1 τ‖^2*(1-z)^2*logSpectralWeight β τ-
      ‖paperFT f.1 τ‖^2*logSpectralWeight β τ =
      (‖paperFT f.1 τ‖^2*logSpectralWeight β τ)*((1-z)^2-1) by ring,
    abs_mul, abs_of_nonneg hw]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hfactor hw

/-- Quantitative weighted convergence of actual far-polar corrections. -/
theorem norm_logDensityL1_farTest_sub_le {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (f : WeilTestFn) (X : ℝ) :
    ‖logDensityL1 hβ hβ1 (farTest X f)-logDensityL1 hβ hβ1 f‖ ≤
      (2*farPolarCoeff X+farPolarCoeff X^2)*‖logDensityL1 hβ hβ1 f‖ := by
  conv_rhs => rw [norm_logDensityL1]
  rw [logDensityL1, logDensityL1, ← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [← integral_const_mul]
  exact integral_mono ((integrable_logWeighted_density hβ hβ1 (farTest X f)).sub
    (integrable_logWeighted_density hβ hβ1 f)).abs
    ((integrable_logWeighted_density hβ hβ1 f).const_mul _)
    (weighted_density_error_pointwise f X)

/-- Both pole zeros can be imposed with vanishing weighted spectral error.
Arithmetic trace preservation still requires the separate fibre argument. -/
theorem tendsto_logDensityL1_farTest {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (f : WeilTestFn) :
    Tendsto (fun X : ℝ => logDensityL1 hβ hβ1 (farTest X f)) atTop
      (𝓝 (logDensityL1 hβ hβ1 f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he : Tendsto (fun X : ℝ => (2*farPolarCoeff X+farPolarCoeff X^2)*
      ‖logDensityL1 hβ hβ1 f‖) atTop (𝓝 0) := by
    simpa using ((tendsto_farPolarCoeff.const_mul 2).add (tendsto_farPolarCoeff.pow 2)).mul_const
      ‖logDensityL1 hβ hβ1 f‖
  exact squeeze_zero (fun _ => norm_nonneg _)
    (norm_logDensityL1_farTest_sub_le hβ hβ1 f) he

end RHTower.ExposingRayTransfer
