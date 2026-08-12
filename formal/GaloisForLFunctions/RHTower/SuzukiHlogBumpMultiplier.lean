import GaloisForLFunctions.RHTower.SuzukiHlogInwardFormCore
import GaloisForLFunctions.HTGeometry.BumpMollifierFamily
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity
import Mathlib.Analysis.Fourier.Convolution

/-!
# Shrinking bump multipliers in Suzuki's logarithmic Fourier space

The normalized compactly supported bump of width `ε` has Fourier transform bounded by one.  As
`ε → 0`, these Fourier transforms converge pointwise to one.  Dominated multiplier continuity then
upgrades this to strong convergence on the exact weighted space
`L²(ℝ, (1 + log⁺ |ξ|) dξ)`.

This is the spectral half of the mollification step in Connes--Consani (2021), Lemma `core`.  The
result is genuinely weighted; ordinary Plancherel convergence would not control the source form
norm.
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped Convolution

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Complexification of the normalized real bump of width `ε`. -/
def complexBumpMollifier {ε : ℝ} (hε : 0 < ε) (x : ℝ) : ℂ :=
  bumpMollifier hε x

theorem integrable_complexBumpMollifier {ε : ℝ} (hε : 0 < ε) :
    Integrable (complexBumpMollifier hε) :=
  (integrable_bumpMollifier hε).ofReal

theorem contDiff_complexBumpMollifier {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (complexBumpMollifier hε) := by
  exact Complex.ofRealCLM.contDiff.comp ((widthBump hε).contDiff_normed (n := ⊤))

theorem hasCompactSupport_complexBumpMollifier {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (complexBumpMollifier hε) := by
  exact HasCompactSupport.comp_left (hasCompactSupport_bumpMollifier hε)
    Complex.ofReal_zero

/-- The normalized bump Fourier symbol is contractive. -/
theorem norm_fourier_complexBumpMollifier_le_one {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) :
    ‖𝓕 (complexBumpMollifier hε) ξ‖ ≤ 1 := by
  calc
    ‖𝓕 (complexBumpMollifier hε) ξ‖ ≤
        ∫ x : ℝ, ‖complexBumpMollifier hε x‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ = ∫ x : ℝ, bumpMollifier hε x := by
      congr with x
      rw [show complexBumpMollifier hε x = (bumpMollifier hε x : ℂ) by rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nonneg_bumpMollifier hε x)]
    _ = 1 := integral_bumpMollifier hε

theorem measurable_fourier_complexBumpMollifier {ε : ℝ} (hε : 0 < ε) :
    Measurable (𝓕 (complexBumpMollifier hε)) :=
  (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) (integrable_complexBumpMollifier hε)).measurable

/-- Shrinking normalized bumps have Fourier transforms converging pointwise to one. -/
theorem tendsto_fourier_complexBumpMollifier_one
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n)
    (hε : Tendsto ε atTop (nhds 0)) (ξ : ℝ) :
    Tendsto (fun n => 𝓕 (complexBumpMollifier (hεpos n)) ξ) atTop (nhds 1) := by
  let g : ℝ → ℂ := fun x => (𝐞 (x * ξ) : ℂ)
  have hg : Continuous g := by fun_prop
  have hconv := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (φ := fun n => widthBump (hεpos n)) hε hg 0
  convert hconv using 1
  · ext n
    rw [Real.fourier_real_eq, MeasureTheory.convolution_def]
    congr with x
    simp only [complexBumpMollifier, bumpMollifier, g, zero_sub,
      ContinuousLinearMap.lsmul_apply, Circle.smul_def]
    change (𝐞 (-(x * ξ)) : ℂ) * (bumpMollifier (hεpos n) x : ℂ) =
      (bumpMollifier (hεpos n) x : ℂ) * (𝐞 (-x * ξ) : ℂ)
    calc
      _ = (bumpMollifier (hεpos n) x : ℂ) * (𝐞 (-(x * ξ)) : ℂ) := mul_comm _ _
      _ = _ := by ring_nf
  · simp [g]

/-- The shrinking-bump Fourier multiplier on Suzuki's weighted Fourier Hilbert space. -/
def suzukiHlogBumpFourierMul {ε : ℝ} (hε : 0 < ε) :
    SuzukiHlogFourierL2 →L[ℂ] SuzukiHlogFourierL2 :=
  lpBoundedMulCLM (p := 2) (μ := suzukiHlogMeasure)
    (measurable_fourier_complexBumpMollifier hε) zero_le_one
    (norm_fourier_complexBumpMollifier_le_one hε)

/-- Multiplication by shrinking-bump Fourier symbols converges strongly in Suzuki's exact weighted
form norm. -/
theorem suzukiHlogBumpFourierMul_tendsto
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n)
    (hε : Tendsto ε atTop (nhds 0)) (f : SuzukiHlogFourierL2) :
    Tendsto (fun n => suzukiHlogBumpFourierMul (hεpos n) f) atTop (nhds f) := by
  have h := tendsto_lpBoundedMulCLM_apply
    (μ := suzukiHlogMeasure)
    (fun n => measurable_fourier_complexBumpMollifier (hεpos n)) measurable_const
    zero_le_one
    (fun n => norm_fourier_complexBumpMollifier_le_one (hεpos n))
    (fun _ => by simp)
    (fun ξ => tendsto_fourier_complexBumpMollifier_one hεpos hε ξ) f
  have hone : lpBoundedMulCLM (p := 2) (μ := suzukiHlogMeasure)
      (measurable_const : Measurable (fun _ : ℝ => (1 : ℂ)))
      zero_le_one (fun _ => by simp) =
      ContinuousLinearMap.id ℂ SuzukiHlogFourierL2 := by
    apply lpBoundedMulCLM_eq_id
    filter_upwards with x
    rfl
  rw [hone] at h
  exact h

end RHTower
