import GaloisForLFunctions.HTGeometry.PositiveEvenSchwartzLaplaceEscape
import GaloisForLFunctions.HTGeometry.SchwartzPositiveMeasureRepresentation
import GaloisForLFunctions.HTGeometry.SchwartzPositiveCompactDiagonal
import GaloisForLFunctions.RHTower.STCFlatGapMeasureReaderNoGo

/-!
# Density of positive even Schwartz sources with a prescribed off-axis Laplace zero

Fix `z` with `Re z ≠ 0` and `Im z ≠ 0`.  Every nonnegative even Schwartz function is a Schwartz
limit of strictly positive even Schwartz functions whose bilateral Laplace transform is entire and
vanishes at `z`.

* **Compact approximation.**  The expanding cutoffs `χ_n f` are nonnegative, even and compactly
  supported, hence have entire Laplace transform, and converge to `f` in every Schwartz seminorm.
* **Four remote phases.**  For `a = Re z > 0`, `τ = Im z > 0` and `R = (2π(N+1) + θ)/τ`,
  the packet `g_R` has Laplace value `G(z)(e^{aR} e^{iθ} + e^{-aR} e^{-iθ})`.  The phases
  `θ = 0, π/2, π, -π/2` give the four directions `2G cosh(aR)`, `2iG sinh(aR)`, `-2G cosh(aR)`,
  `-2iG sinh(aR)`, and nonnegative coefficients of size `O(1/cosh(aR))` cancel any prescribed
  Laplace value exactly while the packets tend to zero in the Schwartz topology.

Consequently the positive even entire-Laplace sources that do not vanish at `z` have empty interior,
and no Schwartz-open admission law forces nonvanishing at `z`.  The positive survivor is the
reporter bound `|𝓛_z f| ≤ ∫ e^{a|x|} |f(x)| dx` for `|Re z| ≤ a`.
-/

open Complex MeasureTheory Filter Topology
open scoped SchwartzMap

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PositiveEvenLaplaceEscape

/-! ## The Laplace transform of an entire-Laplace source is entire -/

theorem bilateralLaplace_eq_spectralLaplace (f : ℝ → ℝ) :
    bilateralLaplace f = RHTower.spectralLaplace volume (fun x => (f x : ℂ)) := by
  funext z
  unfold bilateralLaplace RHTower.spectralLaplace
  congr 1
  funext x
  ring

/-- A source with every exponential moment has an entire bilateral Laplace transform. -/
theorem HasEntireLaplace.differentiable {f : ℝ → ℝ} (hf : HasEntireLaplace f) :
    Differentiable ℂ (bilateralLaplace f) := by
  have hmeas : AEStronglyMeasurable (fun x => (f x : ℂ)) volume :=
    (hf 0).aestronglyMeasurable.congr (Eventually.of_forall fun x => by simp)
  have hmom : ∀ c : ℝ, Integrable (fun u => ‖(f u : ℂ)‖ * Real.exp (c * |u|)) volume := by
    intro c
    refine ((hf (c : ℂ)).norm.add (hf ((-c : ℝ) : ℂ)).norm).mono'
      (hmeas.norm.mul (by fun_prop : Continuous fun u : ℝ =>
        Real.exp (c * |u|)).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
    have hle : Real.exp (c * |u|) ≤ Real.exp (c * u) + Real.exp (-c * u) := by
      rcases abs_cases u with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]
        linarith [Real.exp_pos (-c * u)]
      · rw [h, show c * -u = -c * u by ring]
        linarith [Real.exp_pos (c * u)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs]
    calc |f u| * Real.exp (c * |u|) ≤ |f u| * (Real.exp (c * u) + Real.exp (-c * u)) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = Real.exp (c * u) * |f u| + Real.exp (-c * u) * |f u| := by ring
  rw [bilateralLaplace_eq_spectralLaplace]
  exact RHTower.differentiable_spectralLaplace hmeas hmom

/-- A continuous compactly supported source has an entire bilateral Laplace transform. -/
theorem hasEntireLaplace_of_hasCompactSupport {f : ℝ → ℝ} (hc : Continuous f)
    (hs : HasCompactSupport f) : HasEntireLaplace f := fun z =>
  Continuous.integrable_of_hasCompactSupport (by fun_prop)
    (HasCompactSupport.mul_left (f := fun x : ℝ => cexp (z * x))
      (hs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero))

/-! ## Compact positive approximation -/

/-- The real expanding cutoff `χ_n(t) = b(t/(n+1))`, a real Schwartz function. -/
def realScaledCutoff (n : ℕ) : 𝓢(ℝ, ℝ) :=
  SchwartzMap.postcompCLM Complex.reCLM (SchwartzMap.scaledUnitCutoff n)

/-- The unit bump equal to one on `[-1, 1]` and supported in `[-2, 2]`. -/
def unitIntervalBump : ContDiffBump (0 : ℝ) := ⟨|0| + 1, |0| + 2, by positivity, by norm_num⟩

theorem scaledUnitCutoff_eq_bump (n : ℕ) (t : ℝ) :
    SchwartzMap.scaledUnitCutoff n t = ((unitIntervalBump (((n : ℝ) + 1)⁻¹ * t) : ℝ) : ℂ) :=
  rfl

theorem realScaledCutoff_apply (n : ℕ) (t : ℝ) :
    realScaledCutoff n t = unitIntervalBump (((n : ℝ) + 1)⁻¹ * t) := by
  change (SchwartzMap.scaledUnitCutoff n t).re = _
  rw [scaledUnitCutoff_eq_bump, Complex.ofReal_re]

theorem scaledUnitCutoff_eq_ofReal (n : ℕ) (t : ℝ) :
    SchwartzMap.scaledUnitCutoff n t = (realScaledCutoff n t : ℂ) := by
  rw [realScaledCutoff_apply, scaledUnitCutoff_eq_bump]

theorem realScaledCutoff_nonneg (n : ℕ) (t : ℝ) : 0 ≤ realScaledCutoff n t := by
  rw [realScaledCutoff_apply]
  exact unitIntervalBump.nonneg

theorem realScaledCutoff_neg (n : ℕ) (t : ℝ) : realScaledCutoff n (-t) = realScaledCutoff n t := by
  rw [realScaledCutoff_apply, realScaledCutoff_apply, mul_neg, unitIntervalBump.neg]

theorem hasCompactSupport_realScaledCutoff (n : ℕ) : HasCompactSupport (realScaledCutoff n) :=
  (SchwartzMap.scaledUnitCutoff_hasCompactSupport n).comp_left (g := Complex.re) Complex.zero_re

/-- `(EA.16)`  The compact positive approximation `h_n = χ_n f`. -/
def cutoffApprox (n : ℕ) (f : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℝ) :=
  SchwartzMap.smulLeftCLM ℝ (realScaledCutoff n) f

theorem cutoffApprox_apply (n : ℕ) (f : 𝓢(ℝ, ℝ)) (t : ℝ) :
    cutoffApprox n f t = realScaledCutoff n t * f t := by
  rw [cutoffApprox, SchwartzMap.smulLeftCLM_apply_apply (realScaledCutoff n).hasTemperateGrowth,
    smul_eq_mul]

theorem cutoffApprox_nonneg (n : ℕ) {f : 𝓢(ℝ, ℝ)} (hf : ∀ x, 0 ≤ f x) (t : ℝ) :
    0 ≤ cutoffApprox n f t := by
  rw [cutoffApprox_apply]
  exact mul_nonneg (realScaledCutoff_nonneg n t) (hf t)

theorem cutoffApprox_neg (n : ℕ) {f : 𝓢(ℝ, ℝ)} (hf : ∀ x, f (-x) = f x) (t : ℝ) :
    cutoffApprox n f (-t) = cutoffApprox n f t := by
  rw [cutoffApprox_apply, cutoffApprox_apply, realScaledCutoff_neg, hf]

theorem hasEntireLaplace_cutoffApprox (n : ℕ) (f : 𝓢(ℝ, ℝ)) :
    HasEntireLaplace (cutoffApprox n f) := by
  refine hasEntireLaplace_of_hasCompactSupport (cutoffApprox n f).continuous ?_
  have h : ⇑(cutoffApprox n f) = ⇑(realScaledCutoff n) * ⇑f := by
    funext t
    rw [cutoffApprox_apply, Pi.mul_apply]
  rw [h]
  exact (hasCompactSupport_realScaledCutoff n).mul_right

/-- Complexification does not decrease Schwartz seminorms. -/
theorem seminorm_le_seminorm_realToComplexSchwartz (g : 𝓢(ℝ, ℝ)) (k m : ℕ) :
    SchwartzMap.seminorm ℝ k m g ≤
      SchwartzMap.seminorm ℂ k m (SchwartzMap.realToComplexSchwartz g) := by
  refine SchwartzMap.seminorm_le_bound ℝ k m g (apply_nonneg _ _) fun x => ?_
  have h : ‖iteratedFDeriv ℝ m (⇑(SchwartzMap.realToComplexSchwartz g)) x‖ =
      ‖iteratedFDeriv ℝ m g x‖ :=
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left ((g.smooth ⊤).contDiffAt)
      (by exact_mod_cast le_top)
  rw [← h]
  exact SchwartzMap.le_seminorm ℂ k m _ x

theorem realToComplexSchwartz_cutoffApprox_sub (n : ℕ) (f : 𝓢(ℝ, ℝ)) :
    SchwartzMap.realToComplexSchwartz (cutoffApprox n f - f) =
      SchwartzMap.compactSupportApproximation n (SchwartzMap.realToComplexSchwartz f) -
        SchwartzMap.realToComplexSchwartz f := by
  ext t
  simp only [SchwartzMap.realToComplexSchwartz_apply, sub_apply,
    SchwartzMap.compactSupportApproximation_apply, cutoffApprox_apply, scaledUnitCutoff_eq_ofReal]
  push_cast
  ring

/-- `(EA.16)`  `χ_n f → f` in the Schwartz topology. -/
theorem tendsto_cutoffApprox (f : 𝓢(ℝ, ℝ)) :
    Tendsto (fun n => cutoffApprox n f) atTop (𝓝 f) := by
  rw [(schwartz_withSeminorms ℝ ℝ ℝ).tendsto_nhds _ f]
  rintro ⟨k, m⟩ ε hε
  simp only [SchwartzMap.schwartzSeminormFamily_apply]
  filter_upwards [(SchwartzMap.tendsto_compactSupportApproximation_sub_seminorm k m
    (SchwartzMap.realToComplexSchwartz f)).eventually (Iio_mem_nhds hε)] with n hn
  calc SchwartzMap.seminorm ℝ k m (cutoffApprox n f - f)
      ≤ SchwartzMap.seminorm ℂ k m (SchwartzMap.realToComplexSchwartz (cutoffApprox n f - f)) :=
        seminorm_le_seminorm_realToComplexSchwartz _ k m
    _ < ε := by
      rw [realToComplexSchwartz_cutoffApprox_sub]
      exact hn

end GaloisForLFunctions.HTGeometry.PositiveEvenLaplaceEscape
