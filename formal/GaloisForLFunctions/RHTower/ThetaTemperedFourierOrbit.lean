import GaloisForLFunctions.RHTower.ThetaTemperedSourceJets
import GaloisForLFunctions.HTGeometry.SchwartzTranslation
import GaloisForLFunctions.HTGeometry.FlowTemperedGrowth
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
Literal physical Fourier translation, genuine inverse on tempered functionals,
and real-parameter continuity of Schwartz modulation. The physical transform
uses the positive exponent; right translation therefore gives a negative phase.
-/

open MeasureTheory FourierTransform Filter
open scoped SchwartzMap Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Right translation gives the literal negative phase for the original physical transform. -/
theorem thetaPhysicalFourierCLE_translateCLM_apply
    (a : ℝ) (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    thetaPhysicalFourierCLE (SchwartzMap.translateCLM ℂ a φ) t =
      modulation a t * thetaPhysicalFourierCLE φ t := by
  let c : ℂ := Complex.I * (t : ℂ)
  have hw : modulation a t = Complex.exp (-(c * (a : ℂ))) := by
    unfold modulation cexpLin
    congr 1
    dsimp [c]
    ring
  rw [hw, thetaPhysicalFourierCLE_apply_eq_integral,
    thetaPhysicalFourierCLE_apply_eq_integral]
  change (∫ x : ℝ, Complex.exp (c * (x : ℂ)) * φ (x + a)) =
    Complex.exp (-(c * (a : ℂ))) * ∫ x : ℝ, Complex.exp (c * (x : ℂ)) * φ x
  calc
    _ = ∫ x : ℝ, Complex.exp (-(c * (a : ℂ))) *
        (Complex.exp (c * ((x + a : ℝ) : ℂ)) * φ (x + a)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← mul_assoc, ← Complex.exp_add]
      congr 1
      congr 1
      push_cast
      ring
    _ = ∫ x : ℝ, Complex.exp (-(c * (a : ℂ))) *
        (Complex.exp (c * (x : ℂ)) * φ x) :=
      integral_add_right_eq_self (μ := volume)
        (fun x : ℝ => Complex.exp (-(c * (a : ℂ))) *
          (Complex.exp (c * (x : ℂ)) * φ x)) a
    _ = _ := integral_const_mul _ _

/-- Genuine inverse precomposition on the actual pointwise tempered dual. -/
def thetaPhysicalTemperedInversePullback : 𝓢'(ℝ, ℂ) →L[ℂ] 𝓢'(ℝ, ℂ) :=
  PointwiseConvergenceCLM.precomp ℂ thetaPhysicalFourierCLE.symm.toContinuousLinearMap

theorem thetaPhysicalTemperedInversePullback_apply (T : 𝓢'(ℝ, ℂ)) (φ : 𝓢(ℝ, ℂ)) :
    thetaPhysicalTemperedInversePullback T φ = T (thetaPhysicalFourierCLE.symm φ) := rfl

theorem thetaPhysicalTemperedInversePullback_pullback (T : 𝓢'(ℝ, ℂ)) :
    thetaPhysicalTemperedInversePullback (thetaPhysicalTemperedPullback T) = T := by
  ext φ
  change T (thetaPhysicalFourierCLE (thetaPhysicalFourierCLE.symm φ)) = T φ
  exact congrArg T (thetaPhysicalFourierCLE.apply_symm_apply φ)

theorem thetaPhysicalTemperedPullback_inversePullback (T : 𝓢'(ℝ, ℂ)) :
    thetaPhysicalTemperedPullback (thetaPhysicalTemperedInversePullback T) = T := by
  ext φ
  change T (thetaPhysicalFourierCLE.symm (thetaPhysicalFourierCLE φ)) = T φ
  exact congrArg T (thetaPhysicalFourierCLE.symm_apply_apply φ)

/-- The original physical tempered pullback with its actual continuous inverse. -/
def thetaPhysicalTemperedCLE : 𝓢'(ℝ, ℂ) ≃L[ℂ] 𝓢'(ℝ, ℂ) :=
  ContinuousLinearEquiv.equivOfInverse thetaPhysicalTemperedPullback
    thetaPhysicalTemperedInversePullback thetaPhysicalTemperedInversePullback_pullback
    thetaPhysicalTemperedPullback_inversePullback

theorem thetaPhysicalTemperedCLE_apply (T : 𝓢'(ℝ, ℂ)) :
    thetaPhysicalTemperedCLE T = thetaPhysicalTemperedPullback T := rfl

theorem thetaPhysicalTemperedCLE_symm_apply (T : 𝓢'(ℝ, ℂ)) :
    thetaPhysicalTemperedCLE.symm T = thetaPhysicalTemperedInversePullback T := rfl

theorem thetaPhysicalTemperedPullback_surjective :
    Function.Surjective thetaPhysicalTemperedPullback := by
  intro T
  exact ⟨thetaPhysicalTemperedInversePullback T, thetaPhysicalTemperedPullback_inversePullback T⟩

/-- Genuine Schwartz modulation obtained from the original physical Fourier equivalence. -/
def thetaPhysicalModulationCLM (a : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  thetaPhysicalFourierCLE.toContinuousLinearMap.comp
    ((SchwartzMap.translateCLM ℂ a).comp thetaPhysicalFourierCLE.symm.toContinuousLinearMap)

theorem thetaPhysicalModulationCLM_apply (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    thetaPhysicalModulationCLM a ψ t = modulation a t * ψ t := by
  change thetaPhysicalFourierCLE
    (SchwartzMap.translateCLM ℂ a (thetaPhysicalFourierCLE.symm ψ)) t = _
  rw [thetaPhysicalFourierCLE_translateCLM_apply, thetaPhysicalFourierCLE.apply_symm_apply]

theorem thetaPhysicalModulationCLM_continuous (ψ : 𝓢(ℝ, ℂ)) :
    Continuous (fun a : ℝ => thetaPhysicalModulationCLM a ψ) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  have hshift : Tendsto (fun b : ℝ => b - a) (𝓝 a) (𝓝 0) := by
    simpa only [id_eq, sub_self] using (continuousAt_id (x := a)).sub_const a
  have htranslate : Tendsto
      (fun b : ℝ => SchwartzMap.translateCLM ℂ b (thetaPhysicalFourierCLE.symm ψ))
      (𝓝 a) (𝓝 (SchwartzMap.translateCLM ℂ a (thetaPhysicalFourierCLE.symm ψ))) := by
    have h := (SchwartzMap.tendsto_translateCLM_add_zero
      (thetaPhysicalFourierCLE.symm ψ) a).comp hshift
    change Tendsto
      (fun b : ℝ => SchwartzMap.translateCLM ℂ (a + (b - a))
        (thetaPhysicalFourierCLE.symm ψ))
      (𝓝 a) (𝓝 (SchwartzMap.translateCLM ℂ a (thetaPhysicalFourierCLE.symm ψ))) at h
    have hparameter (b : ℝ) : a + (b - a) = b := by ring
    simpa only [hparameter] using h
  change Tendsto
    (fun b : ℝ => thetaPhysicalFourierCLE
      (SchwartzMap.translateCLM ℂ b (thetaPhysicalFourierCLE.symm ψ)))
    (𝓝 a) (𝓝 (thetaPhysicalFourierCLE
      (SchwartzMap.translateCLM ℂ a (thetaPhysicalFourierCLE.symm ψ))))
  exact (thetaPhysicalFourierCLE.continuous.tendsto _).comp htranslate

theorem thetaRealModulation_hasTemperateGrowth (a : ℝ) :
    Function.HasTemperateGrowth (modulation a) := by
  refine ⟨contDiff_modulation a, ?_⟩
  intro n
  refine ⟨0, |a| ^ n, ?_⟩
  intro t
  rw [norm_iteratedFDeriv_modulation, pow_zero, mul_one]

theorem thetaPhysicalModulationCLM_eq_smulLeftCLM (a : ℝ) :
    thetaPhysicalModulationCLM a = SchwartzMap.smulLeftCLM ℂ (modulation a) := by
  ext ψ t
  rw [thetaPhysicalModulationCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (thetaRealModulation_hasTemperateGrowth a)]
  rfl

/-- The exact scalar inverse integral for the original physical normalization. -/
theorem thetaPhysicalFourierCLE_symm_apply_eq_integral (ψ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    thetaPhysicalFourierCLE.symm ψ t =
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ a : ℝ, modulation a t * ψ a := by
  change (𝓕⁻ (thetaPhysicalFrequencyCompositionCLE.symm ψ)) t = _
  calc
    _ = ∫ ξ : ℝ, modulation (-(2 * Real.pi) * ξ) t * ψ (-(2 * Real.pi) * ξ) := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards [] with ξ
      change Complex.exp (((2 * Real.pi * inner ℝ ξ t : ℝ) : ℂ) * Complex.I) *
        ψ (-(2 * Real.pi) * ξ) = _
      unfold modulation cexpLin
      congr 1
      congr 1
      simp only [RCLike.inner_apply]
      simp
      ring
    _ = |(-(2 * Real.pi))⁻¹| • ∫ a : ℝ, modulation a t * ψ a :=
      Measure.integral_comp_mul_left (fun a : ℝ => modulation a t * ψ a) (-(2 * Real.pi))
    _ = _ := by
      rw [abs_inv, abs_neg, abs_of_pos (by positivity), Algebra.smul_def]
      rfl

theorem thetaPhysicalFourierCLE_inversion (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    φ t = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ a : ℝ, modulation a t * thetaPhysicalFourierCLE φ a := by
  have h := thetaPhysicalFourierCLE_symm_apply_eq_integral (thetaPhysicalFourierCLE φ) t
  rw [thetaPhysicalFourierCLE.symm_apply_apply] at h
  exact h

end RHTower
