import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicHalfLineCoercivity
import GaloisForLFunctions.HTGeometry.HardyBoundary.LogarithmicMomentCompactness
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation

/-!
# Compactness of soft logarithmic Rayleigh sublevels

Coercivity controls physical first moments and positive logarithmic Fourier
moments on every unit energy sublevel. Their uniform tails give compact
closure in ordinary L², without a common exponential-moment bound.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open _root_.RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

/-- The unit Rayleigh sublevel of the exponential trial class, represented in ordinary L². -/
def softLogarithmicRayleighSublevel (E : ℝ) : Set SoninL2 :=
  {v | ∃ (F : ℝ → ℝ) (hF : SoftLogarithmicHalfLineDomain F),
    (∫ u, F u ^ 2) = 1 ∧ softLogarithmicHalfLineEnergy F ≤ E ∧
      v = hF.memLp_complex.toLp (cx F)}

/-- Literal physical and Fourier moments transfer to the L² representative of a trial. -/
theorem SoftLogarithmicHalfLineDomain.sublevel_bounds_of_L2_representative {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) (hm : (∫ u, F u ^ 2) = 1)
    {E : ℝ} (hE : softLogarithmicHalfLineEnergy F ≤ E)
    (v : SoninL2) (hv : (v : ℝ → ℂ) =ᵐ[volume] cx F) :
    ‖v‖ ≤ 1 ∧
      (Integrable (fun u : ℝ => |u| * ‖v u‖ ^ 2) ∧
        (∫ u, |u| * ‖v u‖ ^ 2) ≤ (E + 16) / 4) ∧
      (Integrable (suzukiHlogDensity v) ∧ suzukiHlogMoment v ≤ E + 17) := by
  have hmc : (∫ u, ‖cx F u‖ ^ 2) = 1 := by
    simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hm
  have hnorm : ‖v‖ ^ 2 = 1 := by
    calc
      _ = ∫ u, ‖v u‖ ^ 2 := _root_.RHTower.norm_sq_eq_integral v
      _ = ∫ u, ‖cx F u‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hv] with u hu
        exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hu
      _ = 1 := hmc
  have hfirst : Integrable (fun u : ℝ => |u| * ‖v u‖ ^ 2) := by
    apply hF.integrable_absMoment.congr
    filter_upwards [hv] with u hu
    exact congrArg (fun z : ℂ => |u| * ‖z‖ ^ 2) hu.symm
  have hmoment : (∫ u, |u| * ‖v u‖ ^ 2) = criticalHalfLineFirstMoment F := by
    calc
      _ = ∫ u, |u| * ‖cx F u‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hv] with u hu
        exact congrArg (fun z : ℂ => |u| * ‖z‖ ^ 2) hu
      _ = _ := hF.integral_absMoment
  have hv1 : Integrable (v : ℝ → ℂ) := (hF.integrable.ofReal (𝕜 := ℂ)).congr hv.symm
  have hfourier : (fourierUnitary v : ℝ → ℂ) =ᵐ[volume] 𝓕 (cx F) := by
    have he := coeFn_fourierTransform_eq_fourierIntegral v hv1
    change (fourierUnitary v : ℝ → ℂ) =ᵐ[volume] 𝓕 (v : ℝ → ℂ) at he
    exact he.trans (Eventually.of_forall fun ξ => Real.fourier_congr_ae hv ξ)
  have hplain := _root_.RHTower.integrable_norm_sq_fourier (f := cx F) (hF.integrable.ofReal (𝕜 := ℂ))
    hF.memLp_complex
  have hpositive := hF.integrable_positiveLogarithm
  have hparts : suzukiHlogDensity v =ᵐ[volume]
      (fun ξ => ‖𝓕 (cx F) ξ‖ ^ 2 + max (Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2) := by
    filter_upwards [hfourier] with ξ hξ
    change (1 + max (Real.log |ξ|) 0) * ‖fourierUnitary v ξ‖ ^ 2 = _
    rw [hξ]
    ring
  have hlog : Integrable (suzukiHlogDensity v) := (hplain.add hpositive).congr hparts.symm
  have hlogmoment : suzukiHlogMoment v =
      1 + ∫ ξ, max (Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2 := by
    calc
      _ = ∫ ξ, ‖𝓕 (cx F) ξ‖ ^ 2 + max (Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2 :=
        integral_congr_ae hparts
      _ = (∫ ξ, ‖𝓕 (cx F) ξ‖ ^ 2) +
          ∫ ξ, max (Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2 := integral_add hplain hpositive
      _ = _ := by
        rw [_root_.RHTower.integral_norm_sq_fourier_eq (f := cx F) (hF.integrable.ofReal (𝕜 := ℂ))
          hF.memLp_complex, hmc]
  obtain ⟨hphysical, hspectral⟩ := hF.sublevel_bounds hm hE
  refine ⟨?_, ⟨hfirst, ?_⟩, ⟨hlog, ?_⟩⟩
  · nlinarith only [hnorm, norm_nonneg v]
  · rw [hmoment]
    linarith only [hphysical]
  · rw [hlogmoment]
    linarith only [hspectral]

/-- Every unit Rayleigh sublevel of the soft logarithmic half-line trial class is precompact. -/
theorem isCompact_closure_softLogarithmicRayleighSublevel (E : ℝ) :
    IsCompact (closure (softLogarithmicRayleighSublevel E)) := by
  apply isCompact_closure_of_firstMoment_and_logMoment
    (softLogarithmicRayleighSublevel E) (B := 1) (M := (E + 16) / 4) (L := E + 17)
  · rintro v ⟨F, hF, hm, hE, he⟩
    have hv : (v : ℝ → ℂ) =ᵐ[volume] cx F := by
      rw [he]
      exact hF.memLp_complex.coeFn_toLp
    exact (hF.sublevel_bounds_of_L2_representative hm hE v hv).1
  · rintro v ⟨F, hF, hm, hE, he⟩
    have hv : (v : ℝ → ℂ) =ᵐ[volume] cx F := by
      rw [he]
      exact hF.memLp_complex.coeFn_toLp
    exact (hF.sublevel_bounds_of_L2_representative hm hE v hv).2.1
  · rintro v ⟨F, hF, hm, hE, he⟩
    have hv : (v : ℝ → ℂ) =ᵐ[volume] cx F := by
      rw [he]
      exact hF.memLp_complex.coeFn_toLp
    exact (hF.sublevel_bounds_of_L2_representative hm hE v hv).2.2

#print axioms SoftLogarithmicHalfLineDomain.sublevel_bounds_of_L2_representative
#print axioms isCompact_closure_softLogarithmicRayleighSublevel
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
