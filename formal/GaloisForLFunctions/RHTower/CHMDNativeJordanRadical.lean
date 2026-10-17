import GaloisForLFunctions.RHTower.CHMDNativeJordanSamples
import GaloisForLFunctions.RHTower.PaperThetaConfluentNativeRegularity
import GaloisForLFunctions.RHTower.CHMDFullSpectralNullspace
import GaloisForLFunctions.RHTower.ThetaBVArithmeticAdmission

/-!
# The exact arithmetic radical of finite native Jordan packets

Every finite native packet supplies its literal real and imaginary BV graph
vectors. Their joint Xi samples vanish exactly on the lower Jordan layers.
Subtracting the actual polar plane therefore identifies the same coefficient
kernel with the full signed arithmetic radical. The prime edges and both
polar terms remain in the unprojected energy identity.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex Zeta23
open scoped BoundedContinuousFunction Classical ComplexConjugate

namespace RHTower.CHMDDoobGraph

theorem polarResidual_fourier_at_zero (p : SourceGraph) {z : ℂ} (hz : XiC z = 0) :
    graphFourierReadout (polarResidual p) z = graphFourierReadout p z := by
  have hs := (abs_im_lt_half_of_XiC_eq_zero hz).le
  rw [← graphFourierReadoutCLM_apply _ hs, polarResidual, map_sub, map_sub,
    map_smul, map_smul, graphFourierReadoutCLM_apply, graphFourierReadoutCLM_apply,
    graphFourierReadoutCLM_apply, ground_mem_fullSpectralNullspace z hz,
    oddPolarVector_mem_fullSpectralNullspace z hz]
  simp

theorem polarResidual_mem_signedRadical_iff (p : SourceGraph) :
    polarResidual p ∈ signedRadical ↔ p ∈ fullSpectralNullspace := by
  constructor
  · intro hr z hz
    rw [← polarResidual_fourier_at_zero p hz]
    exact radical_graphFourierReadout_zero hr hz
  · exact polarResidual_mem_signedRadical

end RHTower.CHMDDoobGraph

namespace RHTower.PaperThetaEndpoint
open CHMDDoobGraph HedenmalmThetaSource HedenmalmQuantile
open GaloisForLFunctions.HTGeometry

def nativeBVComponentGraph (f : NativeContinuousSpace) (hf : BoundedVariationOn f univ)
    (L : ℂ →L[ℝ] ℝ) : SourceGraph :=
  bvLift (fun x => L (f x)) (L.lipschitz.comp_boundedVariationOn hf)

theorem nativeBVComponentGraph_source (f : NativeContinuousSpace)
    (hf : BoundedVariationOn f univ) (L : ℂ →L[ℝ] ℝ) :
    (nativeBVComponentGraph f hf L).val.fst =ᵐ[massMeasure] fun x => L (f x) :=
  bvLift_source _ _

theorem integrable_native_component (f : NativeContinuousSpace) (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    Integrable (fun x => flatCharDensity z x * (L (f x) : ℂ)) := by
  apply (integrable_flatCharDensity_all z).mul_bdd (by fun_prop)
  refine Eventually.of_forall fun x => ?_
  calc
    ‖(L (f x) : ℂ)‖ = ‖L (f x)‖ := Complex.norm_real _
    _ ≤ ‖L‖*‖f x‖ := L.le_opNorm _
    _ ≤ ‖L‖*‖f‖ := mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)

/-- Literal graph Fourier readout, with the theta normalization restored. -/
theorem nativeBVComponentGraph_fourier (f : NativeContinuousSpace)
    (hf : BoundedVariationOn f univ) (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    graphFourierReadout (nativeBVComponentGraph f hf L) z =
      (thetaSource.mass : ℂ) * ∫ x, flatCharDensity z x * (L (f x) : ℂ) := by
  rw [graphFourierReadout, paperFT, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [volume_absolutelyContinuous_mass.ae_eq (nativeBVComponentGraph_source f hf L)]
    with x hx
  rw [phiDoobTest, hx, flatCharDensity, sourceChar, PositiveDensitySource.normalized,
    thetaSource_k, thetaCuspFullSource_eq_riemannKernelReal]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero]

/-- Both real graph components together retain the complete complex native transform. -/
theorem nativeBVComponentGraph_complex_sample (f : NativeContinuousSpace)
    (hf : BoundedVariationOn f univ) (z : ℂ) :
    graphFourierReadout (nativeBVComponentGraph f hf Complex.reCLM) z +
      I * graphFourierReadout (nativeBVComponentGraph f hf Complex.imCLM) z =
      (thetaSource.mass : ℂ) * boundedThetaMomentCLM z f := by
  rw [nativeBVComponentGraph_fourier, nativeBVComponentGraph_fourier]
  have hi := integrable_native_component f Complex.imCLM z
  have hr := integrable_native_component f Complex.reCLM z
  change Integrable (fun x => flatCharDensity z x * ((f x).im : ℂ)) at hi
  change Integrable (fun x => flatCharDensity z x * ((f x).re : ℂ)) at hr
  have hsplit : (∫ x, flatCharDensity z x * ((f x).re : ℂ)) +
      I * (∫ x, flatCharDensity z x * ((f x).im : ℂ)) = boundedThetaMomentCLM z f := by
    rw [← integral_const_mul, ← integral_add hr (hi.const_mul I)]
    change (∫ x, flatCharDensity z x * ((f x).re : ℂ) +
      I * (flatCharDensity z x * ((f x).im : ℂ))) = ∫ x, flatCharDensity z x * f x
    apply integral_congr_ae
    filter_upwards [] with x
    linear_combination flatCharDensity z x * (Complex.re_add_im (f x))
  change (thetaSource.mass : ℂ) * (∫ x, flatCharDensity z x * ((f x).re : ℂ)) +
    I * ((thetaSource.mass : ℂ) * (∫ x, flatCharDensity z x * ((f x).im : ℂ))) = _
  linear_combination (thetaSource.mass : ℂ) * hsplit

theorem nativeBVComponents_Xi_silent_iff (f : NativeContinuousSpace)
    (hf : BoundedVariationOn f univ) :
    (nativeBVComponentGraph f hf Complex.reCLM ∈ fullSpectralNullspace ∧
      nativeBVComponentGraph f hf Complex.imCLM ∈ fullSpectralNullspace) ↔
      ∀ z : ℂ, XiC z = 0 → boundedThetaMomentCLM z f = 0 := by
  constructor
  · rintro ⟨hr, hi⟩ z hz
    have he := nativeBVComponentGraph_complex_sample f hf z
    rw [hr z hz, hi z hz, mul_zero, add_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left
      (Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero)
  · intro h
    have hs : ∀ z : ℂ, XiC z = 0 →
        graphFourierReadout (nativeBVComponentGraph f hf Complex.reCLM) z = 0 ∧
        graphFourierReadout (nativeBVComponentGraph f hf Complex.imCLM) z = 0 := by
      intro z hz
      have hp := nativeBVComponentGraph_complex_sample f hf z
      rw [h z hz, mul_zero] at hp
      have hnc : XiC (-conj z) = 0 := by rw [XiC_even, XiC_conj, hz, map_zero]
      have hm := nativeBVComponentGraph_complex_sample f hf (-conj z)
      rw [h _ hnc, mul_zero, ← conj_graphFourierReadout, ← conj_graphFourierReadout] at hm
      have hc := congrArg conj hm
      simp only [map_add, map_mul, conj_conj, Complex.conj_I, map_zero] at hc
      constructor
      · linear_combination (1/2 : ℂ)*hp + (1/2 : ℂ)*hc
      · have hi : I * graphFourierReadout (nativeBVComponentGraph f hf Complex.imCLM) z = 0 := by
          linear_combination (1/2 : ℂ)*hp - (1/2 : ℂ)*hc
        exact (mul_eq_zero.mp hi).resolve_left (by norm_num)
    exact ⟨fun z hz => (hs z hz).1, fun z hz => (hs z hz).2⟩

def nativeFiniteComponentGraph (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) (L : ℂ →L[ℝ] ℝ) : SourceGraph :=
  nativeBVComponentGraph (nativeFiniteSynthesis S c) (nativeFiniteSynthesis_bv S c) L

theorem nativeFiniteComponents_Xi_silent_iff_terminal_zero (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    (nativeFiniteComponentGraph S c Complex.reCLM ∈ fullSpectralNullspace ∧
      nativeFiniteComponentGraph S c Complex.imCLM ∈ fullSpectralNullspace) ↔
      ∀ rho : ↥S, c ⟨rho, nativeTerminalJetIndex rho.val⟩ = 0 :=
  (nativeBVComponents_Xi_silent_iff _ _).trans
    (nativeFiniteSynthesis_Xi_silent_iff_terminal_zero S c)

/-- Exact arithmetic classification: the polar-corrected packet loses precisely its lower layers. -/
theorem nativeFinite_polarResidual_radical_iff_terminal_zero (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    (polarResidual (nativeFiniteComponentGraph S c Complex.reCLM) ∈ signedRadical ∧
      polarResidual (nativeFiniteComponentGraph S c Complex.imCLM) ∈ signedRadical) ↔
      ∀ rho : ↥S, c ⟨rho, nativeTerminalJetIndex rho.val⟩ = 0 := by
  rw [polarResidual_mem_signedRadical_iff, polarResidual_mem_signedRadical_iff]
  exact nativeFiniteComponents_Xi_silent_iff_terminal_zero S c

/-- All mixed signed arithmetic pairings vanish on the lower-layer packet after pole subtraction. -/
theorem nativeFinite_lower_pairings (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S)
    (hc : ∀ rho : ↥S, c ⟨rho, nativeTerminalJetIndex rho.val⟩ = 0) (q : SourceGraph) :
    sourcePair (polarResidual (nativeFiniteComponentGraph S c Complex.reCLM)) q = 0 ∧
      sourcePair (polarResidual (nativeFiniteComponentGraph S c Complex.imCLM)) q = 0 := by
  obtain ⟨hr, hi⟩ := (nativeFinite_polarResidual_radical_iff_terminal_zero S c).mpr hc
  exact ⟨hr q, hi q⟩

theorem nativeFinite_lower_polarResidual_energy (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S)
    (hc : ∀ rho : ↥S, c ⟨rho, nativeTerminalJetIndex rho.val⟩ = 0) :
    sourceEnergy (polarResidual (nativeFiniteComponentGraph S c Complex.reCLM)) = 0 ∧
      sourceEnergy (polarResidual (nativeFiniteComponentGraph S c Complex.imCLM)) = 0 := by
  obtain ⟨hr, hi⟩ := (nativeFinite_polarResidual_radical_iff_terminal_zero S c).mpr hc
  exact ⟨by rw [← sourcePair_self]; exact hr _, by rw [← sourcePair_self]; exact hi _⟩

/-- The original, unprojected signed source keeps exactly its two polar contributions. -/
theorem nativeFinite_lower_source_energy (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S)
    (hc : ∀ rho : ↥S, c ⟨rho, nativeTerminalJetIndex rho.val⟩ = 0)
    (L : ℂ →L[ℝ] ℝ) (hL : L = Complex.reCLM ∨ L = Complex.imCLM) :
    phiDoobArchJumpEnergy (fun x => L (nativeFiniteSynthesis S c x)) +
      (∑' n, ∫ x, phiDoobPrimeJump (fun y => L (nativeFiniteSynthesis S c y)) n x) -
      phiDoobCoshMass (fun x => L (nativeFiniteSynthesis S c x)^2) =
      -2 * polarCosine (nativeFiniteComponentGraph S c L)^2 +
        2 * polarSine (nativeFiniteComponentGraph S c L)^2 := by
  have hs := (nativeFiniteComponents_Xi_silent_iff_terminal_zero S c).mpr hc
  have hp : nativeFiniteComponentGraph S c L ∈ fullSpectralNullspace := by
    rcases hL with rfl | rfl
    · exact hs.1
    · exact hs.2
  have he := full_nullspace_energy hp
  rw [nativeFiniteComponentGraph, nativeBVComponentGraph, sourceEnergy_bvLift] at he
  exact he

end RHTower.PaperThetaEndpoint
