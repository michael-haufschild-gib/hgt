import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransform
import GaloisForLFunctions.HTGeometry.CausalFourierBridge

/-!
# The Plancherel pairing on the line

The sesquilinear duality of the Fourier transform, together with Fourier inversion, gives the
Plancherel pairing in the explicit integral form

`∫ 𝓕f · conj(𝓕ψ) = ∫ f · conj ψ`,

for an integrable `f` and a continuous integrable `ψ` with integrable transform.  This is the step
that converts a symbol pairing on the frequency side into a pairing of the source functions
themselves.
-/

open MeasureTheory FourierTransform Real VectorFourier

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The sesquilinear duality of the Fourier transform on the line. -/
theorem sesq_fourier_pairing {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ : ℝ, (starRingEnd ℂ) (𝓕 f ξ) * g ξ)
      = ∫ x : ℝ, (starRingEnd ℂ) (f x) * 𝓕⁻ g x := by
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (V := ℝ) (W := ℝ) (E := ℂ) (F := ℂ) (G := ℂ)
    (e := Real.fourierChar) (μ := volume) (ν := volume)
    (L := innerₗ ℝ) (innerSL ℂ)
    Real.continuous_fourierChar continuous_inner hf hg
  have hflip : ((innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ)).flip = innerₗ ℝ := by
    ext
    simp
  rw [hflip] at h
  calc (∫ ξ : ℝ, (starRingEnd ℂ) (𝓕 f ξ) * g ξ)
      = ∫ ξ : ℝ, (innerSL ℂ) (𝓕 f ξ) (g ξ) := by
        refine integral_congr_ae ?_
        filter_upwards with ξ
        simp [RCLike.inner_apply, mul_comm]
    _ = ∫ x : ℝ, (innerSL ℂ) (f x) (𝓕⁻ g x) := h
    _ = ∫ x : ℝ, (starRingEnd ℂ) (f x) * 𝓕⁻ g x := by
        refine integral_congr_ae ?_
        filter_upwards with x
        simp [RCLike.inner_apply, mul_comm]

/-- **The Plancherel pairing.** -/
theorem plancherel_pairing {f ψ : ℝ → ℂ} (hf : Integrable f) (hψ : Integrable ψ)
    (hFψ : Integrable (𝓕 ψ)) (hψc : Continuous ψ) :
    (∫ ξ : ℝ, 𝓕 f ξ * (starRingEnd ℂ) (𝓕 ψ ξ))
      = ∫ x : ℝ, f x * (starRingEnd ℂ) (ψ x) := by
  have hinv : 𝓕⁻ (𝓕 ψ) = ψ := hψc.fourierInv_fourier_eq hψ hFψ
  have h := sesq_fourier_pairing hf hFψ
  rw [hinv] at h
  have hconj := congrArg (starRingEnd ℂ) h
  rw [← integral_conj, ← integral_conj] at hconj
  calc (∫ ξ : ℝ, 𝓕 f ξ * (starRingEnd ℂ) (𝓕 ψ ξ))
      = ∫ ξ : ℝ, (starRingEnd ℂ) ((starRingEnd ℂ) (𝓕 f ξ) * 𝓕 ψ ξ) := by
        refine integral_congr_ae ?_
        filter_upwards with ξ
        simp [map_mul]
    _ = ∫ x : ℝ, (starRingEnd ℂ) ((starRingEnd ℂ) (f x) * ψ x) := hconj
    _ = ∫ x : ℝ, f x * (starRingEnd ℂ) (ψ x) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        simp [map_mul]

/-! ## The resolvent pairing is a causal pair form -/

open scoped Convolution

/-- **The resolvent pairing.**  Pairing a source against a reader through one right-half-plane
resolvent is the pairing of the causally smoothed source against the reader. -/
theorem resolvent_pairing_eq_causalPair {a : ℝ} (ha : 0 < a) {φ ψ : ℝ → ℂ}
    (hφ : Integrable φ) (hψ : Integrable ψ) (hFψ : Integrable (𝓕 ψ)) (hψc : Continuous ψ) :
    (∫ ξ : ℝ, ((a : ℂ) + 2 * Complex.I * ξ)⁻¹ * 𝓕 φ ξ * (starRingEnd ℂ) (𝓕 ψ ξ))
      = ∫ t : ℝ, (RHTower.causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] φ) t
          * (starRingEnd ℂ) (ψ t) := by
  have hea : Integrable (RHTower.causalFourierExponential a) :=
    RHTower.causalFourierExponential_integrable ha
  have hconv : Integrable (RHTower.causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] φ) :=
    Integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hea hφ
  have hstep : ∀ ξ : ℝ, ((a : ℂ) + 2 * Complex.I * ξ)⁻¹ * 𝓕 φ ξ
      = 𝓕 (RHTower.causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] φ) ξ := by
    intro ξ
    rw [RHTower.fourier_mul_convolution_eq_of_integrable hea hφ ξ,
      RHTower.fourier_causalFourierExponential ha]
  calc (∫ ξ : ℝ, ((a : ℂ) + 2 * Complex.I * ξ)⁻¹ * 𝓕 φ ξ * (starRingEnd ℂ) (𝓕 ψ ξ))
      = ∫ ξ : ℝ, 𝓕 (RHTower.causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] φ) ξ
          * (starRingEnd ℂ) (𝓕 ψ ξ) := by
        refine integral_congr_ae ?_
        filter_upwards with ξ
        rw [hstep ξ]
    _ = ∫ t : ℝ, (RHTower.causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] φ) t
          * (starRingEnd ℂ) (ψ t) := plancherel_pairing hconv hψ hFψ hψc

/-! ## Restricting to the causal core -/

theorem causalFourierExponential_zero_of_nonpos {a u : ℝ} (hu : u ≤ 0) :
    RHTower.causalFourierExponential a u = 0 := by
  rw [RHTower.causalFourierExponential]
  exact Set.indicator_of_notMem (by simpa using not_lt.mpr hu) _

/-- The causal convolution is a half-line integral. -/
theorem convolution_eq_setIntegral_Ioi (a : ℝ) (φ : ℝ → ℂ) (t : ℝ) :
    (RHTower.causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] φ) t
      = ∫ u in Set.Ioi (0:ℝ), RHTower.causalFourierExponential a u * φ (t - u) := by
  rw [MeasureTheory.convolution_def]
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro u hu
  have hu0 : u ≤ 0 := not_lt.mp (by simpa using hu)
  simp [causalFourierExponential_zero_of_nonpos hu0]

/-- With a strictly anticausal source the half-line integral starts at the reader position. -/
theorem convolution_eq_setIntegral_shift {a : ℝ} {φ : ℝ → ℂ}
    (hφ0 : ∀ s : ℝ, 0 ≤ s → φ s = 0) {t : ℝ} (ht : 0 < t) :
    (RHTower.causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] φ) t
      = ∫ u in Set.Ioi t, RHTower.causalFourierExponential a u * φ (t - u) := by
  rw [convolution_eq_setIntegral_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioi]
  congr 1
  funext u
  by_cases h1 : u ∈ Set.Ioi t
  · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (Set.Ioi_subset_Ioi ht.le h1)]
  · rw [Set.indicator_of_notMem h1]
    by_cases h2 : u ∈ Set.Ioi (0:ℝ)
    · rw [Set.indicator_of_mem h2]
      have hut : u ≤ t := not_lt.mp (by simpa using h1)
      simp [hφ0 _ (by linarith : (0:ℝ) ≤ t - u)]
    · rw [Set.indicator_of_notMem h2]

/-- **The causal pair form is the Hankel form.**  Translating by the reader position turns the
half-line convolution into the sum-kernel pairing. -/
theorem setIntegral_shift_eq_hankel (a : ℝ) (φ : ℝ → ℂ) (t : ℝ) :
    (∫ u in Set.Ioi t, RHTower.causalFourierExponential a u * φ (t - u))
      = ∫ v in Set.Ioi (0:ℝ), RHTower.causalFourierExponential a (t + v) * φ (-v) := by
  have hmp : MeasureTheory.MeasurePreserving (fun v : ℝ => t + v) volume volume :=
    MeasureTheory.measurePreserving_add_left volume t
  have hemb : MeasurableEmbedding (fun v : ℝ => t + v) :=
    (Homeomorph.addLeft t).measurableEmbedding
  have hpre : (fun v : ℝ => t + v) ⁻¹' Set.Ioi t = Set.Ioi (0:ℝ) := by
    ext v
    simp
  have h := hmp.setIntegral_preimage_emb hemb
    (fun u : ℝ => RHTower.causalFourierExponential a u * φ (t - u)) (Set.Ioi t)
  rw [hpre] at h
  rw [← h]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
  congr 2
  ring

/-! ## The resolvent pairing is the Hankel form -/

/-- **The resolvent pairing is a Hankel form.**  On a core of strictly anticausal sources and
strictly causal readers, pairing through a right-half-plane resolvent is exactly the rank-one
Hankel pairing in the sum variable. -/
theorem resolvent_pairing_eq_hankelForm {a : ℝ} (ha : 0 < a) {φ ψ : ℝ → ℂ}
    (hφ : Integrable φ) (hψ : Integrable ψ) (hFψ : Integrable (𝓕 ψ)) (hψc : Continuous ψ)
    (hφ0 : ∀ s : ℝ, 0 ≤ s → φ s = 0) (hψ0 : ∀ t : ℝ, t ≤ 0 → ψ t = 0) :
    (∫ ξ : ℝ, ((a : ℂ) + 2 * Complex.I * ξ)⁻¹ * 𝓕 φ ξ * (starRingEnd ℂ) (𝓕 ψ ξ))
      = ∫ t in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
          RHTower.causalFourierExponential a (t + v) * φ (-v) * (starRingEnd ℂ) (ψ t) := by
  rw [resolvent_pairing_eq_causalPair ha hφ hψ hFψ hψc]
  have houter : (∫ t : ℝ, (RHTower.causalFourierExponential a
        ⋆[ContinuousLinearMap.mul ℂ ℂ] φ) t * (starRingEnd ℂ) (ψ t))
      = ∫ t in Set.Ioi (0:ℝ), (RHTower.causalFourierExponential a
        ⋆[ContinuousLinearMap.mul ℂ ℂ] φ) t * (starRingEnd ℂ) (ψ t) := by
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro t ht
    have ht0 : t ≤ 0 := not_lt.mp (by simpa using ht)
    simp [hψ0 t ht0]
  rw [houter]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [convolution_eq_setIntegral_shift hφ0 ht0, setIntegral_shift_eq_hankel,
    ← MeasureTheory.integral_mul_const]

end GaloisForLFunctions.HTGeometry
