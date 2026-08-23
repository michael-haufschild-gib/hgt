import GaloisForLFunctions.HTGeometry.NearZeroTruncatedPower
import GaloisForLFunctions.RHTower.SoninKernelPairing

/-!
# Burnol's correction kernel pairs to zero against a Sonine vector

The correction term of Burnol's kernel, `E_a(u,s) = ∫_0^a e^{2πiut} t^{-s} dt`, is the conjugated
Fourier transform of `1_{(0,a)} t^{-s̄}`, an honest `L²` function when `Re s < 1/2`.  Pairing it
against the Fourier transform of a Sonine vector `f ∈ K_a` therefore returns, by Plancherel, the
integral `∫_0^a t^{-s} f(t) dt` — which vanishes because `f` **vanishes on the band**.

This is the step that removes the correction from Burnol's kernel identity and leaves the pure
`χ`-factor (arXiv:math/0203120, Thm. 2.1).

## Main results

* `inner_nearZeroPowerVector`
* `integral_nearZeroKernel_mul_fourier_eq_zero`
-/

noncomputable section

open MeasureTheory Set Complex Real Filter Topology FourierTransform
open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The near-origin truncated power, as a vector of `L²(ℝ)`. -/
def nearZeroPowerVector (a : ℝ) {s : ℂ} (hs : s.re < 1 / 2) : SoninL2 :=
  (memLp_two_truncPower_zero (a := a) (s := (starRingEnd ℂ) s)
    (by rwa [Complex.conj_re])).toLp _

theorem inner_nearZeroPowerVector (a : ℝ) {s : ℂ} (hs : s.re < 1 / 2) (f : SoninL2) :
    ⟪nearZeroPowerVector a hs, f⟫_ℂ
      = ∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
  rw [MeasureTheory.L2.inner_def]
  have hcoe := (memLp_two_truncPower_zero (a := a) (s := (starRingEnd ℂ) s)
    (by rwa [Complex.conj_re] : ((starRingEnd ℂ) s).re < 1 / 2)).coeFn_toLp
  rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with u hu
  have hWu : ((nearZeroPowerVector a hs : SoninL2) : ℝ → ℂ) u
      = truncPower 0 a ((starRingEnd ℂ) s) u := by
    simp only [nearZeroPowerVector]
    exact hu
  have hlhs : (starRingEnd ℂ) (((nearZeroPowerVector a hs : SoninL2) : ℝ → ℂ) u)
      = (Set.Ioo (0 : ℝ) a).indicator (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s)) u := by
    rw [hWu, truncPower]
    by_cases hmem : u ∈ Set.Ioo (0 : ℝ) a
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
        conj_ofReal_cpow_neg hmem.1 s]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, map_zero]
  rw [RCLike.inner_apply, hlhs]
  by_cases hmem : u ∈ Set.Ioo (0 : ℝ) a
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    ring
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    ring

theorem coeFn_fourierUnitary_nearZeroPowerVector {a : ℝ} (ha : 0 ≤ a) {s : ℂ}
    (hs : s.re < 1 / 2) :
    ∀ᵐ u ∂(volume : Measure ℝ),
      ((fourierUnitary (nearZeroPowerVector a hs) : SoninL2) : ℝ → ℂ) u
        = 𝓕 (truncPower 0 a ((starRingEnd ℂ) s)) u := by
  have hcs : ((starRingEnd ℂ) s).re < 1 / 2 := by rwa [Complex.conj_re]
  have hcs1 : ((starRingEnd ℂ) s).re < 1 := by
    rw [Complex.conj_re]
    linarith
  set W : SoninL2 := nearZeroPowerVector a hs with hW
  have hae : ((W : SoninL2) : ℝ → ℂ) =ᵐ[volume] truncPower 0 a ((starRingEnd ℂ) s) := by
    simpa [hW, nearZeroPowerVector] using (memLp_two_truncPower_zero (a := a) hcs).coeFn_toLp
  have hWint : Integrable ((W : SoninL2) : ℝ → ℂ) volume :=
    (integrable_truncPower_zero ha hcs1).congr hae.symm
  have hbridge := l2_fourier_coeFn_eq_l1_fourier_of_integrable W hWint
  filter_upwards [hbridge] with u hu
  have h1 : ((fourierUnitary W : SoninL2) : ℝ → ℂ) u = ((𝓕 W : SoninL2) : ℝ → ℂ) u := rfl
  rw [h1, hu, fourierTransform_toLp]
  exact (Real.fourier_congr_ae hae) u

/-- **The near-zero kernel pairs against the Fourier transform as the near-zero Mellin
integral.**  No Sonine hypothesis: this is Plancherel for the truncated power on `(0,a)`. -/
theorem integral_nearZeroKernel_mul_fourier_eq {a : ℝ} (ha : 0 < a) (f : SoninL2)
    {s : ℂ} (hs : s.re < 1 / 2) :
    ∫ u : ℝ, (∫ t in (0 : ℝ)..a, ((t : ℝ) : ℂ) ^ (-s)
        * Complex.exp ((t * (2 * Real.pi * u) : ℝ) * Complex.I))
      * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u
      = ∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
  set W : SoninL2 := nearZeroPowerVector a hs with hW
  have hplanch : ⟪W, f⟫_ℂ = ⟪fourierUnitary W, fourierUnitary f⟫_ℂ :=
    (fourierUnitary.inner_map_map W f).symm
  have hval : ⟪W, f⟫_ℂ
      = ∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
    rw [hW, inner_nearZeroPowerVector a hs f]
  rw [hplanch, MeasureTheory.L2.inner_def] at hval
  rw [← hval]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_fourierUnitary_nearZeroPowerVector (a := a) ha.le hs] with u hu
  rw [RCLike.inner_apply, hu, ← conj_fourierIntegral_truncPower (le_refl (0 : ℝ)) ha.le s u]
  ring

/-- **The correction term pairs to zero.** -/
theorem integral_nearZeroKernel_mul_fourier_eq_zero {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) {s : ℂ} (hs : s.re < 1 / 2) :
    ∫ u : ℝ, (∫ t in (0 : ℝ)..a, ((t : ℝ) : ℂ) ^ (-s)
        * Complex.exp ((t * (2 * Real.pi * u) : ℝ) * Complex.I))
      * ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = 0 := by
  rw [integral_nearZeroKernel_mul_fourier_eq ha f hs]
  have hsupp := physical_indicator_ae_zero_of_mem_centralSoninCarrier hf
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0 := by
    filter_upwards [hsupp] with t ht hmem
    simpa [Set.indicator_of_mem hmem] using ht
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  have hband : t ∈ centralInterval a := by
    rw [centralInterval, Set.mem_Icc]
    exact ⟨by linarith [hmem.1, ha], le_of_lt hmem.2⟩
  rw [ht hband, mul_zero]
  rfl

end RHTower
