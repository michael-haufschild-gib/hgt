import GaloisForLFunctions.RHTower.ThetaWienerHopfTransgression
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1
import GaloisForLFunctions.HTGeometry.EntireZeroSetNull

/-!
# The retarded half-line transgression is injective

Zero-extending a half-line datum turns the retarded transgression into an ordinary convolution, so
its Fourier transform is the pointwise product of the kernel transform and the datum transform.  A
kernel whose transform is nonzero almost everywhere therefore has injective transgression: this is
the multiplier half of the boundary-wall theorem, and it applies to the theta kernel because its
transform is an entire function whose real zero set is null.

* `RHTower.halfLineConvMinus_eq_convolution`;
* `RHTower.eq_zero_of_halfLineConvMinus_eq_zero`;
* `RHTower.eq_zero_of_halfLineConvMinus_eq_zero_of_entire`.
-/

noncomputable section

open MeasureTheory Set Filter Convolution ContinuousLinearMap
open scoped FourierTransform Topology

namespace RHTower

/-- On a datum vanishing to the left of the origin the retarded transgression is the ordinary
convolution. -/
theorem halfLineConvMinus_eq_convolution {k g : ℝ → ℂ} (hsupp : ∀ L : ℝ, L ≤ 0 → g L = 0)
    (x : ℝ) :
    halfLineConvMinus k g x = (k ⋆[ContinuousLinearMap.mul ℂ ℂ, (volume : Measure ℝ)] g) x := by
  have h1 : halfLineConvMinus k g x = ∫ L : ℝ, k (x - L) * g L := by
    rw [halfLineConvMinus_eq_lineConv]
    refine integral_congr_ae (.of_forall fun L => ?_)
    by_cases hL : L ∈ Ioi (0 : ℝ)
    · show k (x - L) * zeroExtend g L = k (x - L) * g L
      rw [zeroExtend, Set.indicator_of_mem hL]
    · show k (x - L) * zeroExtend g L = k (x - L) * g L
      rw [zeroExtend, Set.indicator_of_notMem hL, hsupp L (by simpa using hL)]
  have h2 := integral_sub_left_eq_self (fun t : ℝ => k t * g (x - t)) (volume : Measure ℝ) x
  have h3 : ∀ L : ℝ, (fun t : ℝ => k t * g (x - t)) (x - L) = k (x - L) * g L := by
    intro L
    have hx : x - (x - L) = L := by ring
    simp only [hx]
  rw [h1, convolution]
  simp only [h3] at h2
  rw [h2]
  refine integral_congr_ae (.of_forall fun t => ?_)
  rfl

/-- **The multiplier injectivity of the retarded transgression.**  If the kernel transform is
nonzero almost everywhere, an integrable half-line datum annihilated by the transgression is
almost everywhere zero. -/
theorem eq_zero_of_halfLineConvMinus_eq_zero {k : ℝ → ℂ} (hk : Integrable k)
    (hKne : ∀ᵐ ξ : ℝ, 𝓕 k ξ ≠ 0) {g : ℝ → ℂ} (hg : Integrable g)
    (hsupp : ∀ L : ℝ, L ≤ 0 → g L = 0) (h : ∀ x : ℝ, halfLineConvMinus k g x = 0) :
    g =ᵐ[volume] 0 := by
  have hconv : (k ⋆[ContinuousLinearMap.mul ℂ ℂ, (volume : Measure ℝ)] g) = fun _ : ℝ => (0 : ℂ) := by
    funext x
    rw [← halfLineConvMinus_eq_convolution hsupp x]
    exact h x
  have hF : ∀ ξ : ℝ, 𝓕 k ξ * 𝓕 g ξ = 0 := by
    intro ξ
    rw [← Real.fourier_mul_convolution_eq hk hg ξ, hconv, Real.fourier_eq]
    simp
  have hGzero : ∀ᵐ ξ : ℝ, 𝓕 g ξ = 0 := by
    filter_upwards [hKne] with ξ hξ
    exact (mul_eq_zero.mp (hF ξ)).resolve_left hξ
  have hGcont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg
  have hGall : 𝓕 g = fun _ : ℝ => (0 : ℂ) := by
    refine (Continuous.ae_eq_iff_eq (volume : Measure ℝ) hGcont continuous_const).1 ?_
    filter_upwards [hGzero] with ξ hξ using hξ
  exact HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hg (fun x => by rw [hGall])

/-- **The entire-symbol form.**  If the kernel transform is the restriction to the real axis of an
entire function that is not identically zero, the transgression is injective on integrable half-line
data. -/
theorem eq_zero_of_halfLineConvMinus_eq_zero_of_entire {k : ℝ → ℂ} (hk : Integrable k)
    {K : ℂ → ℂ} (hKanalytic : AnalyticOnNhd ℂ K Set.univ) (hKne : ∃ z, K z ≠ 0)
    (hKsymbol : ∀ ξ : ℝ, 𝓕 k ξ = K (ξ : ℂ)) {g : ℝ → ℂ} (hg : Integrable g)
    (hsupp : ∀ L : ℝ, L ≤ 0 → g L = 0) (h : ∀ x : ℝ, halfLineConvMinus k g x = 0) :
    g =ᵐ[volume] 0 := by
  refine eq_zero_of_halfLineConvMinus_eq_zero hk ?_ hg hsupp h
  have hnull := HTGeometry.volume_real_setOf_eq_zero_eq_zero hKanalytic hKne
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hnull
  intro ξ hξ
  simp only [Set.mem_setOf_eq, not_not] at hξ ⊢
  rw [← hKsymbol ξ]
  exact hξ

/-- The a.e. form of multiplier injectivity: only the almost-everywhere vanishing of the
transgression is needed. -/
theorem eq_zero_of_halfLineConvMinus_ae_eq_zero {k : ℝ → ℂ} (hk : Integrable k)
    (hKne : ∀ᵐ ξ : ℝ, 𝓕 k ξ ≠ 0) {g : ℝ → ℂ} (hg : Integrable g)
    (hsupp : ∀ L : ℝ, L ≤ 0 → g L = 0)
    (h : (fun x => halfLineConvMinus k g x) =ᵐ[volume] 0) :
    g =ᵐ[volume] 0 := by
  have hconvae : (k ⋆[ContinuousLinearMap.mul ℂ ℂ, (volume : Measure ℝ)] g)
      =ᵐ[volume] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [h] with x hx
    rw [← halfLineConvMinus_eq_convolution hsupp x]
    exact hx
  have hF : ∀ ξ : ℝ, 𝓕 k ξ * 𝓕 g ξ = 0 := by
    intro ξ
    rw [← Real.fourier_mul_convolution_eq hk hg ξ, Real.fourier_congr_ae hconvae ξ,
      Real.fourier_eq]
    simp
  have hGzero : ∀ᵐ ξ : ℝ, 𝓕 g ξ = 0 := by
    filter_upwards [hKne] with ξ hξ
    exact (mul_eq_zero.mp (hF ξ)).resolve_left hξ
  have hGcont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg
  have hGall : 𝓕 g = fun _ : ℝ => (0 : ℂ) := by
    refine (Continuous.ae_eq_iff_eq (volume : Measure ℝ) hGcont continuous_const).1 ?_
    filter_upwards [hGzero] with ξ hξ using hξ
  exact HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hg (fun x => by rw [hGall])

/-- The transgression separates integrable half-line data. -/
theorem eq_of_halfLineConvMinus_eq {k : ℝ → ℂ} (hk : Integrable k)
    (hKne : ∀ᵐ ξ : ℝ, 𝓕 k ξ ≠ 0) {g₁ g₂ : ℝ → ℂ} (hg₁ : Integrable g₁) (hg₂ : Integrable g₂)
    (hs₁ : ∀ L : ℝ, L ≤ 0 → g₁ L = 0) (hs₂ : ∀ L : ℝ, L ≤ 0 → g₂ L = 0)
    (h : ∀ x : ℝ, halfLineConvMinus k g₁ x = halfLineConvMinus k g₂ x) :
    g₁ =ᵐ[volume] g₂ := by
  have hsub : ∀ L : ℝ, L ≤ 0 → (g₁ - g₂) L = 0 := by
    intro L hL
    show g₁ L - g₂ L = 0
    rw [hs₁ L hL, hs₂ L hL, sub_zero]
  have hex₁ := hk.ae_convolution_exists (L := ContinuousLinearMap.mul ℂ ℂ)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) hg₁
  have hex₂ := hk.ae_convolution_exists (L := ContinuousLinearMap.mul ℂ ℂ)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) hg₂
  have hzero : (fun x => halfLineConvMinus k (g₁ - g₂) x) =ᵐ[volume] 0 := by
    filter_upwards [hex₁, hex₂] with x hx₁ hx₂
    rw [halfLineConvMinus_eq_convolution hsub x, convolution]
    have hsplit : (∫ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (k t) ((g₁ - g₂) (x - t)))
        = (∫ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (k t) (g₁ (x - t)))
          - ∫ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (k t) (g₂ (x - t)) := by
      rw [← MeasureTheory.integral_sub hx₁ hx₂]
      refine integral_congr_ae (.of_forall fun t => ?_)
      show k t * (g₁ (x - t) - g₂ (x - t)) = k t * g₁ (x - t) - k t * g₂ (x - t)
      ring
    rw [hsplit]
    have he₁ : (∫ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (k t) (g₁ (x - t)))
        = halfLineConvMinus k g₁ x := (halfLineConvMinus_eq_convolution hs₁ x).symm
    have he₂ : (∫ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (k t) (g₂ (x - t)))
        = halfLineConvMinus k g₂ x := (halfLineConvMinus_eq_convolution hs₂ x).symm
    rw [he₁, he₂, h x, sub_self]
    rfl
  have hd := eq_zero_of_halfLineConvMinus_ae_eq_zero hk hKne (hg₁.sub hg₂) hsub hzero
  filter_upwards [hd] with L hL
  have hval : g₁ L - g₂ L = 0 := hL
  exact sub_eq_zero.mp hval

end RHTower
