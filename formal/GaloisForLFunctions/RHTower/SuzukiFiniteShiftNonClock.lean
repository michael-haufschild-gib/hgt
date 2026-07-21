import GaloisForLFunctions.RHTower.SuzukiProjectiveDefectBoundary
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace GaloisForLFunctions.RHTower

open Complex Filter Set Topology

noncomputable section

/-- Singular endpoint term in Suzuki's finite-part Weil kernel applied to `x ↦ exp x`. -/
def suzukiBoundaryLogTerm (a x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.exp x * Real.log (a ^ 2 - x ^ 2)

/-- Suzuki endpoint profile after collecting all terms with a finite left endpoint limit. -/
def suzukiBoundaryKernelProfile (a : ℝ) (R : ℝ → ℝ) (x : ℝ) : ℝ :=
  suzukiBoundaryLogTerm a x + R x

theorem tendsto_suzukiBoundaryDistanceSq_nhdsLT (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => a ^ 2 - x ^ 2) (𝓝[<] a) (𝓝[>] 0) := by
  have hleft : ∀ᶠ x : ℝ in 𝓝[<] a, -a < x :=
    (show ∀ᶠ x : ℝ in 𝓝 a, -a < x from
      Ioi_mem_nhds (show -a < a by linarith)).filter_mono nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hcont : Continuous (fun x : ℝ => a ^ 2 - x ^ 2) :=
      continuous_const.sub (continuous_id.pow 2)
    have hzero : Tendsto (fun x : ℝ => a ^ 2 - x ^ 2) (𝓝 a) (𝓝 0) := by
      simpa using hcont.tendsto a
    exact hzero.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin, hleft] with x hxa hax
    simp only [mem_Iio, mem_Ioi] at hxa hax ⊢
    nlinarith [mul_pos (sub_pos.mpr hxa) (add_pos_of_pos_of_nonneg ha ha.le)]

theorem suzukiBoundaryLogTerm_tendsto_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (suzukiBoundaryLogTerm a) (𝓝[<] a) atTop := by
  have hdist := tendsto_suzukiBoundaryDistanceSq_nhdsLT a ha
  have hlog : Tendsto (fun x : ℝ => -Real.log (a ^ 2 - x ^ 2)) (𝓝[<] a) atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hdist)
  have hcoeff : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * Real.exp x)
      (𝓝[<] a) (𝓝 ((1 / 2 : ℝ) * Real.exp a)) :=
    (tendsto_const_nhds.mul
      (Real.continuous_exp.tendsto a)).mono_left nhdsWithin_le_nhds
  have hpos : 0 < (1 / 2 : ℝ) * Real.exp a := mul_pos (by norm_num) (Real.exp_pos a)
  have hmul := hcoeff.pos_mul_atTop hpos hlog
  convert hmul using 1
  funext x
  simp only [suzukiBoundaryLogTerm]
  ring

theorem suzukiBoundaryKernelProfile_tendsto_atTop
    {a L : ℝ} (ha : 0 < a) {R : ℝ → ℝ} (hR : Tendsto R (𝓝[<] a) (𝓝 L)) :
    Tendsto (suzukiBoundaryKernelProfile a R) (𝓝[<] a) atTop := by
  exact (suzukiBoundaryLogTerm_tendsto_atTop a ha).atTop_add hR

theorem suzukiBoundaryKernelProfile_ne_exp_smul
    {a L c : ℝ} (ha : 0 < a) {R : ℝ → ℝ} (hR : Tendsto R (𝓝[<] a) (𝓝 L)) :
    ¬∀ x ∈ Ioo (-a) a, suzukiBoundaryKernelProfile a R x = c * Real.exp x := by
  intro hEq
  have hleft : ∀ᶠ x : ℝ in 𝓝[<] a, -a < x :=
    (show ∀ᶠ x : ℝ in 𝓝 a, -a < x from
      Ioi_mem_nhds (show -a < a by linarith)).filter_mono nhdsWithin_le_nhds
  have hevent : suzukiBoundaryKernelProfile a R =ᶠ[𝓝[<] a]
      fun x => c * Real.exp x := by
    filter_upwards [self_mem_nhdsWithin, hleft] with x hxa hax
    exact hEq x ⟨hax, hxa⟩
  have hfinite : Tendsto (fun x : ℝ => c * Real.exp x) (𝓝[<] a)
      (𝓝 (c * Real.exp a)) :=
    (tendsto_const_nhds.mul (Real.continuous_exp.tendsto a)).mono_left nhdsWithin_le_nhds
  have hinf := suzukiBoundaryKernelProfile_tendsto_atTop ha hR
  exact not_tendsto_nhds_of_tendsto_atTop hinf (c * Real.exp a)
    (hfinite.congr' hevent.symm)

/-- Non-anchor free-clock zeros on the horizontal sampling line `im z = 1`. -/
def suzukiFreeClockSample (a : ℝ) (n : ℤ) : ℂ :=
  ((Real.pi * (n : ℝ) / a : ℝ) : ℂ) + I

theorem suzukiFreeClockSample_ne_I {a : ℝ} (ha : a ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    suzukiFreeClockSample a n ≠ I := by
  intro h
  have hreal : Real.pi * (n : ℝ) / a = 0 := by
    have := congrArg Complex.re h
    simpa [suzukiFreeClockSample] using this
  have hncast : (n : ℝ) = 0 :=
    (mul_eq_zero.mp ((div_eq_zero_iff.mp hreal).resolve_right ha)).resolve_left
      Real.pi_ne_zero
  exact hn (by exact_mod_cast hncast)

theorem suzukiFreeLivsic_freeClockSample_eq_zero
    {a : ℝ} (ha : a ≠ 0) (n : ℤ) :
    suzukiFreeLivsic a (suzukiFreeClockSample a n) = 0 := by
  have harg :
      2 * I * (a : ℂ) * suzukiFreeClockSample a n =
        ((-2 * a : ℝ) : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    simp only [suzukiFreeClockSample]
    push_cast
    field_simp [ha]
    rw [mul_add, ← mul_assoc I I, I_mul_I]
    ring
  have hexp :
      Complex.exp (2 * I * (a : ℂ) * suzukiFreeClockSample a n) =
        (Real.exp (-2 * a) : ℂ) := by
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    exact (Complex.ofReal_exp _).symm
  simp [suzukiFreeLivsic, hexp]

section HilbertSampling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- If all nonzero coordinates of a vector in a Hilbert basis vanish, the vector is exactly its
zero mode.  This is the completeness step behind Suzuki's clock-sampling rigidity. -/
theorem eq_smul_hilbertBasis_zero_of_repr_eq_zero_off_zero
    (b : HilbertBasis ℤ ℂ E) (v : E)
    (hzero : ∀ n : ℤ, n ≠ 0 → b.repr v n = 0) :
    v = b.repr v 0 • b 0 := by
  apply b.repr.injective
  ext n
  by_cases hn : n = 0
  · subst n
    simp [HilbertBasis.repr_self]
  · rw [hzero n hn]
    simp [map_smul, HilbertBasis.repr_self, hn]

/-- Cross-product numerator measuring the anti-reflected projective tangent. -/
def suzukiReflectionTangentNumerator (F H : ℂ → ℂ) (z : ℂ) : ℂ :=
  H z * F (-z) - F z * H (-z)

/-- If Suzuki's anti-reflected tangent numerator vanishes identically, its weighted source has
only the zero Fourier mode and is therefore proportional to the free exponential source. -/
theorem eq_smul_hilbertBasis_zero_of_suzukiReflectionTangentNumerator_eq_zero
    (b : HilbertBasis ℤ ℂ E) (v : E) (F H : ℂ → ℂ) (sample : ℤ → ℂ)
    (hFzero : ∀ n : ℤ, n ≠ 0 → F (sample n) = 0)
    (hFneg : ∀ n : ℤ, n ≠ 0 → F (-sample n) ≠ 0)
    (hHcoeff : ∀ n : ℤ, n ≠ 0 → H (sample n) = b.repr v n)
    (htangent : ∀ z : ℂ, suzukiReflectionTangentNumerator F H z = 0) :
    v = b.repr v 0 • b 0 := by
  apply eq_smul_hilbertBasis_zero_of_repr_eq_zero_off_zero b v
  intro n hn
  have hcross := htangent (sample n)
  rw [suzukiReflectionTangentNumerator, hFzero n hn, zero_mul, sub_zero] at hcross
  rw [← hHcoeff n hn]
  exact (mul_eq_zero.mp hcross).resolve_right (hFneg n hn)

/-- **Non-flat Suzuki tangent certificate.** A weighted source with a genuine nonzero Fourier
mode forces the anti-reflected projective tangent numerator to be nonzero somewhere. -/
theorem exists_suzukiReflectionTangentNumerator_ne_zero
    (b : HilbertBasis ℤ ℂ E) (v : E) (F H : ℂ → ℂ) (sample : ℤ → ℂ)
    (hFzero : ∀ n : ℤ, n ≠ 0 → F (sample n) = 0)
    (hFneg : ∀ n : ℤ, n ≠ 0 → F (-sample n) ≠ 0)
    (hHcoeff : ∀ n : ℤ, n ≠ 0 → H (sample n) = b.repr v n)
    (hgenuine : v ≠ b.repr v 0 • b 0) :
    ∃ z : ℂ, suzukiReflectionTangentNumerator F H z ≠ 0 := by
  by_contra h
  have hzero : ∀ z : ℂ, suzukiReflectionTangentNumerator F H z = 0 := by
    intro z
    exact not_ne_iff.mp (not_exists.mp h z)
  exact hgenuine
    (eq_smul_hilbertBasis_zero_of_suzukiReflectionTangentNumerator_eq_zero
      b v F H sample hFzero hFneg hHcoeff hzero)

end HilbertSampling

/-- Equality with a free clock carrier at a non-anchor free zero forces the corresponding Suzuki
source Fourier sample to vanish. -/
theorem suzukiFourier_sample_eq_zero_of_livsic_eq_free
    {U F : ℂ → ℂ} {z : ℂ} (hz : z ≠ I) (hF : F z = 0)
    (hden : suzukiFourierDenominator U z ≠ 0)
    (heq : suzukiLivsicQuotient (suzukiFourierNumerator U)
        (suzukiFourierDenominator U) z =
      suzukiLivsicQuotient (suzukiFourierNumerator F)
        (suzukiFourierDenominator F) z) :
    U z = 0 := by
  have hright : suzukiLivsicQuotient (suzukiFourierNumerator F)
      (suzukiFourierDenominator F) z = 0 := by
    simp [suzukiLivsicQuotient, suzukiFourierNumerator, hF]
  rw [hright] at heq
  have hnum : suzukiFourierNumerator U z = 0 :=
    (div_eq_zero_iff.mp heq).resolve_right hden
  rw [suzukiFourierNumerator, mul_eq_zero] at hnum
  exact hnum.resolve_left (sub_ne_zero.mpr hz)

/-- Equality with Suzuki's explicit free clock at one non-anchor clock zero forces the matching
finite-shift Fourier source sample to vanish. -/
theorem suzukiFourier_freeClockSample_eq_zero_of_livsic_eq_freeClock
    {a : ℝ} (ha : a ≠ 0) {n : ℤ} (hn : n ≠ 0) {U : ℂ → ℂ}
    (hden : suzukiFourierDenominator U (suzukiFreeClockSample a n) ≠ 0)
    (heq : suzukiLivsicQuotient (suzukiFourierNumerator U)
        (suzukiFourierDenominator U) (suzukiFreeClockSample a n) =
      suzukiFreeLivsic a (suzukiFreeClockSample a n)) :
    U (suzukiFreeClockSample a n) = 0 := by
  have hright : suzukiFreeLivsic a (suzukiFreeClockSample a n) = 0 :=
    suzukiFreeLivsic_freeClockSample_eq_zero ha n
  rw [hright] at heq
  have hnum : suzukiFourierNumerator U (suzukiFreeClockSample a n) = 0 :=
    (div_eq_zero_iff.mp heq).resolve_right hden
  rw [suzukiFourierNumerator, mul_eq_zero] at hnum
  exact hnum.resolve_left (sub_ne_zero.mpr (suzukiFreeClockSample_ne_I ha hn))

/-- **Finite-shift free-clock rigidity.** If every clock sample of a Suzuki Fourier carrier agrees
with the explicit free carrier, completeness forces the exponentially weighted resolvent source
to contain only its constant Fourier mode. -/
theorem eq_smul_hilbertBasis_zero_of_suzukiLivsic_eq_freeClock
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ℤ ℂ E) (v : E) {a : ℝ} (ha : a ≠ 0) (U : ℂ → ℂ)
    (hcoeff : ∀ n : ℤ, n ≠ 0 → U (suzukiFreeClockSample a n) = b.repr v n)
    (hden : ∀ n : ℤ, n ≠ 0 →
      suzukiFourierDenominator U (suzukiFreeClockSample a n) ≠ 0)
    (heq : ∀ n : ℤ, n ≠ 0 →
      suzukiLivsicQuotient (suzukiFourierNumerator U)
          (suzukiFourierDenominator U) (suzukiFreeClockSample a n) =
        suzukiFreeLivsic a (suzukiFreeClockSample a n)) :
    v = b.repr v 0 • b 0 := by
  apply eq_smul_hilbertBasis_zero_of_repr_eq_zero_off_zero b v
  intro n hn
  rw [← hcoeff n hn]
  exact suzukiFourier_freeClockSample_eq_zero_of_livsic_eq_freeClock
    ha hn (hden n hn) (heq n hn)

end

end GaloisForLFunctions.RHTower
