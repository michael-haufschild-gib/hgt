import GaloisForLFunctions.HTGeometry.PoissonFatou
import GaloisForLFunctions.RHTower.SoninSemilocalPoissonExpansion
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Abel boundary values for the angular Poisson Fourier series

The zero extension of a compact prolate source has endpoint jumps, so its ordinary Poisson series
need not be absolutely summable.  This module supplies the endpoint-safe replacement.  The
bilateral Fourier series is first weighted by `r ^ |m|`; it is then absolutely summable, equals the
Poisson integral exactly, and converges at every symmetric Lebesgue point as `r` tends to one from
below.

The result is a genuine boundary theorem for an interval-integrable datum.  It does not assume the
desired boundary value or hide a nonintegrable series behind a convention.
-/

open Real MeasureTheory Set intervalIntegral Filter Topology

noncomputable section

namespace RHTower

/-- The angular bilateral Fourier term carrying the Abel weight `r ^ |m|`. -/
def angularPoissonFourierTerm (r t : ℝ) (m : ℤ) : ℂ :=
  semilocalBilateralPoissonTerm r (Complex.exp (t * Complex.I)) m

/-- The absolutely convergent bilateral angular series is exactly the real angular Poisson
kernel. -/
theorem tsum_angularPoissonFourierTerm_eq_poissonKer
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    ∑' m : ℤ, angularPoissonFourierTerm r t m =
      (GaloisForLFunctions.HTGeometry.poissonKer r t : ℂ) := by
  have hz : ‖Complex.exp (t * Complex.I)‖ = 1 := by
    exact Complex.norm_exp_ofReal_mul_I t
  change (∑' m : ℤ,
    semilocalBilateralPoissonTerm r (Complex.exp (t * Complex.I)) m) = _
  rw [tsum_semilocalBilateralPoissonTerm_eq_normSq hr0 hr1 hz]
  rw [GaloisForLFunctions.HTGeometry.poissonKer]
  norm_cast
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  field_simp
  ring_nf
  rw [Real.sin_sq]
  ring

/-- The bilateral Abel-weighted Fourier average of a real boundary datum. -/
def poissonAbelFourierAverage (φ : ℝ → ℝ) (r : ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ *
    ∑' m : ℤ, ∫ t in (-Real.pi)..Real.pi,
      angularPoissonFourierTerm r t m * (φ t : ℂ)

/-- The Fourier-side Abel average equals the physical-side Poisson integral.  The proof genuinely
interchanges an absolutely dominated bilateral series with the interval integral. -/
theorem poissonAbelFourierAverage_eq_poissonIntegral
    {φ : ℝ → ℝ} (hφ : IntervalIntegrable φ volume (-Real.pi) Real.pi)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    poissonAbelFourierAverage φ r =
      (((2 * Real.pi)⁻¹ * ∫ t in (-Real.pi)..Real.pi,
        GaloisForLFunctions.HTGeometry.poissonKer r t * φ t : ℝ) : ℂ) := by
  let F : ℤ → ℝ → ℂ := fun m t =>
    angularPoissonFourierTerm r t m * (φ t : ℂ)
  let bound : ℤ → ℝ → ℝ := fun m t => r ^ m.natAbs * |φ t|
  have hsum : Summable fun m : ℤ => r ^ m.natAbs :=
    summable_int_pow_natAbs hr0 hr1
  have hFmeas : ∀ m, AEStronglyMeasurable (F m)
      (volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
    intro m
    have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
    have hphase : Continuous fun t : ℝ => angularPoissonFourierTerm r t m := by
      unfold angularPoissonFourierTerm semilocalBilateralPoissonTerm
      exact continuous_const.mul
        ((Complex.continuous_exp.comp
          (Complex.continuous_ofReal.mul continuous_const)).zpow₀ m
            (fun t => Or.inl (Complex.exp_ne_zero _)))
    rw [Set.uIoc_of_le hpi]
    simpa only [F, Pi.mul_apply] using
      hphase.aestronglyMeasurable.mul
        hφ.1.aestronglyMeasurable.aemeasurable.complex_ofReal.aestronglyMeasurable
  have hbound : ∀ m, ∀ᵐ t ∂volume, t ∈ Set.uIoc (-Real.pi) Real.pi →
      ‖F m t‖ ≤ bound m t := by
    intro m
    filter_upwards with t ht
    change ‖angularPoissonFourierTerm r t m * (φ t : ℂ)‖ ≤
      r ^ m.natAbs * |φ t|
    rw [norm_mul]
    have hz : ‖Complex.exp (t * Complex.I)‖ = 1 := by
      exact Complex.norm_exp_ofReal_mul_I t
    simp [angularPoissonFourierTerm, semilocalBilateralPoissonTerm,
      norm_pow, norm_zpow, hz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
  have hboundSummable : ∀ᵐ t ∂volume,
      t ∈ Set.uIoc (-Real.pi) Real.pi → Summable fun m : ℤ => bound m t := by
    filter_upwards with t ht
    exact hsum.mul_right |φ t|
  have hboundInt : IntervalIntegrable (fun t => ∑' m : ℤ, bound m t)
      volume (-Real.pi) Real.pi := by
    have heq : (fun t => ∑' m : ℤ, bound m t) =
        fun t => (∑' m : ℤ, r ^ m.natAbs) * |φ t| := by
      funext t
      simp only [bound]
      rw [tsum_mul_right]
    rw [heq]
    exact hφ.abs.const_mul _
  have hlim : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-Real.pi) Real.pi →
      HasSum (fun m : ℤ => F m t)
        ((GaloisForLFunctions.HTGeometry.poissonKer r t : ℂ) * (φ t : ℂ)) := by
    filter_upwards with t ht
    have hz : ‖Complex.exp (t * Complex.I)‖ = 1 := by
      exact Complex.norm_exp_ofReal_mul_I t
    have hs : HasSum (fun m : ℤ => F m t)
        ((∑' m : ℤ, angularPoissonFourierTerm r t m) * (φ t : ℂ)) := by
      simpa only [F, angularPoissonFourierTerm] using
        (summable_semilocalBilateralPoissonTerm hr0 hr1 hz).hasSum.mul_right (φ t : ℂ)
    rw [tsum_angularPoissonFourierTerm_eq_poissonKer hr0 hr1 t] at hs
    exact hs
  have hswap := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -Real.pi) (b := Real.pi) (f := fun t =>
      ((GaloisForLFunctions.HTGeometry.poissonKer r t : ℂ) * (φ t : ℂ)))
    bound hFmeas hbound hboundSummable hboundInt hlim
  rw [poissonAbelFourierAverage, hswap.tsum_eq]
  change (2 * Real.pi : ℂ)⁻¹ *
      ∫ t in (-Real.pi)..Real.pi,
        ((GaloisForLFunctions.HTGeometry.poissonKer r t : ℂ) * (φ t : ℂ)) = _
  rw [show (fun t : ℝ =>
      ((GaloisForLFunctions.HTGeometry.poissonKer r t : ℂ) * (φ t : ℂ))) =
      fun t : ℝ => ((GaloisForLFunctions.HTGeometry.poissonKer r t * φ t : ℝ) : ℂ) by
        funext t
        norm_cast]
  rw [intervalIntegral.integral_ofReal]
  norm_cast

/-- **Poisson--Abel boundary theorem.**  At every symmetric Lebesgue point, the exact bilateral
Abel-weighted Fourier average converges to the boundary value. -/
theorem tendsto_poissonAbelFourierAverage_of_symmLebesgue
    {φ : ℝ → ℝ}
    (hφ : IntervalIntegrable φ volume (-Real.pi) Real.pi)
    (hleb : Tendsto
      (fun s => (∫ t in (0 : ℝ)..s,
        |φ t - φ 0| + |φ (-t) - φ 0|) / s)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => poissonAbelFourierAverage φ r)
      (𝓝[<] 1) (𝓝 (φ 0 : ℂ)) := by
  have hreal :=
    GaloisForLFunctions.HTGeometry.tendsto_poissonConv_of_symmLebesgue hφ hleb
  have hcomplex : Tendsto
      (fun r : ℝ => (((2 * Real.pi)⁻¹ *
        ∫ t in (-Real.pi)..Real.pi,
          GaloisForLFunctions.HTGeometry.poissonKer r t * φ t : ℝ) : ℂ))
      (𝓝[<] 1) (𝓝 (φ 0 : ℂ)) := by
    exact (Complex.ofRealCLM.continuous.tendsto (φ 0)).comp hreal
  apply hcomplex.congr'
  have h0r : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r :=
    ((isOpen_Ioi.eventually_mem (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds).mono (fun r hr => hr.le)
  have h1r : ∀ᶠ r in 𝓝[<] (1 : ℝ), r < 1 :=
    eventually_of_mem self_mem_nhdsWithin (fun r hr => Set.mem_Iio.1 hr)
  filter_upwards [h0r, h1r] with r hr0 hr1
  exact (poissonAbelFourierAverage_eq_poissonIntegral hφ hr0 hr1).symm

end RHTower
