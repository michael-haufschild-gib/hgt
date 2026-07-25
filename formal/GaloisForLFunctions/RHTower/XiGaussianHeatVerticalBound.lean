import GaloisForLFunctions.RHTower.XiGaussianHeatTuranDefect

/-!
# The Gaussian heat trace at complex time, and its vertical bound under RH

Continuing the heat time into `Re tau > 0` turns the Gaussian trace into an exponential sum

`nu(tau) = sum_q exp (-tau * (xiSpectralPoint q)^2)`

whose terms have modulus `exp (-(Re tau * Re w - Im tau * Im w))`, `w = (xiSpectralPoint q)^2`.
Under RH every `w` is a positive real, so `Im w = 0`, the modulus of each term collapses to its
value at the real time `Re tau`, and the whole trace obeys

`‖nu(tau)‖ <= nu(Re tau)`.

The off-critical case is exactly the failure of that collapse: a copy with `Im w <> 0` contributes
`exp (Im tau * Im w)`, which grows along one vertical direction.  So the bound is a test of
**cancellation** in the trace rather than of a sign, and a single vertical-line value exceeding the
real-axis value refutes RH.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The Gaussian heat multiplier at complex time. -/
def xiGaussianHeatTermC (τ : ℂ) (q : XiZeroCopy) : ℂ :=
  Complex.exp (-τ * xiSpectralPoint q ^ 2)

theorem norm_xiGaussianHeatTerm (t : ℝ) (q : XiZeroCopy) :
    ‖xiGaussianHeatTerm t q‖ =
      Real.exp (-(t * (xiSpectralPoint q ^ 2).re)) := by
  rw [xiGaussianHeatTerm, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem norm_xiGaussianHeatTermC (τ : ℂ) (q : XiZeroCopy) :
    ‖xiGaussianHeatTermC τ q‖ =
      Real.exp (-(τ.re * (xiSpectralPoint q ^ 2).re -
        τ.im * (xiSpectralPoint q ^ 2).im)) := by
  rw [xiGaussianHeatTermC, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- Under RH the complex-time multiplier has the same modulus as the real-time one. -/
theorem norm_xiGaussianHeatTermC_of_rh (hRH : RiemannHypothesis) (τ : ℂ)
    (q : XiZeroCopy) :
    ‖xiGaussianHeatTermC τ q‖ = ‖xiGaussianHeatTerm τ.re q‖ := by
  have him : (xiSpectralPoint q ^ 2).im = 0 := by
    rw [xiSpectralSq_eq_ofReal_re_of_rh hRH q, Complex.ofReal_im]
  rw [norm_xiGaussianHeatTermC, norm_xiGaussianHeatTerm, him]
  congr 1
  ring

/-- Under RH the complex-time family is absolutely summable in the open right half-plane. -/
theorem summable_norm_xiGaussianHeatTermC_of_rh (hRH : RiemannHypothesis) {τ : ℂ}
    (hτ : 0 < τ.re) :
    Summable (fun q : XiZeroCopy => ‖xiGaussianHeatTermC τ q‖) := by
  have hbase : Summable (fun q : XiZeroCopy => ‖xiGaussianHeatTerm τ.re q‖) :=
    summable_norm_iff.mpr (summable_xiGaussianHeatTerm hτ)
  exact hbase.congr fun q => (norm_xiGaussianHeatTermC_of_rh hRH τ q).symm

/-- The Gaussian heat trace at complex time. -/
def xiGaussianHeatTraceC (τ : ℂ) : ℂ := ∑' q : XiZeroCopy, xiGaussianHeatTermC τ q

/-- **The vertical bound under RH.**  On every vertical line of the open right half-plane the
complex-time Gaussian heat trace is dominated by its value at the corresponding real time. -/
theorem norm_xiGaussianHeatTraceC_le_of_rh (hRH : RiemannHypothesis) {τ : ℂ}
    (hτ : 0 < τ.re) :
    ‖xiGaussianHeatTraceC τ‖ ≤ xiGaussianHeatTraceReal τ.re := by
  have hsumC := summable_norm_xiGaussianHeatTermC_of_rh hRH hτ
  have hbound : ‖xiGaussianHeatTraceC τ‖ ≤
      ∑' q : XiZeroCopy, ‖xiGaussianHeatTermC τ q‖ :=
    norm_tsum_le_tsum_norm hsumC
  have hcongr : ∑' q : XiZeroCopy, ‖xiGaussianHeatTermC τ q‖ =
      ∑' q : XiZeroCopy, (xiGaussianHeatTerm τ.re q).re := by
    refine tsum_congr fun q => ?_
    rw [norm_xiGaussianHeatTermC_of_rh hRH τ q]
    have hreal : xiGaussianHeatTerm τ.re q =
        ((Real.exp (-(τ.re * (xiSpectralPoint q ^ 2).re)) : ℝ) : ℂ) := by
      have h := xiGaussianHeatMonomialTerm_eq_ofReal_of_rh hRH 0 τ.re q
      simpa using h
    rw [hreal, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  rw [hcongr, ← xiGaussianHeatTraceReal_eq_tsum_re hτ] at hbound
  exact hbound

/-- **A cancellation-type RH-disproof endpoint.**  One complex time at which the Gaussian heat trace
exceeds its real-axis value contradicts RH.  Unlike the sign-type endpoints of
`XiGaussianHeatTraceDisproof`, this tests cancellation in the trace. -/
theorem not_riemannHypothesis_of_xiGaussianHeatTraceReal_lt_norm {τ : ℂ}
    (hτ : 0 < τ.re)
    (h : xiGaussianHeatTraceReal τ.re < ‖xiGaussianHeatTraceC τ‖) :
    ¬ RiemannHypothesis := fun hRH =>
  absurd (norm_xiGaussianHeatTraceC_le_of_rh hRH hτ) (not_le.mpr h)

/-- **The individual off-line multiplier is unbounded on every vertical line.**  A copy whose
squared spectral point has nonzero imaginary part -- equivalently, a copy off the critical line --
contributes a factor of arbitrarily large modulus somewhere on each vertical line.  This is the
termwise germ of the converse of `norm_xiGaussianHeatTraceC_le_of_rh`: what separates it from the
full converse is not the growth of any single term but possible cancellation between terms. -/
theorem exists_norm_xiGaussianHeatTermC_gt (σ : ℝ) {q : XiZeroCopy}
    (hq : (xiSpectralPoint q ^ 2).im ≠ 0) (M : ℝ) :
    ∃ y : ℝ, M < ‖xiGaussianHeatTermC (σ + y * I) q‖ := by
  set wre := (xiSpectralPoint q ^ 2).re with hwre
  set wim := (xiSpectralPoint q ^ 2).im with hwim
  refine ⟨(M + σ * wre) / wim, ?_⟩
  have hre : (σ + ((M + σ * wre) / wim : ℝ) * I).re = σ := by simp
  have him : (σ + ((M + σ * wre) / wim : ℝ) * I).im = (M + σ * wre) / wim := by simp
  rw [norm_xiGaussianHeatTermC, hre, him, ← hwre, ← hwim]
  have hcancel : (M + σ * wre) / wim * wim = M + σ * wre := div_mul_cancel₀ _ hq
  have hexp : -(σ * wre - (M + σ * wre) / wim * wim) = M := by
    rw [hcancel]; ring
  rw [hexp]
  linarith [Real.add_one_le_exp M]

end

end RHTower
