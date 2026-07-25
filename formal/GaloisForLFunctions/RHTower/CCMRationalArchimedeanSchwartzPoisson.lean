import GaloisForLFunctions.RHTower.CCMRationalArchimedeanSchwartzLattice
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Signed Poisson decay for the rational CCM archimedean trace

For the basic finite-adele sector `1_{\widehat{\mathbb Z}}`, the degree-zero rational CCM
diagonal trace is the integer lattice sum

`Θ_f(a) = ∑' n : ℤ, f (a * n)`.

This file proves its exact scaled Poisson identity. If the two CCM boundary functionals vanish,
`f 0 = 0` and `∫ f = 0`, it also proves explicit arbitrary-power bounds at both multiplicative
ends. The second bound is genuinely signed: it uses Poisson summation before norms, with the
integral condition killing the zero Fourier mode.

These are value-level estimates for the first archimedean sector. Multiplicative derivatives,
general finite Bruhat factors, the adelic LF completion, and cyclic degrees remain separate.
No positivity, zero-spectrum statement, numerical computation, or Riemann-hypothesis premise
occurs.
-/

noncomputable section

open scoped SchwartzMap FourierTransform

namespace GaloisForLFunctions
namespace RHTower

/-- Nonzero real dilation as a continuous real-linear equivalence. -/
def ccmRationalArchimedeanScale (a : ℝ) (ha : a ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 a ha)

/-- Pullback of a Schwartz function by a nonzero real dilation. -/
def ccmRationalArchimedeanDilation
    (f : CCMRationalArchimedeanSchwartz) (a : ℝ) (ha : a ≠ 0) :
    CCMRationalArchimedeanSchwartz :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ccmRationalArchimedeanScale a ha) f

@[simp]
theorem ccmRationalArchimedeanDilation_apply
    (f : CCMRationalArchimedeanSchwartz) (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    ccmRationalArchimedeanDilation f a ha x = f (a * x) :=
  rfl

/-- Integer-lattice trace in the basic rational finite-adele sector. -/
def ccmRationalArchimedeanLatticeTrace
    (f : CCMRationalArchimedeanSchwartz) (a : ℝ) : ℂ :=
  ∑' n : ℤ, f (a * (n : ℝ))

/-- Every nonzero-base lattice trace is absolutely summable. -/
theorem ccmRationalArchimedeanLatticeTrace_summable
    (f : CCMRationalArchimedeanSchwartz) {a : ℝ} (ha : a ≠ 0) :
    Summable (fun n : ℤ => f (a * (n : ℝ))) :=
  (ccmRationalArchimedeanSchwartz_lattice_summable f ha).of_norm

/-- Exact Fourier scaling law for the Schwartz dilation used in the trace. -/
theorem fourier_ccmRationalArchimedeanDilation
    (f : CCMRationalArchimedeanSchwartz) {a : ℝ} (ha : 0 < a) (w : ℝ) :
    𝓕 (ccmRationalArchimedeanDilation f a ha.ne') w =
      (a⁻¹ : ℂ) * 𝓕 f (w / a) := by
  have h :=
    GaloisForLFunctions.HTGeometry.fourier_comp_div_eq_abs_smul
      (f := fun x : ℝ => f x) (a := a⁻¹) (inv_ne_zero ha.ne') w
  change 𝓕 (fun x : ℝ => f (a * x)) w = _
  rw [show (fun x : ℝ => f (a * x)) =
      (fun x : ℝ => f (x / a⁻¹)) by
    funext x
    congr 1
    field_simp]
  rw [h, abs_inv, abs_of_pos ha]
  simp only [Complex.real_smul]
  congr 1
  · norm_cast
  · change 𝓕 (fun x : ℝ => f x) (a⁻¹ * w) =
        𝓕 (fun x : ℝ => f x) (w / a)
    rw [show a⁻¹ * w = w / a by field_simp]

/-- **Scaled Poisson identity for the basic rational CCM diagonal trace.** -/
theorem ccmRationalArchimedeanLatticeTrace_poisson
    (f : CCMRationalArchimedeanSchwartz) {a : ℝ} (ha : 0 < a) :
    ccmRationalArchimedeanLatticeTrace f a =
      (a⁻¹ : ℂ) *
        ccmRationalArchimedeanLatticeTrace (𝓕 f) a⁻¹ := by
  have h := SchwartzMap.tsum_eq_tsum_fourier
    (ccmRationalArchimedeanDilation f a ha.ne') 0
  have hzero (n : ℤ) :
      fourier n ((0 : ℝ) : UnitAddCircle) = 1 := by
    simpa only [← QuotientAddGroup.mk_zero] using fourier_eval_zero n
  rw [ccmRationalArchimedeanLatticeTrace]
  rw [show ccmRationalArchimedeanLatticeTrace (𝓕 f) a⁻¹ =
      ∑' n : ℤ, 𝓕 f ((n : ℝ) / a) by
    apply tsum_congr
    intro n
    congr 1
    field_simp]
  simp_rw [zero_add, ccmRationalArchimedeanDilation_apply,
    fourier_ccmRationalArchimedeanDilation f ha, hzero, mul_one] at h
  simpa only [← tsum_mul_left] using h

/-- Even exponent used for a nonnegative integral `p`-series majorant. -/
def ccmRationalArchimedeanDecayExponent (N : ℕ) : ℕ :=
  2 * (N + 1)

/-- Punctured nonnegative integral `p`-series kernel. -/
def ccmRationalArchimedeanPSeriesKernel (N : ℕ) (n : ℤ) : ℝ :=
  if n = 0 then 0
  else 1 / (n : ℝ) ^ ccmRationalArchimedeanDecayExponent N

theorem ccmRationalArchimedeanDecayExponent_gt_one (N : ℕ) :
    1 < ccmRationalArchimedeanDecayExponent N := by
  simp [ccmRationalArchimedeanDecayExponent]
  omega

theorem ccmRationalArchimedeanPSeriesKernel_summable (N : ℕ) :
    Summable (ccmRationalArchimedeanPSeriesKernel N) := by
  have h :=
    (Real.summable_one_div_int_pow
      (p := ccmRationalArchimedeanDecayExponent N)).2
      (ccmRationalArchimedeanDecayExponent_gt_one N)
  apply h.congr_cofinite
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  simp [ccmRationalArchimedeanPSeriesKernel, hn]

theorem ccmRationalArchimedeanPSeriesKernel_nonneg
    (N : ℕ) (n : ℤ) :
    0 ≤ ccmRationalArchimedeanPSeriesKernel N n := by
  by_cases hn : n = 0
  · simp [ccmRationalArchimedeanPSeriesKernel, hn]
  · rw [ccmRationalArchimedeanPSeriesKernel, if_neg hn,
      ccmRationalArchimedeanDecayExponent, pow_mul]
    positivity

/-- Explicit Schwartz-seminorm constant for one arbitrary-power lattice estimate. -/
def ccmRationalArchimedeanDecayConstant
    (f : CCMRationalArchimedeanSchwartz) (N : ℕ) : ℝ :=
  SchwartzMap.seminorm ℂ (ccmRationalArchimedeanDecayExponent N) 0 f *
    ∑' n : ℤ, ccmRationalArchimedeanPSeriesKernel N n

theorem ccmRationalArchimedeanDecayConstant_nonneg
    (f : CCMRationalArchimedeanSchwartz) (N : ℕ) :
    0 ≤ ccmRationalArchimedeanDecayConstant f N := by
  apply mul_nonneg (by positivity)
  exact tsum_nonneg (ccmRationalArchimedeanPSeriesKernel_nonneg N)

/--
If the physical zero mode vanishes, the lattice trace has arbitrary-power decay at the large
multiplicative end.
-/
theorem ccmRationalArchimedeanLatticeTrace_large_bound
    (f : CCMRationalArchimedeanSchwartz) (hf0 : f 0 = 0)
    (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ‖ccmRationalArchimedeanLatticeTrace f a‖ ≤
      ccmRationalArchimedeanDecayConstant f N /
        a ^ ccmRationalArchimedeanDecayExponent N := by
  let p := ccmRationalArchimedeanDecayExponent N
  let S := SchwartzMap.seminorm ℂ p 0 f
  let C := S / a ^ p
  have hnorm : Summable (fun n : ℤ => ‖f (a * (n : ℝ))‖) :=
    ccmRationalArchimedeanSchwartz_lattice_summable f ha.ne'
  have hC : 0 ≤ C := div_nonneg (by positivity) (by positivity)
  have hmajor :
      Summable (fun n : ℤ =>
        C * ccmRationalArchimedeanPSeriesKernel N n) :=
    (ccmRationalArchimedeanPSeriesKernel_summable N).mul_left C
  have hpoint (n : ℤ) :
      ‖f (a * (n : ℝ))‖ ≤
        C * ccmRationalArchimedeanPSeriesKernel N n := by
    by_cases hn : n = 0
    · subst n
      simp [hf0, ccmRationalArchimedeanPSeriesKernel]
    · have hnR : (n : ℝ) ≠ 0 := by
        exact_mod_cast hn
      have han : a * (n : ℝ) ≠ 0 := mul_ne_zero ha.ne' hnR
      have hx : 0 < ‖a * (n : ℝ)‖ ^ p :=
        pow_pos (norm_pos_iff.mpr han) _
      have hsem :=
        SchwartzMap.norm_pow_mul_le_seminorm ℂ f p
          (a * (n : ℝ))
      calc
        ‖f (a * (n : ℝ))‖ ≤
            S / ‖a * (n : ℝ)‖ ^ p := by
          apply (le_div_iff₀ hx).2
          simpa [S, mul_comm] using hsem
        _ = C * ccmRationalArchimedeanPSeriesKernel N n := by
          dsimp [C]
          rw [ccmRationalArchimedeanPSeriesKernel, if_neg hn,
            abs_mul, abs_of_pos ha]
          have hnabs : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr hnR
          rw [mul_pow]
          have habspow :
              |(n : ℝ)| ^ p = (n : ℝ) ^ p := by
            change |(n : ℝ)| ^ (2 * (N + 1)) =
              (n : ℝ) ^ (2 * (N + 1))
            rw [pow_mul, pow_mul, sq_abs]
          rw [habspow]
          field_simp
          rfl
  calc
    ‖ccmRationalArchimedeanLatticeTrace f a‖ ≤
        ∑' n : ℤ, ‖f (a * (n : ℝ))‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℤ,
        C * ccmRationalArchimedeanPSeriesKernel N n :=
      Summable.tsum_mono hnorm hmajor hpoint
    _ = ccmRationalArchimedeanDecayConstant f N /
        a ^ ccmRationalArchimedeanDecayExponent N := by
      rw [tsum_mul_left]
      simp only [C, S, p, ccmRationalArchimedeanDecayConstant]
      ring

/--
If the Fourier zero mode vanishes, Poisson summation turns the large-end estimate into
arbitrary-power decay at the small multiplicative end.
-/
theorem ccmRationalArchimedeanLatticeTrace_small_bound
    (f : CCMRationalArchimedeanSchwartz) (hF0 : (𝓕 f) 0 = 0)
    (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ‖ccmRationalArchimedeanLatticeTrace f a‖ ≤
      ccmRationalArchimedeanDecayConstant (𝓕 f) N *
        a ^ (ccmRationalArchimedeanDecayExponent N - 1) := by
  rw [ccmRationalArchimedeanLatticeTrace_poisson f ha, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hdual :=
    ccmRationalArchimedeanLatticeTrace_large_bound
      (𝓕 f) hF0 N (inv_pos.mpr ha)
  calc
    a⁻¹ * ‖ccmRationalArchimedeanLatticeTrace (𝓕 f) a⁻¹‖ ≤
        a⁻¹ *
          (ccmRationalArchimedeanDecayConstant (𝓕 f) N /
            (a⁻¹) ^ ccmRationalArchimedeanDecayExponent N) := by
      gcongr
    _ = ccmRationalArchimedeanDecayConstant (𝓕 f) N *
        a ^ (ccmRationalArchimedeanDecayExponent N - 1) := by
      have hp : 1 ≤ ccmRationalArchimedeanDecayExponent N :=
        (ccmRationalArchimedeanDecayExponent_gt_one N).le
      rw [inv_pow, div_inv_eq_mul]
      rw [show ccmRationalArchimedeanDecayExponent N =
          (ccmRationalArchimedeanDecayExponent N - 1) + 1 by omega,
        pow_succ]
      field_simp
      congr 2

/-- The Fourier zero mode is exactly the additive integral. -/
theorem fourier_ccmRationalArchimedean_zero_eq_integral
    (f : CCMRationalArchimedeanSchwartz) :
    (𝓕 f) 0 = ∫ x : ℝ, f x := by
  change 𝓕 (fun x : ℝ => f x) 0 = _
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp

/--
**Two CCM cancellations imply two-ended arbitrary-power value decay.**

This is the first formal signed-Poisson sector of CCM Proposition 4.8.
-/
theorem ccmRationalArchimedeanLatticeTrace_twoSidedDecay
    (f : CCMRationalArchimedeanSchwartz)
    (hf0 : f 0 = 0) (hfint : (∫ x : ℝ, f x) = 0)
    (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ‖ccmRationalArchimedeanLatticeTrace f a‖ ≤
        ccmRationalArchimedeanDecayConstant f N /
          a ^ ccmRationalArchimedeanDecayExponent N ∧
      ‖ccmRationalArchimedeanLatticeTrace f a‖ ≤
        ccmRationalArchimedeanDecayConstant (𝓕 f) N *
          a ^ (ccmRationalArchimedeanDecayExponent N - 1) := by
  refine
    ⟨ccmRationalArchimedeanLatticeTrace_large_bound f hf0 N ha, ?_⟩
  apply ccmRationalArchimedeanLatticeTrace_small_bound f
  · rw [fourier_ccmRationalArchimedean_zero_eq_integral, hfint]
  · exact ha

end RHTower
end GaloisForLFunctions
