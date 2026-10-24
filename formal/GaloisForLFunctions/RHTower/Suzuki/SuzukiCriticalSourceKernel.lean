import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalBetaKernel
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The complete archimedean Suzuki source in logarithmic coordinates

The primary Beta density and its causal pole convolution give the literal
signed source, including the growing polar branch. The logarithmic substitution
keeps the convolution on its finite interval before any limiting argument.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Critical logarithmic normalization of the literal archimedean source. -/
def suzukiCriticalArchDensity (omega t : ℝ) : ℝ :=
  Real.exp (-t / 2) * (suzukiSourceG omega (Real.exp (-t))).re

/-- The causal pole convolution in logarithmic coordinates. -/
def suzukiCriticalPoleDensity (omega t : ℝ) : ℝ :=
  ∫ r in Ioo 0 t, suzukiCriticalPrimaryDensity omega r *
    Real.exp ((1 / 2 - omega) * (t - r))

private theorem primary_real {omega x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    suzukiPrimaryBetaKernel omega x =
      ((2 / Real.Gamma omega * x ^ (2 - omega) *
        (1 - x ^ 2) ^ (omega - 1) : ℝ) : ℂ) := by
  rw [suzukiPrimaryBetaKernel_eq_source omega hx hx1, Complex.Gamma_ofReal]
  have hb : 0 ≤ 1 - x ^ 2 := by nlinarith
  push_cast
  rw [Complex.ofReal_cpow hx.le, Complex.ofReal_cpow hb]
  push_cast
  rfl

/-- The primary log density is the real-valued complex Mellin pullback. -/
theorem ofReal_suzukiCriticalPrimaryDensity {omega t : ℝ} (ht : 0 < t) :
    (suzukiCriticalPrimaryDensity omega t : ℂ) =
      ((Real.pi ^ omega * Real.exp (-t / 2) : ℝ) : ℂ) *
        suzukiPrimaryBetaKernel omega (Real.exp (-t)) := by
  rw [suzukiCriticalPrimaryDensity,
    primary_real (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (by linarith)),
    Complex.ofReal_re, Complex.ofReal_mul]

private theorem image_exp_neg_interval {t : ℝ} (ht : 0 < t) :
    (fun r : ℝ => Real.exp (-r)) '' Ioo 0 t = Ioo (Real.exp (-t)) 1 := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨Real.exp_lt_exp.mpr (by linarith [hr.2]),
      Real.exp_lt_one_iff.mpr (by linarith [hr.1])⟩
  · intro hx
    have hx0 := (Real.exp_pos (-t)).trans hx.1
    refine ⟨-Real.log x, ⟨neg_pos.mpr (Real.log_neg hx0 hx.2), ?_⟩, ?_⟩
    · have hlog := Real.log_lt_log (Real.exp_pos (-t)) hx.1
      rw [Real.log_exp] at hlog
      linarith
    · simpa only [neg_neg] using Real.exp_log hx0

/-- The finite Beta–pole Mellin convolution has the exact causal logarithmic pullback. -/
theorem suzukiCriticalPoleDensity_eq_mellin {omega t : ℝ} (ht : 0 < t) :
    ((Real.pi ^ omega * Real.exp (-t / 2) : ℝ) : ℂ) *
        positiveMellinConvolution
          (suzukiPrimaryBetaKernel omega) (suzukiPoleKernel omega) (Real.exp (-t)) =
      (suzukiCriticalPoleDensity omega t : ℂ) := by
  let F : ℝ → ℂ := fun y =>
    ((2 / Complex.Gamma (omega : ℂ)) *
      (y : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
      (1 - (y : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1)) *
        ((Real.exp (-t) / y : ℝ) : ℂ) ^ ((omega - 1 : ℝ) : ℂ) / y
  have hd : ∀ r ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-r)) (Ioo 0 t) r := by
    intro r _
    simpa using ((hasDerivAt_id r).neg.exp).hasDerivWithinAt
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd
    (Real.exp_injective.comp neg_injective).injOn F
  rw [image_exp_neg_interval ht] at he
  simp only [abs_neg, abs_of_pos (Real.exp_pos _)] at he
  rw [positiveMellinConvolution_primary_pole_eq_integral omega (Real.exp_pos _),
    integral_Ioc_eq_integral_Ioo]
  change ((Real.pi ^ omega * Real.exp (-t / 2) : ℝ) : ℂ) *
    (∫ y in Ioo (Real.exp (-t)) 1, F y) = _
  rw [he, ← integral_const_mul, suzukiCriticalPoleDensity, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have hp := suzukiPrimaryBetaKernel_eq_source omega (Real.exp_pos (-r))
    (Real.exp_lt_one_iff.mpr (by linarith [hr.1]))
  have hratio : Real.exp (-t) / Real.exp (-r) = Real.exp (-(t - r)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hpow : (Real.exp (-(t - r)) : ℂ) ^ ((omega - 1 : ℝ) : ℂ) =
      (Real.exp (-(t - r) * (omega - 1)) : ℂ) := by
    rw [← Complex.ofReal_cpow (Real.exp_pos _).le, ← Real.exp_mul]
  have hexp : Real.exp (-t / 2) * Real.exp (-(t - r) * (omega - 1)) =
      Real.exp (-r / 2) * Real.exp ((1 / 2 - omega) * (t - r)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hy : (Real.exp (-r) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  dsimp only [F]
  rw [← hp, hratio, hpow, Complex.real_smul, Complex.ofReal_mul,
    ofReal_suzukiCriticalPrimaryDensity hr.1]
  push_cast
  have heC := congrArg (fun x : ℝ => (x : ℂ)) hexp
  push_cast at heC
  field_simp
  linear_combination (Real.pi ^ omega : ℂ) *
    suzukiPrimaryBetaKernel omega (Real.exp (-r)) * heC

/-- Exact decomposition of the full signed archimedean density. -/
theorem suzukiCriticalArchDensity_eq {omega t : ℝ} (ht : 0 < t) :
    suzukiCriticalArchDensity omega t = suzukiCriticalPrimaryDensity omega t -
      2 * omega * suzukiCriticalPoleDensity omega t := by
  have hx := Real.exp_pos (-t)
  have hx1 := Real.exp_lt_one_iff.mpr (show -t < 0 by linarith)
  have hg : suzukiSourceG omega (Real.exp (-t)) =
      suzukiCanonicalG omega (Real.exp (-t)) := by
    rw [suzukiCanonicalG_eq_source omega hx hx1, suzukiSourceG, if_pos ⟨hx, hx1⟩]
  have hpi : (Real.pi : ℂ) ^ (omega : ℂ) = (Real.pi ^ omega : ℂ) :=
    (Complex.ofReal_cpow Real.pi_pos.le omega).symm
  have he : (Real.exp (-t / 2) : ℂ) * suzukiSourceG omega (Real.exp (-t)) =
      ((suzukiCriticalPrimaryDensity omega t -
        2 * omega * suzukiCriticalPoleDensity omega t : ℝ) : ℂ) := by
    rw [hg, suzukiCanonicalG, hpi]
    have hP := ofReal_suzukiCriticalPrimaryDensity (omega := omega) ht
    have hQ := suzukiCriticalPoleDensity_eq_mellin (omega := omega) ht
    push_cast at hP hQ ⊢
    linear_combination hP - (2 * (omega : ℂ)) * hQ
  have hr := congrArg Complex.re he
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, suzukiCriticalArchDensity] using hr

end
end RHTower
