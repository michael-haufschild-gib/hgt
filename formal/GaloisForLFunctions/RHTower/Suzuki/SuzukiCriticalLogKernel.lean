import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalBetaKernel

/-!
# The literal signed Suzuki kernel in logarithmic coordinates

The compact multiplicative Beta–pole convolution becomes a causal convolution
of the critical primary density with the growing exponential pole kernel.
The identity retains the pole before any testing or limiting operation.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The causal pole convolution at the critical Mellin line. -/
def suzukiCriticalPoleDensity (omega t : ℝ) : ℝ :=
  ∫ r in Ioo 0 t, suzukiCriticalPrimaryDensity omega r *
    Real.exp ((1 / 2 - omega) * (t - r))

/-- The literal full archimedean source at the critical Mellin line. -/
def suzukiCriticalSourceDensity (omega t : ℝ) : ℝ :=
  Real.exp (-t / 2) * (suzukiSourceG omega (Real.exp (-t))).re

/-- The primary density is the real logarithmic pullback of the literal Beta kernel. -/
theorem ofReal_suzukiCriticalPrimaryDensity (omega : ℝ) {t : ℝ} (ht : 0 < t) :
    (suzukiCriticalPrimaryDensity omega t : ℂ) =
      (Real.exp (-t / 2) : ℂ) * (Real.pi : ℂ) ^ (omega : ℂ) *
        suzukiPrimaryBetaKernel omega (Real.exp (-t)) := by
  have hx := Real.exp_pos (-t)
  have hx1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hp : suzukiPrimaryBetaKernel omega (Real.exp (-t)) =
      ((2 / Real.Gamma omega * Real.exp (-t) ^ (2 - omega) *
        (1 - Real.exp (-t) ^ 2) ^ (omega - 1) : ℝ) : ℂ) := by
    rw [suzukiPrimaryBetaKernel_eq_source omega hx hx1, Complex.Gamma_ofReal]
    have hb : 0 ≤ 1 - Real.exp (-t) ^ 2 := by nlinarith
    push_cast
    rw [Complex.ofReal_cpow hx.le, Complex.ofReal_cpow hb]
    push_cast
    rfl
  rw [suzukiCriticalPrimaryDensity, hp, Complex.ofReal_re,
    ← Complex.ofReal_cpow Real.pi_pos.le]
  push_cast
  ring

private theorem image_exp_neg_Ioo (t : ℝ) :
    (fun r : ℝ => Real.exp (-r)) '' Ioo 0 t = Ioo (Real.exp (-t)) 1 := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨Real.exp_lt_exp.mpr (by linarith [hr.2]),
      Real.exp_lt_one_iff.mpr (by linarith [hr.1])⟩
  · intro hy
    have hy0 : 0 < y := (Real.exp_pos _).trans hy.1
    have he : Real.exp (-(-Real.log y)) = y := by
      rw [neg_neg, Real.exp_log hy0]
    refine ⟨-Real.log y, ⟨neg_pos.mpr (Real.log_neg hy0 hy.2), ?_⟩, he⟩
    have h := hy.1
    rw [← he, Real.exp_lt_exp] at h
    linarith only [h]

private theorem pole_log_pullback (omega : ℝ) {t r : ℝ} (hr : r ∈ Ioo 0 t) :
    (Real.exp (-t / 2) : ℂ) * (Real.pi : ℂ) ^ (omega : ℂ) *
      (Real.exp (-r) •
        (((2 / Complex.Gamma (omega : ℂ)) *
          (Real.exp (-r) : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
          (1 - (Real.exp (-r) : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1)) *
          ((Real.exp (-t) / Real.exp (-r) : ℝ) : ℂ) ^ ((omega - 1 : ℝ) : ℂ) /
            Real.exp (-r))) =
      (suzukiCriticalPrimaryDensity omega r : ℂ) *
        (Real.exp ((1 / 2 - omega) * (t - r)) : ℂ) := by
  have hx : 0 < Real.exp (-r) := Real.exp_pos _
  have hx1 : Real.exp (-r) < 1 := Real.exp_lt_one_iff.mpr (by linarith [hr.1])
  rw [← suzukiPrimaryBetaKernel_eq_source omega hx hx1, Complex.real_smul,
    ofReal_suzukiCriticalPrimaryDensity omega hr.1]
  have hp : ((Real.exp (-t) / Real.exp (-r) : ℝ) : ℂ) ^
      ((omega - 1 : ℝ) : ℂ) = (Real.exp ((r - t) * (omega - 1)) : ℂ) := by
    rw [← Real.exp_sub, ← Complex.ofReal_cpow (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  have he : Real.exp (-t / 2) * Real.exp ((r - t) * (omega - 1)) =
      Real.exp (-r / 2) * Real.exp ((1 / 2 - omega) * (t - r)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hp]
  have hxC : (Real.exp (-r) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have heC := congrArg (fun x : ℝ => (x : ℂ)) he
  push_cast at heC
  have hcancel : (Real.exp (-r) : ℂ) *
      (suzukiPrimaryBetaKernel omega (Real.exp (-r)) *
        (Real.exp ((r - t) * (omega - 1)) : ℂ) / Real.exp (-r)) =
      suzukiPrimaryBetaKernel omega (Real.exp (-r)) *
        (Real.exp ((r - t) * (omega - 1)) : ℂ) := by
    field_simp
  rw [hcancel]
  calc
    _ = ((Real.exp (-t / 2) : ℂ) * (Real.exp ((r - t) * (omega - 1)) : ℂ)) *
        (Real.pi : ℂ) ^ (omega : ℂ) * suzukiPrimaryBetaKernel omega (Real.exp (-r)) := by ring
    _ = _ := by rw [heC]; ring

/-- Exact causal-convolution identity for the literal multiplicative pole term. -/
theorem ofReal_suzukiCriticalPoleDensity (omega t : ℝ) :
    (suzukiCriticalPoleDensity omega t : ℂ) =
      (Real.exp (-t / 2) : ℂ) * (Real.pi : ℂ) ^ (omega : ℂ) *
        positiveMellinConvolution
          (suzukiPrimaryBetaKernel omega) (suzukiPoleKernel omega) (Real.exp (-t)) := by
  rw [positiveMellinConvolution_primary_pole_eq_integral omega (Real.exp_pos _)]
  let F : ℝ → ℂ := fun y =>
    ((2 / Complex.Gamma (omega : ℂ)) * (y : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
      (1 - (y : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1)) *
      ((Real.exp (-t) / y : ℝ) : ℂ) ^ ((omega - 1 : ℝ) : ℂ) / y
  have hd : ∀ r ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-r)) (Ioo 0 t) r := by
    intro r _
    simpa using ((hasDerivAt_id r).neg.exp).hasDerivWithinAt
  have hi : InjOn (fun r : ℝ => Real.exp (-r)) (Ioo 0 t) :=
    (Real.exp_injective.comp neg_injective).injOn
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hi F
  rw [image_exp_neg_Ioo] at he
  simp only [abs_neg, abs_of_pos (Real.exp_pos _)] at he
  change (suzukiCriticalPoleDensity omega t : ℂ) =
    (Real.exp (-t / 2) : ℂ) * (Real.pi : ℂ) ^ (omega : ℂ) * ∫ y in Ioc (Real.exp (-t)) 1, F y
  rw [integral_Ioc_eq_integral_Ioo, he, ← integral_const_mul,
    suzukiCriticalPoleDensity, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  rw [Complex.ofReal_mul]
  exact (pole_log_pullback omega hr).symm

/-- The complete signed source is primary density minus its exact pole convolution. -/
theorem suzukiCriticalSourceDensity_eq (omega : ℝ) {t : ℝ} (ht : 0 < t) :
    suzukiCriticalSourceDensity omega t =
      suzukiCriticalPrimaryDensity omega t - 2 * omega * suzukiCriticalPoleDensity omega t := by
  have hx : 0 < Real.exp (-t) := Real.exp_pos _
  have hx1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsource : suzukiSourceG omega (Real.exp (-t)) =
      suzukiCanonicalG omega (Real.exp (-t)) := by
    rw [suzukiSourceG, if_pos ⟨hx, hx1⟩,
      suzukiCanonicalG_eq_source omega hx hx1]
  have he : (Real.exp (-t / 2) : ℂ) * suzukiSourceG omega (Real.exp (-t)) =
      ((suzukiCriticalPrimaryDensity omega t -
        2 * omega * suzukiCriticalPoleDensity omega t : ℝ) : ℂ) := by
    rw [hsource, suzukiCanonicalG]
    push_cast
    rw [ofReal_suzukiCriticalPrimaryDensity omega ht,
      ofReal_suzukiCriticalPoleDensity omega t]
    push_cast
    ring
  have hr := congrArg Complex.re he
  simpa only [suzukiCriticalSourceDensity, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using hr

end
end RHTower
