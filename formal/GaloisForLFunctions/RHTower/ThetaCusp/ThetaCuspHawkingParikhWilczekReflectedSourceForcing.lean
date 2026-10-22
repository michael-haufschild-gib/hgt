import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekEulerCurrentDomainUniqueness
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusConnection

/-!
# Complete PW reflected forcing and arithmetic-current transport

Positive-gain reflection changes the connection shift and retains the complete
forcing. For the original Gamma profile, the same-shift forcing mismatch is
nonzero at every shift. The inverse-gain companion fixes that profile and has
exact forcing covariance at every shift, while its unshifted forcing is nonzero.

The full arithmetic current is conjugated to a weighted inverse-dilation current;
its summability and every coefficient are retained. The canonical Mobius
connection transports with its full source term. The Gamma profile is explicitly
excluded from the exponentially decreasing Schwartz source used by that identity.
No source-class identification, vanishing Ward law, or RH conclusion is assumed.
-/

set_option backward.isDefEq.respectTransparency false

open Real GaloisForLFunctions Filter Topology ArithmeticFunction SchwartzMap
namespace RHTower
noncomputable section

private theorem pwGain_ne_zero (t : ℝ) : (pwLogSingularGain t : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

theorem pwLogSingularComplexReflection_involutive :
    Function.Involutive pwLogSingularComplexReflection := by
  intro f
  funext t
  simp only [pwLogSingularComplexReflection, neg_neg, pwLogSingularGain_neg,
    Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ (pwGain_ne_zero t), one_mul]

private theorem pwGain_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u => (pwLogSingularGain u : ℂ))
      (2 * (pwLogSingularConnectionPotential t : ℂ) * (pwLogSingularGain t : ℂ)) t := by
  have h := ((hasDerivAt_pwLogSingularGaugePotential t).const_mul 2).exp.ofReal_comp
  exact h.congr_deriv (by unfold pwLogSingularGain; push_cast; ring)

/-- The full forcing changes sign under the opposite-shift reflected connection. -/
theorem pwLogSingularComplexReflection_forced_derivative (z : ℂ) (f r : ℝ → ℂ)
    (hf : ∀ u, HasDerivAt f (((pwLogSingularConnectionPotential u : ℂ) + z) * f u + r u) u)
    (t : ℝ) :
    HasDerivAt (pwLogSingularComplexReflection f)
      (((pwLogSingularConnectionPotential t : ℂ) - z) *
        pwLogSingularComplexReflection f t - pwLogSingularComplexReflection r t) t := by
  have hn : HasDerivAt (fun u : ℝ => -u) (-1) t := hasDerivAt_neg t
  have hr := (hf (-t)).scomp t hn
  exact ((pwGain_hasDerivAt t).mul hr).congr_deriv (by
    simp only [Function.comp_apply, pwLogSingularComplexReflection, pwLogSingularConnectionPotential,
      Real.cosh_neg, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat, neg_smul, one_smul]
    ring)

/-- At the same shift, the extra spectral forcing is retained as well. -/
theorem pwLogSingularComplexReflection_same_shift_derivative (z : ℂ) (f r : ℝ → ℂ)
    (hf : ∀ u, HasDerivAt f (((pwLogSingularConnectionPotential u : ℂ) + z) * f u + r u) u)
    (t : ℝ) :
    HasDerivAt (pwLogSingularComplexReflection f)
      (((pwLogSingularConnectionPotential t : ℂ) + z) *
        pwLogSingularComplexReflection f t +
        (-pwLogSingularComplexReflection r t - 2 * z * pwLogSingularComplexReflection f t)) t := by
  exact (pwLogSingularComplexReflection_forced_derivative z f r hf t).congr_deriv (by ring)

/-- Complete forcing of the literal Gamma source, without discarding its first winding. -/
def pwGammaConnectionForcing (z : ℂ) (t : ℝ) : ℂ :=
  ((1 - Real.exp t - Real.cosh t : ℝ) - z) * (expShift (1 / 2) 0 t : ℂ)

theorem pwGammaConnectionForcing_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (fun u => (expShift (1 / 2) 0 u : ℂ))
      (((pwLogSingularConnectionPotential t : ℂ) + z) * (expShift (1 / 2) 0 t : ℂ) +
        pwGammaConnectionForcing z t) t := by
  have h := (((hasDerivAt_id t).const_mul (1 / 2 : ℝ)).sub (Real.hasDerivAt_exp t)).exp.ofReal_comp
  convert h using 1
  · ext u
    simp [expShift]
  · dsimp [pwGammaConnectionForcing, pwLogSingularConnectionPotential, expShift]
    push_cast
    ring

/-- No complex shift removes the nonzero reflected source term at the fixed point. -/
theorem pwGammaConnectionForcing_reflection_defect (z : ℂ) :
    pwGammaConnectionForcing z 0 -
      (-pwLogSingularComplexReflection (pwGammaConnectionForcing z) 0 -
        2 * z * pwLogSingularComplexReflection (fun u => (expShift (1 / 2) 0 u : ℂ)) 0) =
      -2 * (Real.exp (-1) : ℂ) := by
  simp only [pwGammaConnectionForcing, pwLogSingularComplexReflection, pwLogSingularGain,
    pwLogSingularGaugePotential, expShift, neg_zero, Real.sinh_zero, Real.cosh_zero,
    Real.exp_zero, zero_div, sub_zero, mul_zero, zero_sub, Nat.cast_zero, add_zero]
  push_cast
  ring

theorem pwGammaConnectionForcing_ne_reflected (z : ℂ) :
    pwGammaConnectionForcing z ≠ (fun t =>
      -pwLogSingularComplexReflection (pwGammaConnectionForcing z) t -
        2 * z * pwLogSingularComplexReflection (fun u => (expShift (1 / 2) 0 u : ℂ)) t) := by
  intro heq
  have h := pwGammaConnectionForcing_reflection_defect z
  rw [congrFun heq 0, sub_self] at h
  have hne : (-2 : ℂ) * (Real.exp (-1) : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero)
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  exact hne h.symm

/-- The negative tail of the literal source violates even the unit exponential weight. -/
theorem pwGammaSource_negative_weight_unbounded (C : ℝ) :
    ∃ v : ℝ, 0 ≤ v ∧ C < Real.exp (|-v|) * ‖(expShift (1 / 2) 0 (-v) : ℂ)‖ := by
  let v : ℝ := 2 * (|C| + 2)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have he : Real.exp (-v) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr hv)
  have h := Real.add_one_le_exp (v / 2 - Real.exp (-v))
  have hC : C < Real.exp (v / 2 - Real.exp (-v)) := by
    dsimp [v] at h
    linarith [le_abs_self C]
  refine ⟨v, hv, ?_⟩
  have hval : Real.exp (|-v|) * ‖(expShift (1 / 2) 0 (-v) : ℂ)‖ =
      Real.exp (v / 2 - Real.exp (-v)) := by
    rw [Complex.norm_real, expShift, Real.norm_of_nonneg (Real.exp_pos _).le]
    simp only [abs_neg, abs_of_nonneg hv, Nat.cast_zero, add_zero, ← Real.exp_add]
    congr 1
    ring
  rwa [hval]

/-- The bare Gamma profile cannot be silently used as an exponentially decreasing Schwartz source. -/
theorem pwGammaSource_not_deningerExpSchwartz :
    ¬ ∃ h : 𝓢(ℝ, ℂ), h ∈ DeningerExpSchwartz ∧
      ∀ t : ℝ, h t = (expShift (1 / 2) 0 t : ℂ) := by
  rintro ⟨h, hh, hq⟩
  obtain ⟨C, hC⟩ := hh 1 0
  obtain ⟨v, _, hv⟩ := pwGammaSource_negative_weight_unbounded C
  have hb := hC (-v)
  rw [norm_iteratedFDeriv_zero, hq, one_mul] at hb
  exact (not_lt_of_ge hb) hv

/-- The companion weighted reflection, using the inverse singular gain. -/
def pwLogInverseGainReflection (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (pwLogSingularGain t : ℂ)⁻¹ * f (-t)

theorem pwGammaSource_gain_transport (t : ℝ) :
    (pwLogSingularGain t : ℂ) * (expShift (1 / 2) 0 t : ℂ) =
      (expShift (1 / 2) 0 (-t) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  simp only [pwLogSingularGain, pwLogSingularGaugePotential, expShift,
    Nat.cast_zero, add_zero, ← Real.exp_add, Real.sinh_eq]
  congr 1
  ring

/-- The inverse-gain companion fixes the literal source; this does not assert horizontality. -/
theorem pwLogInverseGainReflection_gamma_fixed :
    pwLogInverseGainReflection (fun t => (expShift (1 / 2) 0 t : ℂ)) =
      fun t => (expShift (1 / 2) 0 t : ℂ) := by
  funext t
  unfold pwLogInverseGainReflection
  change (pwLogSingularGain t : ℂ)⁻¹ * (expShift (1 / 2) 0 (-t) : ℂ) = _
  rw [← pwGammaSource_gain_transport, inv_mul_cancel_left₀ (pwGain_ne_zero t)]

/-- The full forcing for the inverse connection retains the hyperbolic source term. -/
def pwGammaInverseConnectionForcing (z : ℂ) (t : ℝ) : ℂ :=
  (-(Real.sinh t : ℂ) - z) * (expShift (1 / 2) 0 t : ℂ)

theorem pwGammaInverseConnectionForcing_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (fun u => (expShift (1 / 2) 0 u : ℂ))
      ((-(pwLogSingularConnectionPotential t : ℂ) + z) * (expShift (1 / 2) 0 t : ℂ) +
        pwGammaInverseConnectionForcing z t) t := by
  exact (pwGammaConnectionForcing_hasDerivAt z t).congr_deriv (by
    unfold pwGammaConnectionForcing pwGammaInverseConnectionForcing pwLogSingularConnectionPotential
    rw [Real.sinh_eq, Real.cosh_eq]
    push_cast
    ring)

/-- Source fixation makes the same-shift forcing match for every shift, not just a wall label. -/
theorem pwGammaInverseConnectionForcing_reflected_balance (z : ℂ) (t : ℝ) :
    -pwLogInverseGainReflection (pwGammaInverseConnectionForcing z) t -
      2 * z * pwLogInverseGainReflection (fun u => (expShift (1 / 2) 0 u : ℂ)) t =
        pwGammaInverseConnectionForcing z t := by
  have hq := congrFun pwLogInverseGainReflection_gamma_fixed t
  change (pwLogSingularGain t : ℂ)⁻¹ * (expShift (1 / 2) 0 (-t) : ℂ) = _ at hq
  unfold pwLogInverseGainReflection pwGammaInverseConnectionForcing
  rw [Real.sinh_neg, Complex.ofReal_neg]
  calc
    _ = ((-(Real.sinh t : ℂ) - z) *
        ((pwLogSingularGain t : ℂ)⁻¹ * (expShift (1 / 2) 0 (-t) : ℂ))) := by ring
    _ = _ := by rw [hq]

/-- Even the source-fixed, zero-shift companion has a nonzero complete forcing. -/
theorem pwGammaInverseConnectionForcing_zero_ne_zero :
    pwGammaInverseConnectionForcing 0 ≠ 0 := by
  have hs : Real.sinh 1 ≠ 0 := ne_of_gt
    (lt_of_lt_of_le zero_lt_one (HTGeometry.self_le_sinh_of_nonneg zero_le_one))
  have hq : (expShift (1 / 2) 0 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hne := mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hs)) hq
  intro heq
  apply hne
  simpa only [pwGammaInverseConnectionForcing, sub_zero, Pi.zero_apply] using congrFun heq 1

/-- The outgoing arithmetic current with all coefficients retained. -/
def pwArithmeticCurrentTerm (c : ℕ → ℂ) (f : ℝ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  c n * f (t + Real.log (n : ℝ))

/-- Exact inverse-dilation current forced by singular reflection. -/
def pwReflectedArithmeticCurrentTerm (c : ℕ → ℂ) (f : ℝ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  c n * ((pwLogSingularGain t : ℂ) /
    (pwLogSingularGain (t - Real.log (n : ℝ)) : ℂ)) * f (t - Real.log (n : ℝ))

theorem pwReflectedArithmeticCurrentTerm_transport (c : ℕ → ℂ) (f : ℝ → ℂ)
    (t : ℝ) (n : ℕ) :
    pwReflectedArithmeticCurrentTerm c (pwLogSingularComplexReflection f) t n =
      (pwLogSingularGain t : ℂ) * pwArithmeticCurrentTerm c f (-t) n := by
  unfold pwReflectedArithmeticCurrentTerm pwArithmeticCurrentTerm pwLogSingularComplexReflection
  rw [show -(t - Real.log (n : ℝ)) = -t + Real.log (n : ℝ) by ring]
  field_simp [pwGain_ne_zero (t - Real.log (n : ℝ))]

theorem pwReflectedArithmeticCurrent_summable_iff (c : ℕ → ℂ) (f : ℝ → ℂ) (t : ℝ) :
    Summable (pwReflectedArithmeticCurrentTerm c (pwLogSingularComplexReflection f) t) ↔
      Summable (pwArithmeticCurrentTerm c f (-t)) := by
  have heq : pwReflectedArithmeticCurrentTerm c (pwLogSingularComplexReflection f) t =
      fun n => (pwLogSingularGain t : ℂ) * pwArithmeticCurrentTerm c f (-t) n :=
    funext (pwReflectedArithmeticCurrentTerm_transport c f t)
  rw [heq]
  exact summable_mul_left_iff (pwGain_ne_zero t)

theorem pwReflectedArithmeticCurrent_tsum_transport (c : ℕ → ℂ) (f : ℝ → ℂ) (t : ℝ) :
    (∑' n : ℕ, pwReflectedArithmeticCurrentTerm c (pwLogSingularComplexReflection f) t n) =
      pwLogSingularComplexReflection (fun u => ∑' n : ℕ, pwArithmeticCurrentTerm c f u n) t := by
  simp_rw [pwReflectedArithmeticCurrentTerm_transport]
  exact tsum_mul_left

/-- On the actual canonical preimage, the full reflected current retains the Möbius derivative. -/
theorem pwReflectedMobius_connection {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (t : ℝ) :
    (∑' n : ℕ, pwReflectedArithmeticCurrentTerm (fun n => (vonMangoldt n : ℂ))
      (pwLogSingularComplexReflection (fun u => deningerMobiusPreimage h (Real.exp u))) t n) =
      (pwLogSingularGain t : ℂ) * deningerMobiusDerivative h (Real.exp (-t)) := by
  rw [pwReflectedArithmeticCurrent_tsum_transport]
  unfold pwLogSingularComplexReflection
  congr 1
  calc
    (∑' n : ℕ, pwArithmeticCurrentTerm (fun n => (vonMangoldt n : ℂ))
        (fun u => deningerMobiusPreimage h (Real.exp u)) (-t) n) =
        ∑' n : ℕ, (vonMangoldt n : ℂ) * deningerMobiusPreimage h ((n : ℝ) * Real.exp (-t)) := by
      apply tsum_congr
      intro n
      exact pwEulerCurrentTerm_logPull (deningerMobiusPreimage h) (-t) n
    _ = _ := deningerMobius_connection hh (Real.exp_pos (-t))

/-- A closed statement retaining the nonzero Gamma source obstruction at every shift. -/
theorem pwGamma_reflected_same_forcing_impossible :
    ∀ z : ℂ, ¬ ∃ r : ℝ → ℂ,
      (∀ t, HasDerivAt (fun u => (expShift (1 / 2) 0 u : ℂ))
        (((pwLogSingularConnectionPotential t : ℂ) + z) * (expShift (1 / 2) 0 t : ℂ) + r t) t) ∧
      (∀ t, HasDerivAt (pwLogSingularComplexReflection (fun u => (expShift (1 / 2) 0 u : ℂ)))
        (((pwLogSingularConnectionPotential t : ℂ) + z) *
          pwLogSingularComplexReflection (fun u => (expShift (1 / 2) 0 u : ℂ)) t + r t) t) := by
  intro z
  rintro ⟨r, hr, hTr⟩
  have heq : r = pwGammaConnectionForcing z := by
    funext t
    exact add_left_cancel ((hr t).unique (pwGammaConnectionForcing_hasDerivAt z t))
  subst r
  apply pwGammaConnectionForcing_ne_reflected z
  funext t
  exact add_left_cancel ((hTr t).unique
    (pwLogSingularComplexReflection_same_shift_derivative z _ _
      (pwGammaConnectionForcing_hasDerivAt z) t))

end
end RHTower
