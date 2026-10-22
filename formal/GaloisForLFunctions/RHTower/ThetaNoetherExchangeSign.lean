import GaloisForLFunctions.RHTower.ThetaPrimeShiftNoetherIntegrated
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCenterMixedThreePoint

/-!
# Orientation of the actual arithmetic exchange

Strict radial decrease of the actual theta source orders the two ends of
every prime shift. All prime-power contributions to the outward exchange
are nonnegative, and the prime two makes the sum strictly positive.
Consequently the Gamma/pole exchange has exactly the sign of its source
coordinate, and the positive arithmetic current decreases strictly on the
positive half-line. These are source identities, not a claim of spectral
positive definiteness.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower.ThetaSourceWard

private theorem thetaSource_strictAntiOn :
    StrictAntiOn thetaCuspFullSource (Ici (0 : ℝ)) := by
  intro s hs t ht hst
  have h := strictAntiOn_thetaCuspFullSource_mul_reflect 0 hs ht hst
  simp only [zero_add, zero_sub, thetaCuspFullSource_neg] at h
  nlinarith [thetaCuspFullSource_pos_all s, thetaCuspFullSource_pos_all t]

private theorem thetaSource_abs (x : ℝ) :
    thetaCuspFullSource |x| = thetaCuspFullSource x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, thetaCuspFullSource_neg]

private theorem thetaPrime_reflection_difference (n : ℕ) (x : ℝ) :
    (primeSourceTerm thetaCuspTiltSource n (-x) -
      primeSourceTerm thetaCuspTiltSource n x).re =
      ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (thetaCuspFullSource (x - Real.log n) - thetaCuspFullSource (x + Real.log n)) := by
  simp only [primeSourceTerm, primeCoefficient_eq, thetaCuspTiltSource_k,
    ← Complex.ofReal_mul, Complex.sub_re, Complex.ofReal_re]
  rw [show -x + Real.log n = -(x - Real.log n) by ring, thetaCuspFullSource_neg]
  ring

theorem thetaNoetherExchange_re_prime_sum (x : ℝ) :
    (thetaNoetherExchange x).re = thetaCuspFullSource x *
      ∑' n : ℕ, (primeSourceTerm thetaCuspTiltSource n (-x) -
        primeSourceTerm thetaCuspTiltSource n x).re := by
  have hs := (summable_primeSourceTerm thetaCuspTiltSource (-x)).sub
    (summable_primeSourceTerm thetaCuspTiltSource x)
  have he : thetaNoetherExchange x = (thetaCuspFullSource x : ℂ) *
      (fullPrimeSource thetaCuspTiltSource (-x) - fullPrimeSource thetaCuspTiltSource x) := by
    rw [thetaNoetherExchange_eq, fullPrimeShiftWardDivergence]
    simp only [thetaCuspTiltSource_k]
    ring
  rw [he, fullPrimeSource, fullPrimeSource,
    ← Summable.tsum_sub (summable_primeSourceTerm thetaCuspTiltSource (-x))
      (summable_primeSourceTerm thetaCuspTiltSource x), Complex.re_ofReal_mul,
    Complex.re_tsum hs]

private theorem thetaNoetherExchange_re_pos {x : ℝ} (hx : 0 < x) :
    0 < (thetaNoetherExchange x).re := by
  rw [thetaNoetherExchange_re_prime_sum]
  apply mul_pos (thetaCuspFullSource_pos_all x)
  have hs := (Complex.hasSum_re
    ((summable_primeSourceTerm thetaCuspTiltSource (-x)).sub
      (summable_primeSourceTerm thetaCuspTiltSource x)).hasSum).summable
  refine hs.tsum_pos ?_ 2 ?_
  · intro n
    rw [thetaPrime_reflection_difference]
    apply mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    apply sub_nonneg.mpr
    have hl := Real.log_natCast_nonneg n
    have hb : |x - Real.log n| ≤ x + Real.log n := abs_le.mpr ⟨by linarith, by linarith⟩
    simpa only [thetaSource_abs] using thetaSource_strictAntiOn.antitoneOn
      (abs_nonneg (x - Real.log n)) (by linarith : 0 ≤ x + Real.log n) hb
  · rw [thetaPrime_reflection_difference, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    have hl : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
    apply mul_pos (div_pos hl (Real.sqrt_pos.mpr zero_lt_two))
    apply sub_pos.mpr
    have hb : |x - Real.log (2 : ℝ)| < x + Real.log (2 : ℝ) :=
      abs_lt.mpr ⟨by linarith, by linarith⟩
    simpa only [Nat.cast_ofNat, thetaSource_abs] using thetaSource_strictAntiOn
      (abs_nonneg (x - Real.log (2 : ℝ)))
      (by linarith : 0 ≤ x + Real.log (2 : ℝ)) hb

theorem thetaNoetherExchange_neg (x : ℝ) :
    thetaNoetherExchange (-x) = -thetaNoetherExchange x := by
  simp only [thetaNoetherExchange_eq, fullPrimeShiftWardDivergence,
    thetaCuspTiltSource_k, thetaCuspFullSource_neg, neg_neg]
  ring

theorem thetaNoetherExchange_zero : thetaNoetherExchange 0 = 0 := by
  simp [thetaNoetherExchange]

/-- The literal arithmetic exchange points outward at every nonzero source coordinate. -/
theorem thetaNoetherExchange_re_pos_iff (x : ℝ) :
    0 < (thetaNoetherExchange x).re ↔ 0 < x := by
  constructor
  · intro h
    by_contra hx
    rcases lt_or_eq_of_le (le_of_not_gt hx) with hx | rfl
    · have hn := thetaNoetherExchange_re_pos (neg_pos.mpr hx)
      rw [thetaNoetherExchange_neg, Complex.neg_re] at hn
      linarith
    · simp only [thetaNoetherExchange_zero, Complex.zero_re, lt_self_iff_false] at h
  · exact thetaNoetherExchange_re_pos

theorem thetaNoetherExchange_re_neg_iff (x : ℝ) :
    (thetaNoetherExchange x).re < 0 ↔ x < 0 := by
  have h := thetaNoetherExchange_re_pos_iff (-x)
  simpa only [thetaNoetherExchange_neg, Complex.neg_re, neg_pos] using h

theorem thetaNoetherExchange_eq_zero_iff (x : ℝ) :
    thetaNoetherExchange x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have hn := (thetaNoetherExchange_re_neg_iff x).mpr hx
      simp [h] at hn
    · exact hx
    · have hp := (thetaNoetherExchange_re_pos_iff x).mpr hx
      simp [h] at hp
  · rintro rfl
    exact thetaNoetherExchange_zero

/-- The positive arithmetic current loses charge strictly along the positive half-line. -/
theorem strictAntiOn_thetaNoetherCurrent_re :
    StrictAntiOn
      (fun x : ℝ => (fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource x).re)
      (Ici 0) := by
  have hd (x : ℝ) : HasDerivAt
      (fun y : ℝ => (fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource y).re)
      (-(thetaNoetherExchange x).re) x := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource x)
    convert! h using 1
    simp [thetaNoetherExchange_eq]
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    ((continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt).continuousOn)
  intro x hx
  have hx' : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  rw [(hd x).deriv]
  exact neg_neg_of_pos ((thetaNoetherExchange_re_pos_iff x).mpr hx')

/-- Reflection preserves the self-paired prime current for every even theta source. -/
theorem fullPrimeShiftNoetherCurrent_self_neg (S : ThetaSource) (x : ℝ) :
    fullPrimeShiftNoetherCurrent S S (-x) = fullPrimeShiftNoetherCurrent S S x := by
  have hd (y : ℝ) : HasDerivAt
      (fun z : ℝ => fullPrimeShiftNoetherCurrent S S (-z) - fullPrimeShiftNoetherCurrent S S z)
      0 y := by
    have hn : HasDerivAt (fun z : ℝ => fullPrimeShiftNoetherCurrent S S (-z))
        (-fullPrimeShiftWardDivergence S S (-y)) y := by
      convert! (hasDerivAt_fullPrimeShiftNoetherCurrent S S (-y)).scomp y
        (hasDerivAt_id y).neg using 1
      simp
    have h := hn.sub (hasDerivAt_fullPrimeShiftNoetherCurrent S S y)
    convert! h using 1
    simp only [fullPrimeShiftWardDivergence, S.even', neg_neg]
    ring
  have h := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
    (fun y => (hd y).deriv) x 0
  simpa only [neg_zero, sub_self, sub_eq_zero] using h

/-- The current has a unique global maximum at the reflection center. -/
theorem thetaNoetherCurrent_re_lt_center_iff (x : ℝ) :
    (fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource x).re <
      (fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource 0).re ↔ x ≠ 0 := by
  constructor
  · intro h hx
    subst x
    exact (lt_irrefl _ h)
  · intro hx
    have h := strictAntiOn_thetaNoetherCurrent_re (show (0 : ℝ) ∈ Ici 0 from by simp)
      (abs_nonneg x) (abs_pos.mpr hx)
    rcases le_total 0 x with hx | hx
    · simpa only [abs_of_nonneg hx] using h
    · simpa only [abs_of_nonpos hx, fullPrimeShiftNoetherCurrent_self_neg] using h

/-- The accumulated arithmetic exchange is positive at every noncentral point. -/
theorem integral_thetaNoetherExchange_finite_re_pos_iff (x : ℝ) :
    0 < (∫ y in (0 : ℝ)..x, thetaNoetherExchange y).re ↔ x ≠ 0 := by
  have he : (∫ y in (0 : ℝ)..x, thetaNoetherExchange y) =
      fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource 0 -
        fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource x := by
    simp only [thetaNoetherExchange_eq, intervalIntegral.integral_neg,
      ← fullPrimeShiftNoetherCurrent_sub, neg_sub]
  rw [he, Complex.sub_re, sub_pos, thetaNoetherCurrent_re_lt_center_iff]

end RHTower.ThetaSourceWard
