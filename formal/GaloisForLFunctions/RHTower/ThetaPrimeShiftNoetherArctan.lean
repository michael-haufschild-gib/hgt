import GaloisForLFunctions.RHTower.ThetaPrimeShiftNoetherAction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Strictly positive local arithmetic action responses

Every translated arctangent is a bounded increasing scaling profile.
Each prime link therefore contributes nonnegatively to its action
variation, and the prime two contributes strictly positively on an open
set. The full action response is strictly positive. For the actual theta
source this is an unconditional family of weighted Gamma/pole inequalities.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace RHTower.ThetaSourceWard

theorem thetaPrimeLinkDensity_eq_real (S T : ThetaSource) (p : ℕ × ℝ) :
    thetaPrimeLinkDensity S T p =
      ((ArithmeticFunction.vonMangoldt p.1 / Real.sqrt p.1 * T.k p.2 *
        S.k (p.2 + Real.log p.1) : ℝ) : ℂ) := by
  simp only [thetaPrimeLinkDensity, primeShiftActionDensity, primeCoefficient_eq,
    Complex.ofReal_mul]

theorem thetaPrimeLinkDensity_re_nonneg (S T : ThetaSource) (p : ℕ × ℝ) :
    0 ≤ (thetaPrimeLinkDensity S T p).re := by
  rw [thetaPrimeLinkDensity_eq_real, Complex.ofReal_re]
  exact mul_nonneg (mul_nonneg
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)) (T.pos _).le)
      (S.pos _).le

theorem thetaPrimeLinkDensity_two_re_pos (S T : ThetaSource) (x : ℝ) :
    0 < (thetaPrimeLinkDensity S T (2, x)).re := by
  rw [thetaPrimeLinkDensity_eq_real, Complex.ofReal_re,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact mul_pos (mul_pos (div_pos (Real.log_pos one_lt_two)
    (Real.sqrt_pos.mpr zero_lt_two)) (T.pos x)) (S.pos _)

/-- Bounded local reciprocal scaling centered at an arbitrary source coordinate. -/
def thetaPrimeArctanProfile (r : ℝ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (Real.arctan (x - r) : ℂ))
    (Complex.continuous_ofReal.comp
      (Real.continuous_arctan.comp (continuous_id.sub continuous_const))) (Real.pi / 2)
    (fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩)

theorem thetaPrimeArctanProfile_apply (r x : ℝ) :
    thetaPrimeArctanProfile r x = (Real.arctan (x - r) : ℂ) := rfl

theorem thetaPrimeArctanResponse_density (S T : ThetaSource) (r : ℝ) (p : ℕ × ℝ) :
    (thetaPrimeProfileIncrement (thetaPrimeArctanProfile r) p * thetaPrimeLinkDensity S T p).re =
      (Real.arctan (p.2 + Real.log p.1 - r) - Real.arctan (p.2 - r)) *
        (thetaPrimeLinkDensity S T p).re := by
  simp only [thetaPrimeProfileIncrement, thetaPrimeArctanProfile_apply,
    ← Complex.ofReal_sub, Complex.re_ofReal_mul]

/-- Positive arithmetic links give a strictly positive response to every translated arctangent. -/
theorem thetaPrimeLocalResponse_arctan_re_pos (S T : ThetaSource) (r : ℝ) :
    0 < (thetaPrimeLocalResponse S T (thetaPrimeArctanProfile r)).re := by
  letI : (Measure.count : Measure ℕ).IsOpenPosMeasure :=
    ⟨fun _ _ h => Measure.count_ne_zero h⟩
  have hi := integrable_thetaPrimeLocalResponse S T (thetaPrimeArctanProfile r)
  change Integrable (fun p => thetaPrimeProfileIncrement (thetaPrimeArctanProfile r) p *
    thetaPrimeLinkDensity S T p) thetaPrimeLinkMeasure at hi
  change 0 < (∫ p, thetaPrimeProfileIncrement (thetaPrimeArctanProfile r) p *
    thetaPrimeLinkDensity S T p ∂thetaPrimeLinkMeasure).re
  have he : (∫ p, (thetaPrimeProfileIncrement (thetaPrimeArctanProfile r) p *
      thetaPrimeLinkDensity S T p).re ∂thetaPrimeLinkMeasure) =
    (∫ p, thetaPrimeProfileIncrement (thetaPrimeArctanProfile r) p *
      thetaPrimeLinkDensity S T p ∂thetaPrimeLinkMeasure).re := integral_re hi
  rw [← he]
  apply integral_pos_of_integrable_nonneg_nonzero
    (x := (2, (0 : ℝ)))
    (Complex.continuous_re.comp
      ((continuous_thetaPrimeProfileIncrement _).mul (continuous_thetaPrimeLinkDensity S T)))
    hi.re
  · intro p
    change 0 ≤ (thetaPrimeProfileIncrement (thetaPrimeArctanProfile r) p *
      thetaPrimeLinkDensity S T p).re
    rw [thetaPrimeArctanResponse_density]
    apply mul_nonneg _ (thetaPrimeLinkDensity_re_nonneg S T p)
    apply sub_nonneg.mpr
    apply Real.arctan_mono
    linarith [Real.log_natCast_nonneg p.1]
  · apply ne_of_gt
    change 0 < (thetaPrimeProfileIncrement (thetaPrimeArctanProfile r) (2, 0) *
      thetaPrimeLinkDensity S T (2, 0)).re
    rw [thetaPrimeArctanResponse_density]
    apply mul_pos _ (thetaPrimeLinkDensity_two_re_pos S T 0)
    apply sub_pos.mpr
    apply Real.arctan_strictMono
    have hl : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
    simpa only [Nat.cast_ofNat, zero_add, add_zero, zero_sub] using
      sub_lt_sub_right (lt_add_of_pos_left (0 : ℝ) hl) r

/-- The explicit Gamma/pole exchange is positive against every translated arctangent. -/
theorem integral_arctan_thetaNoetherExchange_re_pos (r : ℝ) :
    0 < (∫ x : ℝ, (Real.arctan (x - r) : ℂ) * thetaNoetherExchange x).re := by
  have h := thetaPrimeLocalResponse_arctan_re_pos thetaCuspTiltSource thetaCuspTiltSource r
  rw [thetaPrimeLocalResponse_actual] at h
  exact h

/-- The actual arithmetic action has a strict local scaling direction at every center. -/
theorem deriv_thetaPrimeLocalAction_arctan_re_pos (r : ℝ) :
    0 < (deriv (thetaPrimeLocalAction thetaCuspTiltSource thetaCuspTiltSource
      (thetaPrimeArctanProfile r)) 0).re := by
  rw [(hasDerivAt_thetaPrimeLocalAction_zero _ _ _).deriv]
  exact thetaPrimeLocalResponse_arctan_re_pos _ _ r

end RHTower.ThetaSourceWard
