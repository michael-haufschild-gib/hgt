import GaloisForLFunctions.RHTower.OrbitwiseSourceDivisorSeam
import GaloisForLFunctions.RHTower.RayCompleteTranslationFaithful
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Static translation-value rigidity of the von Mangoldt source

The moving completed prime--Gamma trace separates into an archimedean value difference and the
translated von Mangoldt value difference.  This file proves that the prime difference is a
faithful static value constraint: if a complex translation leaves the actual all-prime source
unchanged cofinally on the real Euler ray, then the translation is zero.

The proof first recovers every translated prime-power coefficient from the cofinal L-series
values.  Those coefficients are the values of the Euler translation characters.  Ray-complete
translation faithfulness then kills the operator `T_h - 1`.  Thus the argument retains the full
unsquared prime carrier and does not use a continuation path, a finite prime cutoff, or the Xi
divisor.  It supplies source marking, not the still-missing orientation/positivity theorem for RH.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- A translated von Mangoldt coefficient on a prime-power ray is the corresponding Euler
translation-character value times `log p`. -/
theorem shiftedVonMangoldtCoeff_prime_pow_exp (h : ℂ) {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0) :
    shiftedVonMangoldtCoeff h (p ^ m) =
      (Real.log p : ℂ) *
        Complex.exp (-(((m : ℝ) * Real.log p : ℝ) : ℂ) * h) := by
  rw [shiftedVonMangoldtCoeff,
    ArithmeticFunction.vonMangoldt_apply_pow hm,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hpm0 : ((p ^ m : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero m hp.ne_zero
  have hlog : Complex.log ((p ^ m : ℕ) : ℂ) =
      (((m : ℝ) * Real.log p : ℝ) : ℂ) := by
    have hlogR : Real.log ((p ^ m : ℕ) : ℝ) =
        (m : ℝ) * Real.log (p : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity), hlogR]
  rw [Complex.cpow_def_of_ne_zero hpm0, hlog, div_eq_mul_inv,
    ← Complex.exp_neg]
  congr 1
  ring_nf

/-- Static cofinal value constraint for a translation of the von Mangoldt L-series. -/
def VonMangoldtTranslationValueConstraint (h : ℂ) : Prop :=
  (fun x : ℝ =>
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (h + (x : ℂ)))
    =ᶠ[atTop]
  fun x : ℝ =>
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x : ℂ)

/-- **All-prime value faithfulness.**  The von Mangoldt source has no nonzero complex
translation period, even when equality is required only cofinally on the real Euler ray. -/
theorem vonMangoldtTranslationValueConstraint_iff (h : ℂ) :
    VonMangoldtTranslationValueConstraint h ↔ h = 0 := by
  constructor
  · intro hv
    let P : AddMonoidAlgebra ℂ ℂ := AddMonoidAlgebra.single h 1 - 1
    have hseries :
        (fun x : ℝ => LSeries (shiftedVonMangoldtCoeff h) (x : ℂ)) =ᶠ[atTop]
          fun x : ℝ => LSeries (shiftedVonMangoldtCoeff 0) (x : ℂ) := by
      filter_upwards [hv] with x hx
      rw [LSeries_shiftedVonMangoldtCoeff, LSeries_shiftedVonMangoldtCoeff]
      simpa using hx
    have hP : P = 0 := by
      apply GaloisForLFunctions.RHTower.euler_translation_faithful
      intro p hp m hm
      have hc := LSeries.eq_of_LSeries_eventually_eq
        (shiftedVonMangoldtCoeff_abscissa_lt_top h)
        (shiftedVonMangoldtCoeff_abscissa_lt_top 0) hseries
        (pow_ne_zero m hp.ne_zero)
      rw [shiftedVonMangoldtCoeff_prime_pow_exp h hp (by omega),
        shiftedVonMangoldtCoeff_prime_pow_exp 0 hp (by omega)] at hc
      have hlog : (Real.log p : ℂ) ≠ 0 := by
        exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      have hexp : Complex.exp (-(((m : ℝ) * Real.log p : ℝ) : ℂ) * h) = 1 := by
        apply mul_left_cancel₀ hlog
        simpa using hc
      rw [show GaloisForLFunctions.RHTower.translationChar
          ((m : ℝ) * Real.log p) P =
          GaloisForLFunctions.RHTower.translationChar ((m : ℝ) * Real.log p)
              (AddMonoidAlgebra.single h 1) - 1 by
            simp [P, map_sub]]
      rw [GaloisForLFunctions.RHTower.translationChar_single, hexp, sub_self]
    by_contra hh
    change (AddMonoidAlgebra.single h 1 - 1 : AddMonoidAlgebra ℂ ℂ) = 0 at hP
    have hsingle : (AddMonoidAlgebra.single h 1 : AddMonoidAlgebra ℂ ℂ) = 1 :=
      sub_eq_zero.mp hP
    have heval := congrArg (fun Q : AddMonoidAlgebra ℂ ℂ => Q.coeff h) hsingle
    rw [AddMonoidAlgebra.one_def] at heval
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      if_neg (Ne.symm hh)] at heval
    exact one_ne_zero heval
  · rintro rfl
    filter_upwards with x
    simp

/-- The same static constraint stated for the actual continued prime flux. -/
def InfinitePrimeFluxTranslationValueConstraint (h : ℂ) : Prop :=
  (fun x : ℝ => infinitePrimeFlux (h + (x : ℂ))) =ᶠ[atTop]
    fun x : ℝ => infinitePrimeFlux (x : ℂ)

/-- The actual prime flux has no nonzero cofinal translation period. -/
theorem infinitePrimeFluxTranslationValueConstraint_iff (h : ℂ) :
    InfinitePrimeFluxTranslationValueConstraint h ↔ h = 0 := by
  constructor
  · intro hflux
    apply (vonMangoldtTranslationValueConstraint_iff h).mp
    filter_upwards [hflux, eventually_gt_atTop (1 - h.re),
      eventually_gt_atTop 1] with x hx hxshift hxone
    have hh : 1 < (h + (x : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    have hx' : 1 < ((x : ℝ) : ℂ).re := by simpa using hxone
    rw [← infinitePrimeFlux_eq_vonMangoldtLSeries hh,
      ← infinitePrimeFlux_eq_vonMangoldtLSeries hx']
    exact hx
  · rintro rfl
    filter_upwards with x
    simp

/-- The spectral displacement used by the moving completed trace is a translation by `z I` in
the Euler `s`-coordinate. -/
def MovingVonMangoldtValueConstraint (z : ℂ) : Prop :=
  VonMangoldtTranslationValueConstraint (z * I)

/-- The moving prime channel vanishes cofinally only at the zero spectral displacement. -/
theorem movingVonMangoldtValueConstraint_iff (z : ℂ) :
    MovingVonMangoldtValueConstraint z ↔ z = 0 := by
  rw [MovingVonMangoldtValueConstraint,
    vonMangoldtTranslationValueConstraint_iff]
  constructor
  · intro hz
    exact (mul_eq_zero.mp hz).resolve_right I_ne_zero
  · rintro rfl
    simp

end

end RHTower
