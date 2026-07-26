import GaloisForLFunctions.RHTower.DeningerLefschetzTrace
import GaloisForLFunctions.RHTower.CCMCompletedPrimeGammaAccretivityCriterion

/-!
# Deninger cohomological resolvent passivity universality

The multiplicity-exact centered Deninger divisor resolvent trace agrees with the continued
prime--archimedean source trace on every regular point of the centered upper half-strip.
Consequently its anti-Herglotz/passivity law is exactly the established arithmetic source gate,
and hence exactly the Riemann hypothesis.
-/

open Complex

namespace RHTower

noncomputable section

/--
The centered Deninger divisor resolvent is anti-Herglotz on every regular point of the upper
half-strip.
-/
def DeningerDivisorUpperAntiHerglotz : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      (deningerDivisorRelativeResolventTrace z).im ≤ 0

private theorem xiExplicitAdmissible_of_mem_centeredUpperHalfStrip
    {z : ℂ} (hzpos : 0 < z.im) (hzhalf : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    XiExplicitAdmissible z := by
  refine ⟨?_, ?_, hzeta⟩
  · simp only [add_re, mul_re, I_re, mul_zero, I_im, mul_one]
    norm_num
    linarith
  · intro h
    have hre := congrArg Complex.re h
    simp only [add_re, mul_re, I_re, mul_zero, I_im, mul_one, one_re] at hre
    norm_num at hre
    linarith

/--
Deninger cohomological resolvent passivity and continued prime--Gamma source passivity are the
same pointwise condition.
-/
theorem deningerDivisorUpperAntiHerglotz_iff_continuedPrimeArchUpperAntiHerglotz :
    DeningerDivisorUpperAntiHerglotz ↔ ContinuedPrimeArchUpperAntiHerglotz := by
  constructor
  · intro hD z hzpos hzhalf hzeta
    have hadm :=
      xiExplicitAdmissible_of_mem_centeredUpperHalfStrip hzpos hzhalf hzeta
    rw [← deningerResolventLefschetzTrace hadm]
    exact hD z hzpos hzhalf hzeta
  · intro hsource z hzpos hzhalf hzeta
    have hadm :=
      xiExplicitAdmissible_of_mem_centeredUpperHalfStrip hzpos hzhalf hzeta
    rw [deningerResolventLefschetzTrace hadm]
    exact hsource z hzpos hzhalf hzeta

/-- Exact cohomological resolvent passivity criterion for RH. -/
theorem deningerDivisorUpperAntiHerglotz_iff_riemannHypothesis :
    DeningerDivisorUpperAntiHerglotz ↔ RiemannHypothesis := by
  rw [deningerDivisorUpperAntiHerglotz_iff_continuedPrimeArchUpperAntiHerglotz,
    continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis]

/--
**Deninger cohomological resolvent passivity universality.**

The Deninger divisor resolvent, continued prime--Gamma response, and RH define one and the same
passivity law.
-/
theorem deninger_cohomologicalResolventPassivityUniversality :
    (DeningerDivisorUpperAntiHerglotz ↔ ContinuedPrimeArchUpperAntiHerglotz) ∧
      (DeningerDivisorUpperAntiHerglotz ↔ RiemannHypothesis) :=
  ⟨deningerDivisorUpperAntiHerglotz_iff_continuedPrimeArchUpperAntiHerglotz,
    deningerDivisorUpperAntiHerglotz_iff_riemannHypothesis⟩

end

end RHTower
