import GaloisForLFunctions.RHTower.XiHurwitzRationalFiberSeam
import GaloisForLFunctions.RHTower.XiHurwitzAnchorPrimeTwoOrientationEnergy
import GaloisForLFunctions.RHTower.PrimeTailCoPoissonBoundary

/-!
# The first prime co-Poisson seed and the Hurwitz reflection receiver

The literal seed at prime `2` is enough to express the remaining HJ source
producer without a modal or asymptotic surrogate.  Its raw Mellin pairing has
a nonzero diagonal value on the critical line, so the correct source test is
the pairing multiplied by the reflected-exponent separation.  Away from the
critical line, vanishing of that residual is exactly equality of the
convergent two-point Hurwitz fibres.  This file proves the reduction only; it
does not assert the residual-vanishing premise.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- Literal first-prime Mellin source test at the two HJ reflected exponents. -/
def primeTailSeedTwoReflectionMellin (rho : ℂ) : ℂ :=
  ∫ x : ℝ in Ioc 0 1,
    primeTailSeed 2 ((starRingEnd ℂ) rho + 1) x *
      (x : ℂ) ^ ((2 - rho) - 1)

/-- The diagonal-safe first-prime source residual.  Its prefactor is exactly
the separation of the two reflected exponents. -/
def primeTailSeedTwoReflectionResidual (rho : ℂ) : ℂ :=
  ((starRingEnd ℂ) rho + 1 - (2 - rho)) * primeTailSeedTwoReflectionMellin rho

/-- At an off-critical open-strip point, vanishing of the literal first-prime
co-Poisson residual forces equality of the finite reflected Hurwitz fibres. -/
theorem rationalHurwitzFiberTwoReflectionFixed_of_primeTailSeedTwoReflectionResidual_eq_zero
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hoff : rho.re ≠ 1 / 2)
    (hsource : primeTailSeedTwoReflectionResidual rho = 0) :
    rationalHurwitzFiberResponse 2 ((starRingEnd ℂ) rho) =
      rationalHurwitzFiberResponse 2 (1 - rho) := by
  have hzw : (starRingEnd ℂ) rho + 1 ≠ 2 - rho := by
    intro h
    apply hoff
    have hre := congrArg Complex.re h
    simp only [Complex.conj_re, Complex.add_re, Complex.one_re, Complex.sub_re] at hre
    norm_num at hre
    linarith
  have hsourceRaw : primeTailSeedTwoReflectionMellin rho = 0 := by
    unfold primeTailSeedTwoReflectionResidual at hsource
    exact (mul_eq_zero.mp hsource).resolve_left (sub_ne_zero.mpr hzw)
  have hform := integral_primeTailTerm (n := 2) (by norm_num : 2 ≤ 2) hzw
  change (∫ x : ℝ in Ioc 0 1,
    primeTailSeed 2 ((starRingEnd ℂ) rho + 1) x *
      (x : ℂ) ^ ((2 - rho) - 1)) = 0 at hsourceRaw
  rw [hsourceRaw] at hform
  have hdiv :
      ((2 : ℂ) ^ (-(2 - rho)) - (2 : ℂ) ^ (-((starRingEnd ℂ) rho + 1))) /
        (((starRingEnd ℂ) rho + 1) - (2 - rho)) = 0 := hform.symm
  have hden : ((starRingEnd ℂ) rho + 1) - (2 - rho) ≠ 0 := sub_ne_zero.mpr hzw
  have hnum : (2 : ℂ) ^ (-(2 - rho)) = (2 : ℂ) ^ (-((starRingEnd ℂ) rho + 1)) := by
    rcases (div_eq_zero_iff.mp hdiv) with h | h
    · exact sub_eq_zero.mp h
    · exact False.elim (hden h)
  have hpow : (2 : ℂ) ^ (2 - rho) = (2 : ℂ) ^ ((starRingEnd ℂ) rho + 1) := by
    have hinv := congrArg Inv.inv hnum
    rw [Complex.cpow_neg, Complex.cpow_neg, inv_inv] at hinv
    simpa only [inv_inv] using hinv
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hscaled :
      (2 : ℂ) * (2 : ℂ) ^ (1 - rho) = (2 : ℂ) * (2 : ℂ) ^ ((starRingEnd ℂ) rho) := by
    calc
      (2 : ℂ) * (2 : ℂ) ^ (1 - rho) = (2 : ℂ) ^ (2 - rho) := by
        calc
          (2 : ℂ) * (2 : ℂ) ^ (1 - rho) =
              (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (1 - rho) := by
                rw [Complex.cpow_one]
          _ = (2 : ℂ) ^ ((1 : ℂ) + (1 - rho)) :=
            (Complex.cpow_add (1 : ℂ) (1 - rho) htwo).symm
          _ = (2 : ℂ) ^ (2 - rho) := by
            congr 1
            ring
      _ = (2 : ℂ) ^ ((starRingEnd ℂ) rho + 1) := hpow
      _ = (2 : ℂ) ^ ((starRingEnd ℂ) rho) * (2 : ℂ) := by
        calc
          (2 : ℂ) ^ ((starRingEnd ℂ) rho + 1) =
              (2 : ℂ) ^ ((starRingEnd ℂ) rho + (1 : ℂ)) := by rfl
          _ = (2 : ℂ) ^ ((starRingEnd ℂ) rho) * (2 : ℂ) ^ (1 : ℂ) :=
            Complex.cpow_add _ _ htwo
          _ = (2 : ℂ) ^ ((starRingEnd ℂ) rho) * (2 : ℂ) := by
            rw [Complex.cpow_one]
      _ = (2 : ℂ) * (2 : ℂ) ^ ((starRingEnd ℂ) rho) := by ring
  have hcpow : (2 : ℂ) ^ ((starRingEnd ℂ) rho) = (2 : ℂ) ^ (1 - rho) := by
    apply mul_left_cancel₀ htwo
    simpa using hscaled.symm
  have hconj : 0 < ((starRingEnd ℂ) rho).re := by simpa using hstrip.1
  have href : 0 < (1 - rho).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [hstrip.2]
  rw [rationalHurwitzFiberResponse_eq_cpow (by norm_num : 0 < 2) hconj,
    rationalHurwitzFiberResponse_eq_cpow (by norm_num : 0 < 2) href]
  exact hcpow

/-- The diagonal-safe literal co-Poisson residual has exactly the same
open-strip zero locus as the existing common first-prime seam.  Thus its
vanishing is not a second, differently phrased HJ producer obligation: it is
the prime-orientation charge already shared with the Hurwitz and HC routes. -/
theorem primeTailSeedTwoReflectionResidual_eq_zero_iff_firstPrimeSeamCharge_eq_zero
    (rho : ℂ) (hstrip : 0 < rho.re ∧ rho.re < 1) :
    primeTailSeedTwoReflectionResidual rho = 0 ↔
      orbitwiseFirstPrimeSeamCharge rho = 0 := by
  constructor
  · intro hres
    by_cases hre : rho.re = 1 / 2
    · exact (orbitwiseFirstPrimeSeamCharge_eq_zero_iff rho).mpr hre
    · exact
        (rationalHurwitzFiberTwo_reflection_fixed_iff_firstPrimeSeamCharge_eq_zero hstrip).mp
          (rationalHurwitzFiberTwoReflectionFixed_of_primeTailSeedTwoReflectionResidual_eq_zero
            hstrip hre hres)
  · intro hseam
    have hre : rho.re = 1 / 2 :=
      (orbitwiseFirstPrimeSeamCharge_eq_zero_iff rho).mp hseam
    have hfixed : (starRingEnd ℂ) rho + 1 = 2 - rho := by
      apply Complex.ext
      · simp only [Complex.conj_re, Complex.add_re, Complex.one_re, Complex.sub_re]
        norm_num
        linarith
      · simp only [Complex.conj_im, Complex.add_im, Complex.one_im, Complex.sub_im]
        norm_num
    unfold primeTailSeedTwoReflectionResidual
    rw [sub_eq_zero.mpr hfixed, zero_mul]

/-- The exact HJ source-producer obligation: every Xi divisor must annihilate
the diagonal-safe literal first-prime co-Poisson residual. -/
def XiPrimeTailSeedTwoReflectionResidualVanishes : Prop :=
  ∀ rho : XiDivisorSupport, primeTailSeedTwoReflectionResidual (rho : ℂ) = 0

/-- The literal first-prime residual-vanishing law is sufficient for RH. -/
theorem riemannHypothesis_of_xiPrimeTailSeedTwoReflectionResidualVanishes
    (hsource : XiPrimeTailSeedTwoReflectionResidualVanishes) : RiemannHypothesis := by
  apply riemannHypothesis_of_xiRationalHurwitzFiberTwoReflectionFixed
  intro rho
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  by_cases hoff : (rho : ℂ).re = 1 / 2
  · exact (rationalHurwitzFiberResponse_reflection_fixed_iff (by norm_num) hstrip).mpr hoff
  · exact rationalHurwitzFiberTwoReflectionFixed_of_primeTailSeedTwoReflectionResidual_eq_zero
      hstrip hoff (hsource rho)

/-- The diagonal-safe literal first-prime source residual is an exact HJ
receiver: its vanishing over the Xi divisor is equivalent to RH. -/
theorem xiPrimeTailSeedTwoReflectionResidualVanishes_iff_riemannHypothesis :
    XiPrimeTailSeedTwoReflectionResidualVanishes ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_xiPrimeTailSeedTwoReflectionResidualVanishes
  · intro hRH rho
    have hre := xi_divisor_support_re_eq_half_of_rh hRH rho
    have hfixed : (starRingEnd ℂ) (rho : ℂ) = 1 - (rho : ℂ) := by
      apply Complex.ext
      · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
        linarith
      · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im, zero_sub]
    unfold primeTailSeedTwoReflectionResidual
    rw [hfixed]
    ring

/-- The literal first-prime co-Poisson residual is the source realization of
the established Xi--Hurwitz orientation energy zero locus. -/
theorem xiPrimeTailSeedTwoReflectionResidualVanishes_iff_orientationEnergy_zero :
    XiPrimeTailSeedTwoReflectionResidualVanishes ↔ xiHurwitzOrientationEnergy = 0 := by
  rw [show XiPrimeTailSeedTwoReflectionResidualVanishes ↔ XiFirstPrimeSeamChargesVanish by
    constructor
    · intro h rho
      exact
        (primeTailSeedTwoReflectionResidual_eq_zero_iff_firstPrimeSeamCharge_eq_zero
          (rho : ℂ) (xi_divisor_support_re_mem_open_unit rho)).mp (h rho)
    · intro h rho
      exact
        (primeTailSeedTwoReflectionResidual_eq_zero_iff_firstPrimeSeamCharge_eq_zero
          (rho : ℂ) (xi_divisor_support_re_mem_open_unit rho)).mpr (h rho)]
  exact xiFirstPrimeSeamChargesVanish_iff_orientationEnergy_zero

end RHTower
