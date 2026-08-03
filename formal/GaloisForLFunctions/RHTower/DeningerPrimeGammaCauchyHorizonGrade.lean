import GaloisForLFunctions.RHTower.DeningerArithmeticPrimeGammaHilbert
import GaloisForLFunctions.RHTower.DeningerPrimeGammaEulerSectorObstruction
import GaloisForLFunctions.RHTower.DeningerMeyerXiGaussianResidueNonadmission

/-!
# A source-derived horizon grade for the Gaussian--Gamma residue packet

The forced Gaussian--Gamma residue packet is not admitted by the unweighted divisor `ℓ²`
completion.  Its analytic inverse removes the local residue but leaves the constant global packet.

This file supplies the independent global grade from the already constructed prime--Gamma source.
Every lower absolute-Euler Cauchy atom restricts to a square-summable function on the
multiplicity-exact Xi divisor.  Its pole lies in a zero-free source sector, so none of its divisor
coordinates vanishes.  Multiplying the forced residue normalizer by this grade therefore gives a
square-summable admitted packet without erasing any finite divisor coordinate.
-/

open Complex

namespace RHTower
namespace DeningerMeyerGaussianGreen

noncomputable section

/-- The divisor horizon grade supplied by one literal lower prime--Gamma Cauchy source atom. -/
def primeGammaCauchyHorizonGrade
    (z : DeningerPrimeGammaLowerPoint) (q : XiZeroCopy) : ℂ :=
  deningerPrimeGammaLowerCauchyTest (Finsupp.single z 1) (xiSpectralPoint q)

/-- Every source Cauchy grade is square-summable on the multiplicity-exact Xi divisor. -/
theorem summable_norm_sq_primeGammaCauchyHorizonGrade
    (z : DeningerPrimeGammaLowerPoint) :
    Summable (fun q : XiZeroCopy => ‖primeGammaCauchyHorizonGrade z q‖ ^ 2) := by
  have h := deningerPrimeGammaLowerCauchyTest_squareSummable
    (Finsupp.single z 1)
  exact h

/-- Every admissible source grade necessarily decays at the infinite divisor horizon. -/
theorem tendsto_norm_primeGammaCauchyHorizonGrade_cofinite_zero
    (z : DeningerPrimeGammaLowerPoint) :
    Filter.Tendsto (fun q : XiZeroCopy => ‖primeGammaCauchyHorizonGrade z q‖)
      Filter.cofinite (nhds 0) := by
  have hsq :=
    (summable_norm_sq_primeGammaCauchyHorizonGrade z).tendsto_cofinite_zero
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg, norm_nonneg, Real.sqrt_zero] using hsqrt

/-- The source grade loses no divisor coordinate: its Cauchy pole is in the zero-free Euler
sector, while every spectral coordinate lies on the Xi divisor. -/
theorem primeGammaCauchyHorizonGrade_ne_zero
    (z : DeningerPrimeGammaLowerPoint) (q : XiZeroCopy) :
    primeGammaCauchyHorizonGrade z q ≠ 0 := by
  rw [primeGammaCauchyHorizonGrade,
    deningerPrimeGammaLowerCauchyTest_single, one_mul, xiWeilCauchyTest]
  apply inv_ne_zero
  apply sub_ne_zero.mpr
  intro h
  exact (XiC_ne_zero_of_one_lt_centered_re z.property)
    (h ▸ XiC_xiSpectralPoint_eq_zero q)

/-- The source-derived diagonal weight: local analytic normalization times global Cauchy grade. -/
def primeGammaCauchyResidueWeight
    (z : DeningerPrimeGammaLowerPoint) (q : XiZeroCopy) : ℂ :=
  primeGammaCauchyHorizonGrade z q * xiGaussianGammaResidueNormalizer q

/-- After the forced local normalizer, the admitted residue coefficient is exactly the source
Cauchy grade. -/
theorem primeGammaCauchyResidueWeight_mul_packet
    (z : DeningerPrimeGammaLowerPoint) (q : XiZeroCopy) :
    primeGammaCauchyResidueWeight z q * xiGaussianGammaResiduePacket q =
      primeGammaCauchyHorizonGrade z q := by
  rw [primeGammaCauchyResidueWeight]
  exact horizonGrade_mul_normalizer_mul_packet
    (primeGammaCauchyHorizonGrade z) q

/-- The source-derived weighted singular residue packet is admitted by the divisor `ℓ²` carrier. -/
theorem summable_norm_sq_primeGammaCauchyResiduePacket
    (z : DeningerPrimeGammaLowerPoint) :
    Summable (fun q : XiZeroCopy =>
      ‖primeGammaCauchyResidueWeight z q *
        xiGaussianGammaResiduePacket q‖ ^ 2) := by
  exact (summable_weighted_packet_iff_horizonGrade
    (primeGammaCauchyHorizonGrade z)).2
      (summable_norm_sq_primeGammaCauchyHorizonGrade z)

/-- Multiplication by the source-derived grade is coefficient-faithful on arbitrary divisor
packets, despite its necessary decay at the infinite horizon. -/
theorem primeGammaCauchyHorizonGrade_mul_injective
    (z : DeningerPrimeGammaLowerPoint) :
    Function.Injective
      (fun u : XiZeroCopy → ℂ =>
        fun q => primeGammaCauchyHorizonGrade z q * u q) := by
  intro u v huv
  funext q
  exact mul_left_cancel₀ (primeGammaCauchyHorizonGrade_ne_zero z q)
    (congrFun huv q)

/-- Admission and ordinary unweighted stable recovery are incompatible: the source grade is
pointwise faithful but admits no positive uniform lower modulus. -/
theorem not_exists_uniform_lower_bound_primeGammaCauchyHorizonGrade
    (z : DeningerPrimeGammaLowerPoint) :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ q : XiZeroCopy, c ≤ ‖primeGammaCauchyHorizonGrade z q‖ := by
  rintro ⟨c, hc, hlower⟩
  have hev :=
    (tendsto_norm_primeGammaCauchyHorizonGrade_cofinite_zero z).eventually_lt_const hc
  obtain ⟨q, hq⟩ := hev.exists
  exact (not_lt_of_ge (hlower q)) hq

end

end DeningerMeyerGaussianGreen
end RHTower
