import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteAdeleHaar

/-!
# The translation coefficient of finite-adelic Haar measure

The normalized overlap of the integral finite adeles with a translate is their indicator.
This realizes the critical Haar translation reading on the actual finite adele ring.
-/

open MeasureTheory IsDedekindDomain
open GaloisForLFunctions.RHTower
open scoped Classical
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The coefficient of the integral-subring indicator under additive translation. -/
def finiteAdelicHaarTranslation (b : CCMRationalFiniteAdele) : ℂ :=
  ∫ x in ccmRationalIntegralFiniteAdeles,
    (if x - b ∈ ccmRationalIntegralFiniteAdeles then (1 : ℂ) else 0)
    ∂ccmRationalFiniteAdeleHaar

private theorem integralFiniteAdeles_sub_mem_iff {x b : CCMRationalFiniteAdele}
    (hx : x ∈ ccmRationalIntegralFiniteAdeles) :
    x - b ∈ ccmRationalIntegralFiniteAdeles ↔ b ∈ ccmRationalIntegralFiniteAdeles := by
  constructor
  · intro h v
    have he : b v = x v - (x v - b v) := by ring
    rw [he]
    exact (v.adicCompletionIntegers ℚ).sub_mem (hx v) (h v)
  · intro hb v
    exact (v.adicCompletionIntegers ℚ).sub_mem (hx v) (hb v)

/-- The Haar translation coefficient is exactly the integral-adele indicator. -/
theorem finiteAdelicHaarTranslation_eq (b : CCMRationalFiniteAdele) :
    finiteAdelicHaarTranslation b =
      if b ∈ ccmRationalIntegralFiniteAdeles then 1 else 0 := by
  unfold finiteAdelicHaarTranslation
  calc
    _ = ∫ _ in ccmRationalIntegralFiniteAdeles,
        (if b ∈ ccmRationalIntegralFiniteAdeles then (1 : ℂ) else 0)
        ∂ccmRationalFiniteAdeleHaar := by
      apply setIntegral_congr_fun ccmRationalIntegralFiniteAdeles_isOpen.measurableSet
      intro x hx
      change (if x - b ∈ ccmRationalIntegralFiniteAdeles then (1 : ℂ) else 0) =
        if b ∈ ccmRationalIntegralFiniteAdeles then 1 else 0
      rw [integralFiniteAdeles_sub_mem_iff hx]
    _ = _ := by
      simp only [setIntegral_const, measureReal_def,
        ccmRationalFiniteAdeleHaar_integral_subring, ENNReal.toReal_one, one_smul]

#print axioms finiteAdelicHaarTranslation_eq
end GaloisForLFunctions.AdelicKreinGeometry
