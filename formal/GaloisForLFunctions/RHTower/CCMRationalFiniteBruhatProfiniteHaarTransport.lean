import GaloisForLFunctions.RHTower.CCMRationalClassSpaceSection
import GaloisForLFunctions.RHTower.CCMRationalFiniteAdeleHaarCharacter
import GaloisForLFunctions.RHTower.CCMRationalAdelicBruhatSimpleTensorTraceClass

/-!
# Profinite-unit Haar transport and full-support denominator control

Multiplication by a profinite unit preserves the normalized finite-adelic Haar
measure exactly.  Separately, compact support supplies a positive natural
denominator for every point of the full translated support, not only its
rational diagonal samples.  These facts are the measure-theoretic input for
turning `ε₁` into finite cyclic quadrature.
-/

noncomputable section

open MeasureTheory IsDedekindDomain
open scoped RestrictedProduct algebraMap Classical

namespace GaloisForLFunctions
namespace RHTower

/-- Right multiplication by a profinite unit as additive homeomorphism. -/
def ccmRationalFiniteAdeleProfiniteMulRightEquiv
    (b : CCMRationalProfiniteUnit) :
    CCMRationalFiniteAdele ≃ₜ+ CCMRationalFiniteAdele :=
  ContinuousAddEquiv.mulRight b.1

/-- Profinite-unit multiplication preserves integral finite adeles. -/
theorem ccmRationalFiniteAdeleProfiniteMulRightEquiv_preimage_integral
    (b : CCMRationalProfiniteUnit) :
    ccmRationalFiniteAdeleProfiniteMulRightEquiv b ⁻¹'
        ccmRationalIntegralFiniteAdeles =
      ccmRationalIntegralFiniteAdeles := by
  ext x
  constructor
  · intro hx
    change ∀ v, (x * (b.1 : CCMRationalFiniteAdele)) v ∈
      CCMRationalLocalIntegers v at hx
    intro v
    have hmul := mul_mem (hx v) (b.2.2 v)
    have hcancel :
        (b.1 : CCMRationalFiniteAdele) *
          ((b.1⁻¹ : CCMRationalFiniteAdeleˣ) : CCMRationalFiniteAdele) = 1 := by
      change ↑(b.1 * b.1⁻¹) = (1 : CCMRationalFiniteAdele)
      simp
    change ((x * (b.1 : CCMRationalFiniteAdele)) *
      ((b.1⁻¹ : CCMRationalFiniteAdeleˣ) : CCMRationalFiniteAdele)) v ∈
        CCMRationalLocalIntegers v at hmul
    rw [mul_assoc, hcancel, mul_one] at hmul
    exact hmul
  · intro hx v
    exact mul_mem (hx v) (b.2.1 v)

/-- Haar character of profinite-unit multiplication is exactly one. -/
theorem ccmRationalFiniteAdeleProfiniteMulRightHaarCharacter
    (b : CCMRationalProfiniteUnit) :
    addEquivAddHaarChar
      (ccmRationalFiniteAdeleProfiniteMulRightEquiv b) = 1 := by
  have h := addEquivAddHaarChar_smul_preimage
    ccmRationalFiniteAdeleHaar
    (X := ccmRationalIntegralFiniteAdeles)
    (ccmRationalFiniteAdeleProfiniteMulRightEquiv b)
  rw [ccmRationalFiniteAdeleProfiniteMulRightEquiv_preimage_integral b,
    ccmRationalFiniteAdeleHaar_integral_subring] at h
  apply ENNReal.coe_injective
  simpa [ENNReal.smul_def] using h

/-- The normalized finite Bruhat integral is invariant under right
multiplication by a profinite unit. -/
theorem ccmRationalFiniteBruhatIntegral_mulRight_profinite
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalProfiniteUnit) :
    ccmRationalFiniteBruhatIntegral
        (ccmRationalFiniteBruhatMulRight phi b.1) =
      ccmRationalFiniteBruhatIntegral phi := by
  rw [ccmRationalFiniteBruhatIntegral_apply,
    ccmRationalFiniteBruhatIntegral_apply]
  change (∫ x, phi.1
      (ccmRationalFiniteAdeleProfiniteMulRightEquiv b x)
      ∂ccmRationalFiniteAdeleHaar) = _
  have hmap :
      (∫ x, phi.1 (ccmRationalFiniteAdeleProfiniteMulRightEquiv b x)
          ∂ccmRationalFiniteAdeleHaar) =
        ∫ y, phi.1 y ∂(ccmRationalFiniteAdeleHaar.map
          (ccmRationalFiniteAdeleProfiniteMulRightEquiv b)) :=
    (integral_map_equiv
      (ccmRationalFiniteAdeleProfiniteMulRightEquiv b).toHomeomorph.toMeasurableEquiv
      phi.1).symm
  rw [hmap]
  have hmeasure := addEquivAddHaarChar_smul_map
    ccmRationalFiniteAdeleHaar
    (ccmRationalFiniteAdeleProfiniteMulRightEquiv b)
  rw [ccmRationalFiniteAdeleProfiniteMulRightHaarCharacter b] at hmeasure
  have hmeasure' :
      ccmRationalFiniteAdeleHaar.map
          (ccmRationalFiniteAdeleProfiniteMulRightEquiv b) =
        ccmRationalFiniteAdeleHaar := by
    simpa only [one_smul] using hmeasure
  rw [hmeasure']

/-- **Full-support denominator law.** After right translation by any finite
idele, one positive natural denominator carries every nonzero point of the
translated Bruhat function into integral finite adeles. -/
theorem ccmRationalFiniteBruhatMulRight_exists_positiveNatSupportDenominator
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ) :
    ∃ D : ℕ, 0 < D ∧ ∀ x : CCMRationalFiniteAdele,
      phi.1 (x * b) ≠ 0 →
        algebraMap ℕ CCMRationalFiniteAdele D * x ∈
          ccmRationalIntegralFiniteAdelesAddSubgroup := by
  let g := ccmRationalFiniteBruhatMulRight phi b
  obtain ⟨d, hd, hden⟩ :=
    ccmRationalFiniteAdele_isCompact_exists_commonIntegerDenominator g.2
  let D := d.natAbs
  have hD : 0 < D := Int.natAbs_pos.mpr hd
  refine ⟨D, hD, fun x hx => ?_⟩
  have hxg : g.1 x ≠ 0 := by simpa [g] using hx
  have hdx := hden
    (subset_tsupport (f := (g.1 : CCMRationalFiniteAdele → ℂ)) hxg)
  change algebraMap ℤ CCMRationalFiniteAdele d * x ∈
    ccmRationalIntegralFiniteAdelesAddSubgroup at hdx
  have hmap : algebraMap ℕ CCMRationalFiniteAdele D =
      algebraMap ℤ CCMRationalFiniteAdele (D : ℤ) := by simp
  have hdD : d = (D : ℤ) ∨ d = -(D : ℤ) := by
    simpa [D] using Int.natAbs_eq d
  rcases hdD with hdD | hdD
  · rw [hmap, ← hdD]
    exact hdx
  · have hnegdx :=
      ccmRationalIntegralFiniteAdelesAddSubgroup.neg_mem hdx
    rw [hmap]
    simpa [hdD] using hnegdx

/-- One positive natural denominator simultaneously controls full translated
support and every rational diagonal orbit. -/
theorem ccmRationalFiniteBruhatMulRight_exists_positiveNatFullDenominator
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ) :
    ∃ D : ℕ, 0 < D ∧
      (∀ x : CCMRationalFiniteAdele,
        phi.1 (x * b) ≠ 0 →
          algebraMap ℕ CCMRationalFiniteAdele D * x ∈
            ccmRationalIntegralFiniteAdelesAddSubgroup) ∧
      ∀ q : ℚ,
        phi.1 (algebraMap ℚ CCMRationalFiniteAdele q * b) ≠ 0 →
          algebraMap ℕ ℚ D * q ∈ (algebraMap ℤ ℚ).range := by
  obtain ⟨D, hD, hsupport⟩ :=
    ccmRationalFiniteBruhatMulRight_exists_positiveNatSupportDenominator phi b
  refine ⟨D, hD, hsupport, fun q hq => ?_⟩
  have hfinite := hsupport
    (algebraMap ℚ CCMRationalFiniteAdele q) hq
  have hmap : algebraMap ℕ CCMRationalFiniteAdele D =
      algebraMap ℚ CCMRationalFiniteAdele (D : ℚ) := by simp
  rw [hmap] at hfinite
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ
  intro v
  have hv := hfinite v
  change ((algebraMap ℚ CCMRationalFiniteAdele (D : ℚ) *
    algebraMap ℚ CCMRationalFiniteAdele q) v) ∈
      v.adicCompletionIntegers ℚ at hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv
  change Valued.v
      (algebraMap ℚ (v.adicCompletion ℚ) (D : ℚ) *
        algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1 at hv
  rw [← map_mul,
    HeightOneSpectrum.algebraMap_adicCompletion ℤ ℚ v,
    Function.comp_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
  exact hv

end RHTower
end GaloisForLFunctions
