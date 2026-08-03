import GaloisForLFunctions.RHTower.CCMRationalClassSpaceSection
import GaloisForLFunctions.RHTower.CCMRationalFiniteAdeleDenominator

/-!
# Uniform rational denominators under profinite-unit translation

Compact support supplies one denominator for the entire support of a finite Bruhat function.
Right multiplication by a profinite unit does not enlarge this denominator: both the unit and
its inverse are integral at every finite place.  Hence one integer confines every rational
diagonal orbit simultaneously over the full `𝔽̂ˣ` class-space coordinate.
-/

noncomputable section

open scoped RestrictedProduct algebraMap

namespace GaloisForLFunctions
namespace RHTower

open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

/-- **Uniform profinite denominator law.**  One nonzero integer confines the rational support
after right translation by every profinite unit. -/
theorem ccmRationalFiniteBruhat_exists_uniformProfiniteIntegerDenominator
    (φ : CCMRationalFiniteBruhatSchwartz) :
    ∃ d : ℤ, d ≠ 0 ∧
      ∀ (b : CCMRationalProfiniteUnit) (q : ℚ),
        φ.1 (algebraMap ℚ CCMRationalFiniteAdele q * b.1) ≠ 0 →
          algebraMap ℤ ℚ d * q ∈ (algebraMap ℤ ℚ).range := by
  obtain ⟨d, hd, hsupport⟩ :=
    ccmRationalFiniteAdele_isCompact_exists_commonIntegerDenominator φ.2
  refine ⟨d, hd, fun b q hφ => ?_⟩
  have hxSupport :
      algebraMap ℚ CCMRationalFiniteAdele q * b.1 ∈
        tsupport (φ.1 : CCMRationalFiniteAdele → ℂ) :=
    subset_tsupport (f := (φ.1 : CCMRationalFiniteAdele → ℂ)) hφ
  have hxDen := hsupport hxSupport
  have hqDen : ∀ v : HeightOneSpectrum ℤ,
      (algebraMap ℤ CCMRationalFiniteAdele d *
          algebraMap ℚ CCMRationalFiniteAdele q) v ∈
        v.adicCompletionIntegers ℚ := by
    intro v
    have hmul := mul_mem (hxDen v) (b.2.2 v)
    convert hmul using 1
    simp [mul_assoc]
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ
  intro v
  have hv := hqDen v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv
  change Valued.v
      (algebraMap ℤ (v.adicCompletion ℚ) d *
        algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1 at hv
  rw [IsScalarTower.algebraMap_apply ℤ ℚ (v.adicCompletion ℚ),
    ← map_mul,
    HeightOneSpectrum.algebraMap_adicCompletion ℤ ℚ v,
    Function.comp_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
  exact hv

end RHTower
end GaloisForLFunctions
