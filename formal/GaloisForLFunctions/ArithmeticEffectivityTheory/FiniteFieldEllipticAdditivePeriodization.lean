import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticAdditiveSplitting
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Additive periodization on the actual elliptic adeles

The simple-pole domain meets every diagonal translate exactly once.
Its ambient Haar normalization therefore gives exact additive unfolding,
including the nonnegative Tonelli formula without an integrability premise.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- The diagonal subgroup retains the actual function-field coordinates. -/
def diagonalAdelesEquiv : K ≃+ diagonalAdeles where
  toFun z := ⟨adeleEmbedding z, ⟨z, rfl⟩⟩
  invFun z := adeleRationalProjection z
  left_inv := adeleRationalProjection_diagonal
  right_inv z := by
    obtain ⟨w, hw⟩ := z.property
    apply Subtype.ext
    change adeleEmbedding (adeleRationalProjection (z : Adeles)) = (z : Adeles)
    rw [← hw, adeleRationalProjection_diagonal]
  map_add' z w := Subtype.ext (map_add adeleEmbedding z w)

instance diagonalAdeles_countable : Countable diagonalAdeles :=
  diagonalAdelesEquiv.symm.injective.countable

local instance : MeasurableAdd Adeles := ContinuousAdd.measurableAdd

/-- The actual simple-pole domain is a fundamental domain for diagonal translations. -/
theorem ellipticAdditiveDomain_isAddFundamentalDomain :
    IsAddFundamentalDomain diagonalAdeles (ellipticAdditiveDomain : Set Adeles) adeleHaar := by
  apply IsAddFundamentalDomain.mk' ellipticAdditiveDomain_isOpen.measurableSet.nullMeasurableSet
  intro a
  obtain ⟨z, hz, hu⟩ := adele_existsUnique_gap_representative a
  refine ⟨⟨adeleEmbedding (-z), ⟨-z, rfl⟩⟩, ?_, ?_⟩
  · change adeleEmbedding (-z) + a ∈ ellipticAdditiveDomain
    simpa only [map_neg, sub_eq_add_neg, add_comm] using hz
  · intro g hg
    obtain ⟨w, hw⟩ := g.property
    have hwD : a - adeleEmbedding (-w) ∈ ellipticAdditiveDomain := by
      change (g : Adeles) + a ∈ ellipticAdditiveDomain at hg
      rw [← hw] at hg
      simpa only [map_neg, sub_neg_eq_add, add_comm] using hg
    have hwz : w = -z := neg_eq_iff_eq_neg.mp (hu (-w) hwD)
    apply Subtype.ext
    exact hw.symm.trans (congrArg adeleEmbedding hwz)

private theorem lintegral_domainHaar (f : Adeles → ℝ≥0∞) :
    (∫⁻ d : ellipticAdditiveDomain, f (d : Adeles) ∂ellipticDomainHaar) =
      ∫⁻ a in (ellipticAdditiveDomain : Set Adeles), f a ∂adeleHaar := by
  have hm := ellipticAdditiveDomain_isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
  have h := hm.lintegral_map (μ := ellipticDomainHaar) f
  have hr : Set.range (Subtype.val : ellipticAdditiveDomain → Adeles) =
      (ellipticAdditiveDomain : Set Adeles) := by
    ext a
    constructor
    · rintro ⟨d, rfl⟩
      exact d.property
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  change (∫⁻ a, f a ∂Measure.map (Subtype.val : ellipticAdditiveDomain → Adeles)
    (Measure.comap (Subtype.val : ellipticAdditiveDomain → Adeles) adeleHaar)) = _ at h
  rw [hm.map_comap, hr] at h
  exact h.symm

/-- Exact Haar decomposition as the sum of all rational translates of the compact domain. -/
theorem lintegral_adeleHaar_eq_tsum_domain (f : Adeles → ℝ≥0∞) :
    (∫⁻ a, f a ∂adeleHaar) =
      ∑' z : K, ∫⁻ d : ellipticAdditiveDomain,
        f (adeleEmbedding z + (d : Adeles)) ∂ellipticDomainHaar := by
  calc
    _ = ∑' g : diagonalAdeles, ∫⁻ a in (ellipticAdditiveDomain : Set Adeles),
        f ((g : Adeles) + a) ∂adeleHaar :=
      ellipticAdditiveDomain_isAddFundamentalDomain.lintegral_eq_tsum'' f
    _ = ∑' z : K, ∫⁻ a in (ellipticAdditiveDomain : Set Adeles),
        f (adeleEmbedding z + a) ∂adeleHaar :=
      (diagonalAdelesEquiv.toEquiv.tsum_eq
        (fun g : diagonalAdeles => ∫⁻ a in (ellipticAdditiveDomain : Set Adeles),
          f ((g : Adeles) + a) ∂adeleHaar)).symm
    _ = _ := tsum_congr fun z => (lintegral_domainHaar (fun a => f (adeleEmbedding z + a))).symm

/-- Tonelli periodization over the actual function field and the normalized gap domain. -/
theorem lintegral_adeleHaar_periodization (f : Adeles → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ a, f a ∂adeleHaar) =
      ∫⁻ d : ellipticAdditiveDomain, ∑' z : K,
        f (adeleEmbedding z + (d : Adeles)) ∂ellipticDomainHaar := by
  rw [lintegral_adeleHaar_eq_tsum_domain]
  exact (lintegral_tsum fun z =>
    (hf.comp (continuous_const.add continuous_subtype_val).measurable).aemeasurable).symm

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticAdditiveDomain_isAddFundamentalDomain
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.lintegral_adeleHaar_eq_tsum_domain
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.lintegral_adeleHaar_periodization
