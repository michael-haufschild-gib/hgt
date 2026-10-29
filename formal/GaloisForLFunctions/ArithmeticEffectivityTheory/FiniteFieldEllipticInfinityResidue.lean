import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticInfinityValuation
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticPoleReduction
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The degree-one infinity place

Leading-term cancellation represents every residue at infinity by a unique
constant. Thus the actual infinity residue field is `𝔽₃`, and `x/y` gives
degree rotations whose logarithmic norm is an integral multiple of `log 3`.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

noncomputable section

/-- Constants embed into the actual infinity valuation ring. -/
def infinityConstants : Constants →+* InfinityRing :=
  (algebraMap Constants K).codRestrict InfinityRing.toSubring
    (fun c => (mem_infinityRing_iff _).mpr (infinityRegular.algebraMap_mem c))

@[simp] lemma infinityConstants_coe (c : Constants) :
    (infinityConstants c : K) = algebraMap Constants K c := rfl

/-- The residue field at the actual infinity valuation. -/
abbrev InfinityResidueField := IsLocalRing.ResidueField InfinityRing

/-- Reduction of constants into the infinity residue field. -/
def infinityResidueEmbedding : Constants →+* InfinityResidueField :=
  (IsLocalRing.residue InfinityRing).comp infinityConstants

lemma infinity_regular_sub_constant (z : InfinityRing) :
    ∃ c : Constants, infinityValuation ((z : K) - algebraMap Constants K c) < 1 := by
  obtain ⟨a, b, hb, hz, hab⟩ := (mem_infinityRing_iff (z : K)).mp z.2
  obtain ⟨c, hc⟩ := exists_scalar_poleDegree_sub_lt a b hb hab
  refine ⟨c, ?_⟩
  have hdiff : (z : K) - algebraMap Constants K c =
      algebraMap A K (a - algebraMap Constants A c * b) / algebraMap A K b := by
    rw [hz, map_sub, map_mul, ← IsScalarTower.algebraMap_apply, sub_div]
    rw [mul_div_cancel_right₀ _ (map_ne_zero hb)]
  rw [hdiff, infinityValuation_div_lt_one_iff _ b hb]
  exact hc

/-- Every residue at infinity comes from the original finite constant field. -/
theorem infinityResidueEmbedding_surjective : Function.Surjective infinityResidueEmbedding := by
  intro a
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective (R := InfinityRing) a
  obtain ⟨c, hc⟩ := infinity_regular_sub_constant z
  refine ⟨c, ?_⟩
  change IsLocalRing.residue InfinityRing (infinityConstants c) =
    IsLocalRing.residue InfinityRing z
  apply Eq.symm
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact (Valuation.mem_maximalIdeal_iff (v := infinityValuation)).mpr hc

/-- The actual infinity place has residue degree one. -/
def infinityResidueEquiv : Constants ≃+* InfinityResidueField :=
  RingEquiv.ofBijective infinityResidueEmbedding
    ⟨infinityResidueEmbedding.injective, infinityResidueEmbedding_surjective⟩

instance infinityResidue_finite : Finite InfinityResidueField :=
  Finite.of_surjective infinityResidueEmbedding infinityResidueEmbedding_surjective

theorem infinityResidue_card : Nat.card InfinityResidueField = 3 := by
  rw [← Nat.card_congr infinityResidueEquiv.toEquiv]
  simpa only [Nat.card_eq_fintype_card] using ZMod.card 3

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

