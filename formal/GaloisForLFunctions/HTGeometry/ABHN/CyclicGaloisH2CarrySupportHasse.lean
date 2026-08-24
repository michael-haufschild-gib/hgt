import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2CarryReciprocityProfile
import GaloisForLFunctions.HTGeometry.ABHN.FinsuppReciprocitySupportCardinality

/-!
# Support rigidity for cyclic carry reciprocity profiles

The torsion invariant of literal cyclic `H²` carry classes is faithful. Hence a nonzero finite
carry profile with zero invariant sum cannot be concentrated at one place. In particular, a
carry parameter outside the field-norm image forces a distinct nonzero carry coordinate.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

/-- A nonzero reciprocal cyclic carry profile occupies at least two places. -/
theorem cyclicGaloisCarryH2Profile_two_le_support_card_of_sum_eq_zero
    (ι : Type u) [DecidableEq ι]
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (f : ι →₀ cyclicGaloisH2 K L)
    (hf : cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L n hn qEquiv f = 0)
    (hne : f ≠ 0) :
    2 ≤ f.support.card := by
  apply finsupp_two_le_support_card_of_injective_sum_eq_zero
    (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv).toAddMonoidHom
    (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv).injective f
  · exact hf
  · exact hne

/-- A nonzero reciprocal cyclic carry profile has two distinct nonzero local classes. -/
theorem cyclicGaloisCarryH2Profile_exists_two_nonzero_places_of_sum_eq_zero
    (ι : Type u) [DecidableEq ι]
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (f : ι →₀ cyclicGaloisH2 K L)
    (hf : cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L n hn qEquiv f = 0)
    (hne : f ≠ 0) :
    ∃ i j, i ≠ j ∧ f i ≠ 0 ∧ f j ≠ 0 := by
  apply finsupp_exists_two_nonzero_places_of_injective_sum_eq_zero
    (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv).toAddMonoidHom
    (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv).injective f
  · exact hf
  · exact hne

/-- Product-one reciprocity forces every nonzero cyclic carry packet to use two places. -/
theorem cyclicGaloisCarryH2Profile_exists_two_nonzero_places_of_product_eq_one
    (ι : Type u) [DecidableEq ι]
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (f : ι →₀ cyclicGaloisH2 K L)
    (hf : f.prod
      (fun _ z => cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv z) = 1)
    (hne : f ≠ 0) :
    ∃ i j, i ≠ j ∧ f i ≠ 0 ∧ f j ≠ 0 := by
  apply cyclicGaloisCarryH2Profile_exists_two_nonzero_places_of_sum_eq_zero
    ι K L n hn qEquiv f
  · exact (cyclicGaloisCarryH2Profile_product_eq_one_iff_sum_eq_zero
      ι K L n hn qEquiv f).mp hf
  · exact hne

/-- A nonnorm carry parameter in a reciprocal profile has a distinct nonzero local partner. -/
theorem cyclicGaloisCarryH2Profile_nonnorm_coordinate_has_nonzero_partner
    (ι : Type u) [DecidableEq ι]
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (f : ι →₀ cyclicGaloisH2 K L) (i : ι) (a : Additive Kˣ)
    (hi : f i = cyclicGaloisCarryH2Class K L a)
    (ha : a ∉ cyclicGaloisH2BaseNormImage K L)
    (hf : cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L n hn qEquiv f = 0) :
    ∃ j, j ≠ i ∧ f j ≠ 0 := by
  have hfi : f i ≠ 0 := by
    rw [hi]
    intro hzero
    exact ha ((cyclicGaloisCarryH2Class_eq_zero_iff_mem_normImage K L a).mp hzero)
  apply finsupp_exists_other_nonzero_place_of_injective_sum_eq_zero
    (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv).toAddMonoidHom
    (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv).injective f
  · exact hf
  · exact hfi

end

end GaloisForLFunctions.HTGeometry.ABHN
