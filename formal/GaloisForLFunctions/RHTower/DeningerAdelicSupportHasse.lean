import GaloisForLFunctions.HTGeometry.ABHN.FinsuppReciprocitySupportCardinality
import GaloisForLFunctions.RHTower.DeningerAdelicFiniteLogProfile
import GaloisForLFunctions.RHTower.DeningerTowerReciprocity

namespace RHTower

open NumberField
open GaloisForLFunctions.HTGeometry.ABHN

variable {K : Type*} [Field K] [NumberField K]

noncomputable local instance : DecidableEq (InfinitePlace K ⊕ FinitePlace K) := Classical.decEq _

def deningerInfinitePlaceEmbedding : InfinitePlace K ↪ (InfinitePlace K ⊕ FinitePlace K) :=
  ⟨Sum.inl, Sum.inl_injective⟩

def deningerFinitePlaceEmbedding : FinitePlace K ↪ (InfinitePlace K ⊕ FinitePlace K) :=
  ⟨Sum.inr, Sum.inr_injective⟩

noncomputable def deningerAllPlaceLogProfile (alpha : Kˣ) :
    (InfinitePlace K ⊕ FinitePlace K) →₀ ℝ :=
  Finsupp.embDomain deningerInfinitePlaceEmbedding
      ((Finsupp.equivFunOnFinite).symm
        (fun w : InfinitePlace K => (w.mult : ℝ) * Real.log (w (alpha : K)))) +
    Finsupp.embDomain deningerFinitePlaceEmbedding (deningerFinitePlaceLogProfile alpha)

@[simp] theorem deningerAllPlaceLogProfile_inl (alpha : Kˣ) (w : InfinitePlace K) :
    deningerAllPlaceLogProfile alpha (Sum.inl w) =
      (w.mult : ℝ) * Real.log (w (alpha : K)) := by
  classical
  simp [deningerAllPlaceLogProfile, Finsupp.embDomain_apply,
    deningerInfinitePlaceEmbedding, deningerFinitePlaceEmbedding]

@[simp] theorem deningerAllPlaceLogProfile_inr (alpha : Kˣ) (w : FinitePlace K) :
    deningerAllPlaceLogProfile alpha (Sum.inr w) = Real.log (w (alpha : K)) := by
  classical
  simp [deningerAllPlaceLogProfile, Finsupp.embDomain_apply,
    deningerInfinitePlaceEmbedding, deningerFinitePlaceEmbedding,
    deningerFinitePlaceLogProfile_apply]

theorem deningerAllPlaceLogProfile_sum_eq_zero (alpha : Kˣ) :
    (deningerAllPlaceLogProfile alpha).sum (fun _ x => x) = 0 := by
  rw [deningerAllPlaceLogProfile, Finsupp.sum_add_index' (by intros; rfl) (by intros; rfl),
    Finsupp.sum_embDomain, Finsupp.sum_embDomain]
  rw [Finsupp.sum_fintype _ _ (by intro; rfl)]
  exact deningerFinitePlaceLogProfile_global_reciprocity alpha

theorem deningerAllPlaceLogProfile_ne_zero_of_not_isOfFinOrder
    (alpha : Kˣ) (halpha : ¬ IsOfFinOrder (alpha : K)) :
    deningerAllPlaceLogProfile alpha ≠ 0 := by
  intro hzero
  apply halpha
  apply (deningerKummerReciprocityHom_eq_zero_iff K alpha).mp
  apply Subtype.ext
  change deningerKummerTest K (Units.ne_zero alpha) = 0
  ext w
  change deningerKummerFun K (alpha : K) w = 0
  cases w with
  | inl w =>
      have hw := Finsupp.ext_iff.mp hzero (Sum.inl w)
      simpa only [deningerKummerFun_inl, deningerAllPlaceLogProfile_inl,
        Finsupp.zero_apply] using hw
  | inr w =>
      have hw := Finsupp.ext_iff.mp hzero (Sum.inr w)
      simpa only [deningerKummerFun_inr, deningerAllPlaceLogProfile_inr,
        Finsupp.zero_apply] using hw

theorem deningerAllPlaceLogProfile_two_le_support_card_of_not_isOfFinOrder
    (alpha : Kˣ) (halpha : ¬ IsOfFinOrder (alpha : K)) :
    2 ≤ (deningerAllPlaceLogProfile alpha).support.card :=
  finsupp_two_le_support_card_of_sum_eq_zero
    (deningerAllPlaceLogProfile alpha)
    (deningerAllPlaceLogProfile_sum_eq_zero alpha)
    (deningerAllPlaceLogProfile_ne_zero_of_not_isOfFinOrder alpha halpha)

theorem deningerAllPlaceLogProfile_exists_two_nonzero_places_of_not_isOfFinOrder
    (alpha : Kˣ) (halpha : ¬ IsOfFinOrder (alpha : K)) :
    ∃ v w : DeningerPlace K, v ≠ w ∧
      deningerAllPlaceLogProfile alpha v ≠ 0 ∧ deningerAllPlaceLogProfile alpha w ≠ 0 :=
  finsupp_exists_two_nonzero_places_of_sum_eq_zero
    (deningerAllPlaceLogProfile alpha)
    (deningerAllPlaceLogProfile_sum_eq_zero alpha)
    (deningerAllPlaceLogProfile_ne_zero_of_not_isOfFinOrder alpha halpha)

end RHTower
