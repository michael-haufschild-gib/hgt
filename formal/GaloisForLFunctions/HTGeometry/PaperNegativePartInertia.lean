import GaloisForLFunctions.HTGeometry.PaperFiniteNegativePart
import GaloisForLFunctions.RHTower.SchattenApproximation

/-! # Exact negative index and optimal arbitrary positive correction

The dimension of the full negative-part range is the negative index of the
original form and the minimum rank of any positive repair. Corrections may mix
all coordinates and need not commute with the original source operator.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PaperNegativePart

open RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_repair_le (Q : E →L[ℂ] E) : ‖repair Q‖ ≤ ‖Q‖ :=
  CStarAlgebra.norm_negPart_le Q

theorem negative_subspace_finite_dimension (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    [FiniteDimensional ℂ (negativeSpace Q)] (W : Submodule ℂ E)
    (hW : ∀ x ∈ W, x ≠ 0 → (inner ℂ (Q x) x).re < 0) :
    FiniteDimensional ℂ W ∧ Module.finrank ℂ W ≤ negativeRank Q := by
  let L : W →ₗ[ℂ] negativeSpace Q :=
    ((repair Q).toLinearMap.comp W.subtype).codRestrict _ (fun x => ⟨x, rfl⟩)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have hC : repair Q (x : E) = 0 := congrArg Subtype.val hx
    have hneg := hW x x.property (fun h => hx0 (Subtype.ext h))
    have hpos := (repaired_positive Q hQ).re_inner_nonneg_left (x : E)
    change 0 ≤ (inner ℂ ((Q + repair Q) (x : E)) (x : E)).re at hpos
    rw [add_apply, hC, add_zero] at hpos
    exact not_lt_of_ge hpos hneg
  exact ⟨FiniteDimensional.of_injective L hinj, LinearMap.finrank_le_finrank_of_injective hinj⟩

theorem exact_negative_index (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    [FiniteDimensional ℂ (negativeSpace Q)] :
    (∀ W : Submodule ℂ E,
      (∀ x ∈ W, x ≠ 0 → (inner ℂ (Q x) x).re < 0) →
        FiniteDimensional ℂ W ∧ Module.finrank ℂ W ≤ negativeRank Q) ∧
      ∃ W : Submodule ℂ E, Module.finrank ℂ W = negativeRank Q ∧
        ∀ x ∈ W, x ≠ 0 → (inner ℂ (Q x) x).re < 0 :=
  ⟨negative_subspace_finite_dimension Q hQ,
    negativeSpace Q, rfl, fun _ hx hx0 => negativeSpace_strict Q hQ hx hx0⟩

theorem negativeRank_le_repair_rank (Q F : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) {r : ℕ}
    (hr : HasRankLE F r) (hpos : (Q + F).IsPositive) : negativeRank Q ≤ r := by
  obtain ⟨V, hV, hdim, hmem⟩ := hr
  letI := hV
  let L : negativeSpace Q →ₗ[ℂ] V :=
    (F.toLinearMap.comp (negativeSpace Q).subtype).codRestrict V (fun x => hmem x)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have hF : F (x : E) = 0 := congrArg Subtype.val hx
    have hneg := negativeSpace_strict Q hQ x.property (fun h => hx0 (Subtype.ext h))
    have hp := hpos.re_inner_nonneg_left (x : E)
    change 0 ≤ (inner ℂ ((Q + F) (x : E)) (x : E)).re at hp
    rw [add_apply, hF, add_zero] at hp
    exact not_lt_of_ge hp hneg
  exact (LinearMap.finrank_le_finrank_of_injective hinj).trans hdim

theorem hasRankLE_repair (Q : E →L[ℂ] E) [FiniteDimensional ℂ (negativeSpace Q)] :
    HasRankLE (repair Q) (negativeRank Q) :=
  ⟨negativeSpace Q, inferInstance, le_rfl, fun x => ⟨x, rfl⟩⟩

theorem positive_repair_rank_iff (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    [FiniteDimensional ℂ (negativeSpace Q)] (r : ℕ) :
    (∃ F : E →L[ℂ] E, HasRankLE F r ∧ (Q + F).IsPositive) ↔ negativeRank Q ≤ r := by
  constructor
  · rintro ⟨F, hr, hp⟩
    exact negativeRank_le_repair_rank Q F hQ hr hp
  · intro hr
    exact ⟨repair Q, (hasRankLE_repair Q).mono hr, repaired_positive Q hQ⟩

theorem repair_exact_rank (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    [FiniteDimensional ℂ (negativeSpace Q)] (r : ℕ) :
    HasRankLE (repair Q) r ↔ negativeRank Q ≤ r :=
  ⟨fun h => negativeRank_le_repair_rank Q _ hQ h (repaired_positive Q hQ),
    fun h => (hasRankLE_repair Q).mono h⟩

theorem negativeRank_mono_of_form_le (Q R : E →L[ℂ] E)
    (hQ : IsSelfAdjoint Q) (hR : IsSelfAdjoint R)
    [FiniteDimensional ℂ (negativeSpace R)]
    (hle : ∀ x, (inner ℂ (R x) x).re ≤ (inner ℂ (Q x) x).re) :
    negativeRank Q ≤ negativeRank R :=
  (negative_subspace_finite_dimension R hR (negativeSpace Q)
    (fun x hx hx0 => (hle x).trans_lt (negativeSpace_strict Q hQ hx hx0))).2

theorem negativeRank_eq_zero_iff (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    [FiniteDimensional ℂ (negativeSpace Q)] : negativeRank Q = 0 ↔ Q.IsPositive := by
  rw [negativeRank, Submodule.finrank_eq_zero, negativeSpace, LinearMap.range_eq_bot]
  constructor
  · intro h
    apply (repair_eq_zero_iff Q hQ).1
    ext x
    exact congrArg (fun L : E →ₗ[ℂ] E => L x) h
  · intro h
    exact congrArg ContinuousLinearMap.toLinearMap ((repair_eq_zero_iff Q hQ).2 h)

end GaloisForLFunctions.HTGeometry.PaperNegativePart
