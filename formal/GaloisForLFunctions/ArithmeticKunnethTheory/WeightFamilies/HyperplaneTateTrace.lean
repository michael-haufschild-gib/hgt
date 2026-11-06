import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanMomentCounts

/-!
# The explicit hyperplane contribution to Kloosterman moments

Deleting the leading coordinate identifies a torus hyperplane with the complement
of the smaller hyperplane. The resulting recurrence determines its point count and
isolates its contribution from the double-zero locus in the global moment identity.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem normalizedCoordinateZeroTorus_card_zero :
    (normalizedCoordinateZeroTorus (F := F) 0).card = 0 := by
  simp [normalizedCoordinateZeroTorus]

/-- Deleting the leading coordinate identifies the hyperplane with the complement
of the smaller hyperplane: the deleted coordinate is forced and must be nonzero. -/
theorem normalizedCoordinateZeroTorus_card_complement (m : ℕ) :
    (normalizedCoordinateZeroTorus (F := F) (m + 1)).card =
      ((univ : Finset (MomentTorus F m)) \ normalizedCoordinateZeroTorus m).card := by
  apply card_bij (fun (x : MomentTorus F (m + 1)) _ => Fin.tail x)
  · intro x hx
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro ht
    have hx' := (mem_filter.mp hx).2
    have ht' := (mem_filter.mp ht).2
    rw [Fin.sum_univ_succ] at hx'
    change 1 + ∑ j : Fin m, (x j.succ : F) = 0 at ht'
    apply (x 0).property
    linear_combination hx' - ht'
  · intro x hx y hy htail
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    rw [Fin.sum_univ_succ] at hx' hy'
    have hs := congrArg (fun t : MomentTorus F m => ∑ j, (t j : F)) htail
    change (∑ j : Fin m, (x j.succ : F)) = ∑ j : Fin m, (y j.succ : F) at hs
    have hzero : (x 0 : F) = (y 0 : F) := by linear_combination hx' - hy' - hs
    funext j
    refine Fin.cases (Subtype.ext hzero) (fun j => congrFun htail j) j
  · intro y hy
    have hy0 : 1 + ∑ j, (y j : F) ≠ 0 := by
      intro h
      exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
    let x : MomentTorus F (m + 1) :=
      Fin.cons ⟨-(1 + ∑ j, (y j : F)), neg_ne_zero.mpr hy0⟩ y
    refine ⟨x, ?_, rfl⟩
    simp only [normalizedCoordinateZeroTorus, mem_filter, mem_univ, true_and,
      x, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    ring

/-- The deletion recurrence for the normalized torus hyperplane. -/
theorem normalizedCoordinateZeroTorus_card_recurrence (m : ℕ) :
    (normalizedCoordinateZeroTorus (F := F) (m + 1)).card +
      (normalizedCoordinateZeroTorus (F := F) m).card = (Fintype.card F - 1) ^ m := by
  rw [normalizedCoordinateZeroTorus_card_complement,
    card_sdiff_add_card_eq_card (subset_univ _), card_univ]
  simp only [MomentTorus, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_subtype_compl (fun r : F => r = 0), Fintype.card_subtype_eq]

/-- The hyperplane count is the integral polynomial determined by deletion. -/
theorem normalizedCoordinateZeroTorus_card_formula (m : ℕ) :
    (Fintype.card F : ℤ) * (normalizedCoordinateZeroTorus (F := F) m).card =
      ((Fintype.card F : ℤ) - 1) ^ m - (-1) ^ m := by
  induction m with
  | zero => simp [normalizedCoordinateZeroTorus_card_zero]
  | succ m ih =>
      have hrec : ((normalizedCoordinateZeroTorus (F := F) (m + 1)).card : ℤ) +
          (normalizedCoordinateZeroTorus (F := F) m).card = ((Fintype.card F : ℤ) - 1) ^ m := by
        have h := congrArg (fun n : ℕ => (n : ℤ)) (normalizedCoordinateZeroTorus_card_recurrence (F := F) m)
        simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_sub Fintype.card_pos, Nat.cast_one] using h
      rw [pow_succ, pow_succ]
      linear_combination (Fintype.card F : ℤ) * hrec - ih

/-- Only the double-zero count remains after the explicit hyperplane contribution is removed. -/
theorem kloosterman_moment_double_count {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) (m : ℕ) :
    ∑ a : F, SignedSuccessorArithmetic.kloosterman ψ a b ^ (m + 1) =
      (Fintype.card F : ℂ) ^ 2 * (normalizedDoubleZeroTorus (F := F) m).card -
        ((Fintype.card F : ℂ) - 1) ^ m + (-1) ^ m := by
  have hB : (Fintype.card F : ℂ) * (normalizedCoordinateZeroTorus (F := F) m).card =
      ((Fintype.card F : ℂ) - 1) ^ m - (-1) ^ m := by
    exact_mod_cast normalizedCoordinateZeroTorus_card_formula (F := F) m
  rw [kloosterman_moment_projective_counts hψ hb, mul_sub, hB]
  ring

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
