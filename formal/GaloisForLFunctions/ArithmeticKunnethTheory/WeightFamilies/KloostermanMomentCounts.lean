import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanMomentHypersurface

/-!
# Kloosterman moments as differences of torus point counts

Scaling a nonzero parameter preserves the global moment. Orthogonality in both
parameters therefore expresses it as the difference of two explicit point counts:
one imposes vanishing coordinate sum, the other also vanishing reciprocal sum.
-/

open Finset AddChar
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

open SignedSuccessorArithmetic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Torus tuples whose coordinate sum vanishes. -/
def coordinateZeroTorus (m : ℕ) : Finset (MomentTorus F m) :=
  univ.filter (fun x => ∑ j, (x j : F) = 0)

/-- Torus tuples whose coordinate and reciprocal coordinate sums both vanish. -/
def doubleZeroTorus (m : ℕ) : Finset (MomentTorus F m) :=
  (coordinateZeroTorus m).filter (fun x => ∑ j, (x j : F)⁻¹ = 0)

/-- Scaling the summation variable moves a nonzero parameter into the first slot. -/
theorem kloosterman_rescale_nonzero (ψ : AddChar F ℂ) (a : F) {b : F} (hb : b ≠ 0) :
    kloosterman ψ a b = kloosterman ψ (a * b) 1 := by
  unfold kloosterman
  refine sum_nbij' (fun x : F => x / b) (fun x : F => b * x) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact div_ne_zero hx hb
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact mul_ne_zero hb hx
  · intro x _
    exact mul_div_cancel₀ x hb
  · intro x _
    simp [hb]
  · intro x hx
    have hx0 := (mem_filter.mp hx).2
    congr 1
    field_simp
    <;> ring

/-- The global tensor moment is independent of the nonzero second parameter. -/
theorem kloosterman_moment_nonzero_parameter (ψ : AddChar F ℂ) {b : F} (hb : b ≠ 0)
    (m : ℕ) :
    ∑ a : F, kloosterman ψ a b ^ m = ∑ a : F, kloosterman ψ a 1 ^ m := by
  simp_rw [kloosterman_rescale_nonzero ψ _ hb]
  exact sum_nbij' (fun a : F => a * b) (fun a : F => a / b)
    (by simp) (by simp) (by simp [hb]) (by simp [hb]) (by intros; rfl)

/-- Orthogonality in both parameters counts the intersection of the two hypersurfaces. -/
theorem kloosterman_double_moment_count {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (m : ℕ) :
    ∑ b : F, ∑ a : F, kloosterman ψ a b ^ m =
      (Fintype.card F : ℂ) ^ 2 * (doubleZeroTorus (F := F) m).card := by
  unfold doubleZeroTorus coordinateZeroTorus
  rw [sum_congr rfl (fun b _ => kloosterman_moment_hypersurface hψ b m)]
  rw [← mul_sum, sum_comm]
  simp_rw [sum_mulShift _ hψ]
  simp only [Nat.cast_ite, Nat.cast_zero]
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  ring

/-- At the zero parameter only the coordinate-sum constraint remains. -/
theorem kloosterman_zero_parameter_moment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (m : ℕ) :
    ∑ a : F, kloosterman ψ a 0 ^ m =
      (Fintype.card F : ℂ) * (coordinateZeroTorus (F := F) m).card := by
  rw [kloosterman_moment_hypersurface hψ]
  simp [coordinateZeroTorus]

/-- Every nonzero-parameter moment is a difference of explicit torus point counts. -/
theorem kloosterman_moment_count_identity {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) (m : ℕ) :
    ((Fintype.card F : ℂ) - 1) * (∑ a : F, kloosterman ψ a b ^ m) =
      (Fintype.card F : ℂ) ^ 2 * (doubleZeroTorus (F := F) m).card -
        (Fintype.card F : ℂ) * (coordinateZeroTorus (F := F) m).card := by
  have h := kloosterman_double_moment_count hψ m
  rw [← sum_filter_add_sum_filter_not univ (fun t : F => t ≠ 0)] at h
  have hz : (univ : Finset F).filter (fun t => ¬ t ≠ 0) = {0} := by ext; simp
  have hc : ((univ.filter (fun t : F => t ≠ 0)).card : ℂ) = (Fintype.card F : ℂ) - 1 := by
    rw [card_units_filter, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  have hconst : (∑ t ∈ univ.filter (fun t : F => t ≠ 0), ∑ a : F, kloosterman ψ a t ^ m) =
      ((Fintype.card F : ℂ) - 1) * (∑ a : F, kloosterman ψ a b ^ m) := by
    rw [sum_congr rfl (fun t ht =>
      (kloosterman_moment_nonzero_parameter ψ (mem_filter.mp ht).2 m).trans
        (kloosterman_moment_nonzero_parameter ψ hb m).symm), sum_const, nsmul_eq_mul, hc]
  rw [hconst, hz, sum_singleton, kloosterman_zero_parameter_moment hψ] at h
  exact eq_sub_iff_add_eq.mpr h

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
