import GaloisForLFunctions.HTGeometry.PositiveDefiniteCoordinateFrame
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coordinate maxima and Euclidean norms

A finite nonempty real coordinate vector attains its supremum norm at one
coordinate. The coordinate-axis vectors attain the same absolute-value norm.
These identities allow a coordinatewise decay certificate to be expressed
in terms of the complete direction vector.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.FiniteCoordinateNorms
noncomputable section

/-- A finite nonempty real coordinate vector attains its norm at one coordinate. -/
theorem exists_norm_eq_abs_coordinate {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℝ) :
    ∃ i, ‖v‖ = |v i| := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖₊) Finset.univ_nonempty
  have hs : Finset.univ.sup (fun j => ‖v j‖₊) = ‖v i‖₊ :=
    le_antisymm (Finset.sup_le hmax) (Finset.le_sup (f := fun j => ‖v j‖₊) hi)
  refine ⟨i, ?_⟩
  rw [Pi.norm_def, hs]
  exact Real.norm_eq_abs (v i)

/-- A vector supported on the first coordinate has exactly that coordinate's absolute-value norm. -/
theorem norm_cons_zero (r : ℕ) (θ : ℝ) :
    ‖(Fin.cons θ (0 : Fin r → ℝ) : Fin (r + 1) → ℝ)‖ = |θ| := by
  obtain ⟨i, hi⟩ := exists_norm_eq_abs_coordinate
    (Fin.cons θ (0 : Fin r → ℝ) : Fin (r + 1) → ℝ)
  have hb (j : Fin (r + 1)) : |(Fin.cons θ (0 : Fin r → ℝ) : Fin (r + 1) → ℝ) j| ≤ |θ| := by
    refine Fin.cases ?_ (fun q => ?_) j
    · exact le_rfl
    · simpa only [Fin.cons_succ, Pi.zero_apply, abs_zero] using abs_nonneg θ
  apply le_antisymm (hi.trans_le (hb i))
  simpa only [Fin.cons_zero, Real.norm_eq_abs] using
    norm_le_pi_norm (Fin.cons θ (0 : Fin r → ℝ) : Fin (r + 1) → ℝ) 0

/-- The ordinary Euclidean norm of a real coordinate vector. -/
def euclideanNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖

theorem euclideanNorm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ euclideanNorm v := norm_nonneg _

theorem euclideanNorm_sq {n : ℕ} (v : Fin n → ℝ) :
    euclideanNorm v ^ 2 = ∑ i, v i ^ 2 := by
  rw [euclideanNorm, EuclideanSpace.norm_sq_eq]
  change (∑ i, ‖v i‖ ^ 2) = ∑ i, v i ^ 2
  simp only [Real.norm_eq_abs, sq_abs]

/-- The corpus's coordinate-square bound gives an explicit comparison with the maximum norm. -/
theorem euclideanNorm_le_card_mul_norm (r : ℕ) (v : Fin (r + 1) → ℝ) :
    euclideanNorm v ≤ ((r + 1 : ℕ) : ℝ) * ‖v‖ := by
  have hsq : euclideanNorm v ^ 2 ≤ ((r + 1 : ℕ) : ℝ) * ‖v‖ ^ 2 := by
    rw [euclideanNorm_sq]
    exact GaloisForLFunctions.HTGeometry.sum_sq_le_card_mul_pi_norm_sq v
  have hd : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hd2 : ((r + 1 : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2 := by
    simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (r + 1))
  apply (sq_le_sq₀ (euclideanNorm_nonneg v)
    (mul_nonneg (Nat.cast_nonneg (r + 1)) (norm_nonneg v))).mp
  calc
    _ ≤ ((r + 1 : ℕ) : ℝ) * ‖v‖ ^ 2 := hsq
    _ ≤ ((r + 1 : ℕ) : ℝ) ^ 2 * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hd2 (sq_nonneg ‖v‖)
    _ = _ := by ring

/-- Coordinate-axis directions have the same exact norm in the Euclidean and maximum conventions. -/
theorem euclideanNorm_cons_zero (r : ℕ) (θ : ℝ) :
    euclideanNorm (Fin.cons θ (0 : Fin r → ℝ)) = |θ| := by
  apply (sq_eq_sq₀ (euclideanNorm_nonneg _) (abs_nonneg θ)).mp
  rw [euclideanNorm_sq, sq_abs, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero, add_zero]

#print axioms exists_norm_eq_abs_coordinate
#print axioms norm_cons_zero
#print axioms euclideanNorm_sq
#print axioms euclideanNorm_le_card_mul_norm
#print axioms euclideanNorm_cons_zero

end
end GaloisForLFunctions.BiarithmeticGeometry.FiniteCoordinateNorms
