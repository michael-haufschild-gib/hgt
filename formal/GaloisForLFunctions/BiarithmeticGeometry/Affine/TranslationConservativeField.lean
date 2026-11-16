import GaloisForLFunctions.BiarithmeticGeometry.Affine.FiniteTranslationUnipotence
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Conservative matrix fields from rational affine translations

Rational translation representations give flat matrix fields on every integer
lattice. Transport depends only on the total displacement; parallel paths have
the same transport and a multiple direction is an exact subsampling.

These are the integral-shift and direction laws of *New Directions in Irrationality*,
Proposition 3.5 and Corollary 3.6, specialized to affine representations.
Unipotence additionally bounds the order of every trajectory's finite differences
by the matrix dimension.
-/

open GaloisForLFunctions.ArithmeticPositiveDuality

namespace GaloisForLFunctions.BiarithmeticGeometry

variable {n d : ℕ}

/-- A lattice displacement acts by the corresponding rational translation. -/
def translationField (ρ : AffineGroupQ →* Matrix (Fin n) (Fin n) ℂ)
    (b : Fin d → ℚ) (v : Fin d → ℤ) : Matrix (Fin n) (Fin n) ℂ :=
  ρ (translation (∑ i, (v i : ℚ) * b i))

@[simp] theorem translationField_zero
    (ρ : AffineGroupQ →* Matrix (Fin n) (Fin n) ℂ) (b : Fin d → ℚ) :
    translationField ρ b 0 = 1 := by
  simp [translationField, translation_zero]

/-- The cocycle law is exact, with no dependence on a lattice base point. -/
theorem translationField_add
    (ρ : AffineGroupQ →* Matrix (Fin n) (Fin n) ℂ) (b : Fin d → ℚ)
    (v w : Fin d → ℤ) :
    translationField ρ b (v + w) = translationField ρ b v * translationField ρ b w := by
  simp only [translationField, Pi.add_apply, Int.cast_add, add_mul,
    Finset.sum_add_distrib, translation_add, map_mul]

/-- Parallel transport around any elementary lattice square has zero defect. -/
theorem translationField_flat
    (ρ : AffineGroupQ →* Matrix (Fin n) (Fin n) ℂ) (b : Fin d → ℚ)
    (v w : Fin d → ℤ) :
    translationField ρ b v * translationField ρ b w =
      translationField ρ b w * translationField ρ b v := by
  rw [← translationField_add, ← translationField_add, add_comm v w]

/-- Ordered path transport depends only on the sum of the lattice increments. -/
theorem translationField_path
    (ρ : AffineGroupQ →* Matrix (Fin n) (Fin n) ℂ) (b : Fin d → ℚ)
    (path : List (Fin d → ℤ)) :
    (path.map (translationField ρ b)).prod = translationField ρ b path.sum := by
  induction path with
  | nil => simp
  | cons v path ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, ih, translationField_add]

/-- Repeating one direction gives its integer-multiple displacement. -/
theorem translationField_nsmul
    (ρ : AffineGroupQ →* Matrix (Fin n) (Fin n) ℂ) (b : Fin d → ℚ)
    (v : Fin d → ℤ) (k : ℕ) :
    translationField ρ b (k • v) = translationField ρ b v ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, translationField_add, ih, pow_succ]

/-- A multiple direction is the same trajectory sampled at multiples of its stride. -/
theorem translationField_stride
    (ρ : AffineGroupQ →* Matrix (Fin n) (Fin n) ℂ) (b : Fin d → ℚ)
    (v : Fin d → ℤ) (m k : ℕ) :
    translationField ρ b (m • v) ^ k = translationField ρ b v ^ (m * k) := by
  rw [translationField_nsmul, pow_mul]

/-- Finite differences of an affine translation orbit are powers of its unipotent defect. -/
theorem affine_translation_iterated_difference
    (ρ : AffineGroupQ →* Matrix (Fin n) (Fin n) ℂ) (b x : ℚ) (k : ℕ) :
    (fwdDiff b)^[k] (fun t : ℚ => ρ (translation t)) x =
      ρ (translation x) * (ρ (translation b) - 1) ^ k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      change (fwdDiff b)^[k] (fun t : ℚ => ρ (translation t)) (x + b) -
        (fwdDiff b)^[k] (fun t : ℚ => ρ (translation t)) x = _
      rw [ih, ih, translation_add, map_mul, pow_succ']
      noncomm_ring

/-- Every rational direction has an annihilator of order at most the matrix dimension. -/
theorem affine_translation_difference_vanishes
    (ρ : AffineGroupQ →* Matrix (Fin n) (Fin n) ℂ) (b x : ℚ) :
    (fwdDiff b)^[n] (fun t : ℚ => ρ (translation t)) x = 0 := by
  rw [affine_translation_iterated_difference,
    finite_rational_affine_translation_unipotent, mul_zero]

#print axioms translationField_path
#print axioms translationField_stride
#print axioms affine_translation_difference_vanishes

end GaloisForLFunctions.BiarithmeticGeometry
