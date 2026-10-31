import GaloisForLFunctions.HeckeKreinToeplitz.Index.LocallyPeriodicProjection
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnForm
import GaloisForLFunctions.ArithmeticPositiveDuality.AMautnerPhenomenonForTheAffineGroupOfQ
import Mathlib.Algebra.Ring.Periodic

/-!
# Locally periodic rational translations

Right invariance under integer translation makes each rational translation locally periodic
on the kernel column space. A column at slope `a` has period `den(b/a)` under translation by `b`.
-/

open Module
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Translation powers in any rational affine representation are integer translation multiples. -/
theorem rational_affine_translation_pow {M : Type*} [Monoid M]
    (ρ : AffineGroupQ →* M) (b : ℚ) (n : ℕ) :
    ρ (translation b) ^ n = ρ (translation ((n : ℚ) * b)) := by
  induction n with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, translation_zero, map_one]
  | succ n ih =>
    rw [pow_succ, ih, ← map_mul, ← translation_add]
    congr 2
    push_cast
    ring

/-- Move a translation across an affine map by dividing its step by the slope. -/
theorem translation_mul_affine_eq (g : AffineGroupQ) (b : ℚ) :
    translation b * g = g * translation (b / affSlope g) := by
  apply affine_ext
  · simp only [affSlope_mul, affSlope_translation, one_mul, mul_one]
  · simp only [affShift_mul, affSlope_translation, affShift_translation, one_mul]
    field_simp [affSlope_ne_zero g]
    ring

/-- A right unit period gives every right integer period. -/
theorem right_integer_translation_period {k : AffineGroupQ → ℂ}
    (hp : ∀ g, k (g * translation 1) = k g) (g : AffineGroupQ) (m : ℤ) :
    k (g * translation (m : ℚ)) = k g := by
  have h : Function.Periodic (fun b : ℚ => k (g * translation b)) 1 := by
    intro b
    change k (g * translation (b + 1)) = k (g * translation b)
    rw [translation_add, ← mul_assoc]
    exact hp _
  simpa only [mul_one, translation_zero] using h.int_mul_eq m

/-- The denominator of the rescaled translation step is a period of each kernel column. -/
theorem kernel_translation_column_period {k : AffineGroupQ → ℂ}
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (g : AffineGroupQ) :
    ((kernelColumnRepresentation k (translation b)) ^ (b / affSlope g).den)
      (kernelColumnPoint k g) = kernelColumnPoint k g := by
  let q := b / affSlope g
  change ((kernelColumnRepresentation k (translation b)) ^ q.den) (kernelColumnPoint k g) = _
  rw [rational_affine_translation_pow, kernelColumnRepresentation_point, translation_mul_affine_eq]
  have he : (q.den : ℚ) * b / affSlope g = q.num := by
    calc
      (q.den : ℚ) * b / affSlope g = q * (q.den : ℚ) := by dsimp only [q]; ring
      _ = q.num := Rat.mul_den_eq_num q
  rw [he]
  apply Subtype.ext
  funext x
  change k (x⁻¹ * (g * translation (q.num : ℚ))) = k (x⁻¹ * g)
  rw [← mul_assoc]
  exact right_integer_translation_period hp (x⁻¹ * g) q.num

/-- Right integer invariance makes every rational translation locally periodic on kernel columns. -/
theorem kernel_translation_locally_periodic {k : AffineGroupQ → ℂ}
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (v : kernelColumnSpan k) :
    ∃ m : ℕ, m ≠ 0 ∧ ((kernelColumnRepresentation k (translation b)) ^ m) v = v := by
  let T := kernelColumnRepresentation k (translation b)
  have hpoint (g : AffineGroupQ) : kernelColumnPoint k g ∈ periodicVectorSubmodule T :=
    ⟨(b / affSlope g).den, Nat.ne_of_gt (b / affSlope g).den_pos,
      kernel_translation_column_period hp b g⟩
  obtain ⟨n, g, c, rfl⟩ := exists_kernelColumnPoint_fin_sum k v
  change (∑ i, c i • kernelColumnPoint k (g i)) ∈ periodicVectorSubmodule T
  exact (periodicVectorSubmodule T).sum_mem (fun i _ =>
    (periodicVectorSubmodule T).smul_mem (c i) (hpoint (g i)))

#print axioms kernel_translation_locally_periodic
end GaloisForLFunctions.BiarithmeticGeometry
