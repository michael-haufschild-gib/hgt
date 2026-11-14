import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Hexablock polynomial coordinates and Brown–Halmos identities

The coordinates `w(u-1)/2`, `v(u+1)/2`, `wz(u+1)/2`, `uvwz` split
isometric energy. The slice `(u,1,1,1)` preserves the operator and adjoint
commutants, and its Brown–Halmos equations are equivalent to `u* t u = t`.

These are the algebraic mechanisms in the hexablock parametrization and
Brown–Halmos relations of Pal–Su–Tomar, *Hardy Spaces and Toeplitz operators
on the Hexablock*, §§5 and 7.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.Hexablock
variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]

def halfSum (u v : A) : A := (1 / 2 : ℝ) • (u + v)
def halfDiff (u v : A) : A := (1 / 2 : ℝ) • (u - v)

/-- Polarization splits a quadratic form between the sum and difference channels. -/
theorem polarization (u v t : A) :
    star (halfDiff u v) * t * halfDiff u v +
      star (halfSum u v) * t * halfSum u v =
        (1 / 2 : ℝ) • (star u * t * u + star v * t * v) := by
  simp only [halfSum, halfDiff, star_smul, star_add, star_sub, star_trivial,
    smul_mul_assoc, mul_smul_comm, smul_smul, add_mul, sub_mul, mul_add, mul_sub,
    smul_add, smul_sub]
  module

omit [Algebra ℝ A] [StarModule ℝ A] in
/-- Multiplication by an isometry leaves the Gram operator unchanged. -/
theorem gram_mul (u v : A) (hu : star u * u = 1) :
    star (u * v) * (u * v) = star v * v := by
  rw [star_mul, mul_assoc, ← mul_assoc (star u), hu, one_mul]

omit [Algebra ℝ A] [StarModule ℝ A] in
/-- Isometries are closed under multiplication, without a commutativity requirement. -/
theorem isometry_mul (u v : A) (hu : star u * u = 1) (hv : star v * v = 1) :
    star (u * v) * (u * v) = 1 := by
  rw [gram_mul u v hu, hv]

omit [Algebra ℝ A] [StarModule ℝ A] in
theorem isometry_pow (u : A) (hu : star u * u = 1) (n : ℕ) :
    star (u ^ n) * u ^ n = 1 := by
  induction n with
  | zero => simp only [pow_zero, star_one, mul_one]
  | succ n ih => simpa only [pow_succ] using isometry_mul _ _ ih hu

/-- The two channels of an isometry form an exact partition of identity. -/
theorem half_gram (u : A) (hu : star u * u = 1) :
    star (halfDiff u 1) * halfDiff u 1 +
      star (halfSum u 1) * halfSum u 1 = 1 := by
  have h := polarization u 1 1
  simp only [mul_one, star_one, hu] at h
  rw [h, smul_add]
  module

/-- Polynomial parametrization of the hexablock. -/
def a (u w : A) : A := w * halfDiff u 1
def x₁ (u v : A) : A := v * halfSum u 1
def x₂ (u w z : A) : A := (w * z) * halfSum u 1
def x₃ (u v w z : A) : A := u * v * w * z

/-- Both energy identities follow from the same polarization identity. -/
theorem energy (u v w z : A)
    (hu : star u * u = 1) (hv : star v * v = 1)
    (hw : star w * w = 1) (hz : star z * z = 1) :
    (star (a u w) * a u w + star (x₁ u v) * x₁ u v = 1) ∧
    (star (a u w) * a u w + star (x₂ u w z) * x₂ u w z = 1) ∧
    star (x₃ u v w z) * x₃ u v w z = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [a, x₁, gram_mul _ _ hw, gram_mul _ _ hv, half_gram u hu]
  · rw [a, x₂, gram_mul _ _ hw, gram_mul _ _ (isometry_mul _ _ hw hz), half_gram u hu]
  · exact isometry_mul _ _ (isometry_mul _ _ (isometry_mul _ _ hu hv) hw) hz

/-- Brown–Halmos relations for the four coordinates of a hexablock isometry. -/
def BrownHalmos (a x y p t : A) : Prop :=
  star p * t * p = t ∧
  star x * t * p = t * y ∧
  star a * t * a + star y * t * y = t ∧
  star a * t * a + star x * t * x = t

/-- The slice `(u,1,1,1)` has exactly the fixed operators of `t ↦ u* t u`.
No normality or isometry assumption is needed for this equivalence. -/
theorem slice_brownHalmos_iff (u t : A) :
    BrownHalmos (halfDiff u 1) (halfSum u 1) (halfSum u 1) u t ↔
      star u * t * u = t := by
  refine ⟨fun h => h.1, fun h => ?_⟩
  have henergy : star (halfDiff u 1) * t * halfDiff u 1 +
      star (halfSum u 1) * t * halfSum u 1 = t := by
    rw [polarization, h, star_one, one_mul, mul_one, smul_add]
    module
  refine ⟨h, ?_, henergy, henergy⟩
  simp only [halfSum, star_smul, star_add, star_one, star_trivial,
    smul_mul_assoc, add_mul, one_mul, mul_smul_comm, mul_add, mul_one, h]
  module

omit [StarRing A] [StarModule ℝ A] in
/-- The parametrized sum and difference recover the original operator. -/
theorem halfDiff_add_halfSum (u : A) : halfDiff u 1 + halfSum u 1 = u := by
  simp only [halfDiff, halfSum, smul_sub, smul_add]
  module

omit [StarRing A] [StarModule ℝ A] in
/-- Splitting an operator preserves its commutant exactly. -/
theorem slice_commutant_iff (u t : A) :
    (Commute t (halfDiff u 1) ∧ Commute t (halfSum u 1)) ↔ Commute t u := by
  constructor
  · intro h
    have hh := h.1.add_right h.2
    rwa [halfDiff_add_halfSum] at hh
  · intro h
    exact ⟨(h.sub_right (Commute.one_right t)).smul_right _,
      (h.add_right (Commute.one_right t)).smul_right _⟩

/-- Splitting also preserves commutation with the adjoint. -/
theorem slice_adjoint_commutant_iff (u t : A) :
    (Commute t (star (halfDiff u 1)) ∧ Commute t (star (halfSum u 1))) ↔
      Commute t (star u) := by
  simpa only [halfDiff, halfSum, star_smul, star_sub, star_add, star_one, star_trivial]
    using slice_commutant_iff (star u) t

/-- The adjoint of the sum channel cancels the original isometry. -/
theorem star_halfSum_mul (u : A) (hu : star u * u = 1) :
    star (halfSum u 1) * u = halfSum u 1 := by
  simp only [halfSum, star_smul, star_add, star_one, star_trivial,
    smul_mul_assoc, add_mul, one_mul, hu]
  rw [add_comm]

/-- The cross-coordinate identity only needs the first isometry to commute with the others. -/
theorem cross (u v w z : A) (hu : star u * u = 1) (hv : star v * v = 1)
    (huv : Commute u v) (huw : Commute u w) (huz : Commute u z) :
    star (x₁ u v) * x₃ u v w z = x₂ u w z := by
  calc
    star (x₁ u v) * x₃ u v w z =
        star (halfSum u 1) * (star v * v) * u * w * z := by
      simp only [x₁, x₃, star_mul]
      rw [huv.eq]
      noncomm_ring
    _ = halfSum u 1 * w * z := by rw [hv, mul_one, star_halfSum_mul u hu]
    _ = x₂ u w z := by
      have hw : Commute (halfSum u 1) w :=
        (huw.add_left (Commute.one_left w)).smul_left _
      have hz : Commute (halfSum u 1) z :=
        (huz.add_left (Commute.one_left z)).smul_left _
      rw [x₂, mul_assoc, (hw.mul_right hz).eq]

end GaloisForLFunctions.HTGeometry.Hexablock
