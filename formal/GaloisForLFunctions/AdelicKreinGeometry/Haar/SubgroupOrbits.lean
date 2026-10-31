import GaloisForLFunctions.AdelicKreinGeometry.Haar.GeneralOrbits
import GaloisForLFunctions.AdelicKreinGeometry.Haar.SubgroupEndpoints
import GaloisForLFunctions.AdelicKreinGeometry.Haar.TranslationSaturation
import GaloisForLFunctions.BiarithmeticGeometry.Affine.SubgroupOrders

/-!
# Cyclic orbits of subgroup-indicator successors

Identity-value saturation makes every successor-subgroup element a period.
Translation orbits of affine columns are therefore orthonormal through their
quotient order, and their fixed projections have reciprocal-order norm.
-/

open Module Finset
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- Every member of the successor subgroup is a period after integer invariance. -/
theorem subgroup_successor_right_invariant {H : AddSubgroup ℚ} {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) {b : ℚ} (hb : b ∈ H) (g : AffineGroupQ) :
    k (g * translation b) = k g := by
  apply translation_saturation_right_invariant hk hi hp b _ g
  rw [hs, if_pos hb, hasSubgroupSuccessor_one hs]

/-- The quotient order of the rescaled step is a period of each affine column. -/
theorem subgroup_successor_column_period {H : AddSubgroup ℚ} {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (g : AffineGroupQ) :
    ((kernelColumnRepresentation k (translation b)) ^ rationalSubgroupOrder H (b / affSlope g))
      (kernelColumnPoint k g) = kernelColumnPoint k g := by
  let q := b / affSlope g
  change ((kernelColumnRepresentation k (translation b)) ^ rationalSubgroupOrder H q)
    (kernelColumnPoint k g) = _
  rw [rational_affine_translation_pow, kernelColumnRepresentation_point, translation_mul_affine_eq]
  have he : (rationalSubgroupOrder H q : ℚ) * b / affSlope g =
      (rationalSubgroupOrder H q : ℚ) * q := by dsimp only [q]; ring
  rw [he]
  apply Subtype.ext
  funext x
  change k (x⁻¹ * (g * translation ((rationalSubgroupOrder H q : ℚ) * q))) = k (x⁻¹ * g)
  rw [← mul_assoc]
  exact subgroup_successor_right_invariant hk hi hs hp (rationalSubgroupOrder_mul_mem H q) _

/-- Distinct quotient classes give orthogonal positions in a translation orbit. -/
theorem subgroup_successor_affine_orbit_orthonormal {H : AddSubgroup ℚ}
    {k : AffineGroupQ → ℂ} (hk : IsHermKernel k) (hs : HasSubgroupSuccessor H k)
    (g : AffineGroupQ) (b : ℚ) {i j : ℕ}
    (hi : i < rationalSubgroupOrder H (b / affSlope g))
    (hj : j < rationalSubgroupOrder H (b / affSlope g)) :
    kernelColumnPairing k
      (((kernelColumnRepresentation k (translation b)) ^ i) (kernelColumnPoint k g))
      (((kernelColumnRepresentation k (translation b)) ^ j) (kernelColumnPoint k g)) =
      if i = j then 1 else 0 := by
  classical
  rw [affine_column_translation_orbit_pairing hk, hs]
  by_cases hij : i = j
  · simp only [hij, sub_self, zero_mul, H.zero_mem, ite_true]
  · rw [if_neg (nat_difference_not_mem_below_subgroupOrder H _ hi hj hij), if_neg hij]

/-- A subgroup-successor fixed projection has norm equal to the reciprocal quotient order. -/
theorem subgroup_successor_projection_pairing {H : AddSubgroup ℚ}
    (h1 : (1 : ℚ) ∈ H) {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (g : AffineGroupQ) :
    kernelColumnPairing k
      (translationFixedProjection k hp b (kernelColumnPoint k g))
      (translationFixedProjection k hp b (kernelColumnPoint k g)) =
      (rationalSubgroupOrder H (b / affSlope g) : ℂ)⁻¹ := by
  classical
  let d := rationalSubgroupOrder H (b / affSlope g)
  let T := kernelColumnRepresentation k (translation b)
  let v := kernelColumnPoint k g
  have hd : 0 < d := rationalSubgroupOrder_pos H h1 _
  have hperiod : (T ^ d) v = v := subgroup_successor_column_period hk hi hs hp b g
  have havg := kernelColumnPairing_projection_average hk (translation b)
    (kernel_translation_locally_periodic hp b) v v hd.ne' hperiod
  have hterm (j : ℕ) (hj : j ∈ range d) :
      kernelColumnPairing k v ((T ^ j) v) = if j = 0 then 1 else 0 := by
    have h := subgroup_successor_affine_orbit_orthonormal hk hs g b hd (mem_range.mp hj)
    simpa only [pow_zero, Module.End.one_apply, eq_comm] using h
  have hsum : (∑ j ∈ range d, kernelColumnPairing k v ((T ^ j) v)) = 1 := by
    calc
      (∑ j ∈ range d, kernelColumnPairing k v ((T ^ j) v)) =
          kernelColumnPairing k v ((T ^ 0) v) := by
        apply Finset.sum_eq_single 0
        · intro j hj hj0
          rw [hterm j hj, if_neg hj0]
        · intro h
          exact (h (mem_range.mpr hd)).elim
      _ = 1 := by rw [hterm 0 (mem_range.mpr hd), if_pos rfl]
  rw [hsum, mul_one] at havg
  exact havg

theorem subgroup_successor_projection_pairing_re {H : AddSubgroup ℚ}
    (h1 : (1 : ℚ) ∈ H) {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (g : AffineGroupQ) :
    (kernelColumnPairing k
      (translationFixedProjection k hp b (kernelColumnPoint k g))
      (translationFixedProjection k hp b (kernelColumnPoint k g))).re =
      (rationalSubgroupOrder H (b / affSlope g) : ℝ)⁻¹ := by
  rw [subgroup_successor_projection_pairing h1 hk hi hs hp]
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
    Complex.ofReal_re ((rationalSubgroupOrder H (b / affSlope g) : ℝ)⁻¹)

theorem subgroup_successor_projection_pairing_nonneg {H : AddSubgroup ℚ}
    (h1 : (1 : ℚ) ∈ H) {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (g : AffineGroupQ) :
    0 ≤ (kernelColumnPairing k
      (translationFixedProjection k hp b (kernelColumnPoint k g))
      (translationFixedProjection k hp b (kernelColumnPoint k g))).re := by
  rw [subgroup_successor_projection_pairing_re h1 hk hi hs hp]
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

#print axioms subgroup_successor_right_invariant
#print axioms subgroup_successor_affine_orbit_orthonormal
#print axioms subgroup_successor_projection_pairing
end GaloisForLFunctions.AdelicKreinGeometry
