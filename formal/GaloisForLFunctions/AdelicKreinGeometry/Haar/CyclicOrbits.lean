import GaloisForLFunctions.BiarithmeticGeometry.Affine.PeriodicTranslations
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnProjections
import GaloisForLFunctions.HTGeometry.RationalDenominatorLadder

/-!
# Cyclic Haar orbits and fixed projections

A rational translation orbit of a dilation column is orthonormal up to its
reduced denominator. Its fixed projection therefore has squared norm equal to
the reciprocal orbit length.
-/

open Module Finset
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

private theorem nat_mul_nonintegral_below_den (q : ℚ) {j : ℕ}
    (hj : 0 < j) (hjd : j < q.den) : ((j : ℚ) * q).den ≠ 1 := by
  intro h
  obtain ⟨z, hz⟩ := (den_eq_one_iff_exists _).mp h
  have hd := (HTGeometry.exists_intCast_natMul_iff_den_dvd hj q).mp ⟨z, hz.symm⟩
  exact (not_le_of_gt hjd) (Nat.le_of_dvd hj hd)

private theorem nat_difference_nonintegral_below_den (q : ℚ) {i j : ℕ}
    (hi : i < q.den) (hj : j < q.den) (hij : i ≠ j) :
    (((j : ℚ) - (i : ℚ)) * q).den ≠ 1 := by
  by_cases hlt : i < j
  · have he : (j : ℚ) - (i : ℚ) = ((j - i : ℕ) : ℚ) := (Nat.cast_sub hlt.le).symm
    rw [he]
    exact nat_mul_nonintegral_below_den q (by omega) (by omega)
  · have hgt : j < i := by omega
    intro h
    obtain ⟨z, hz⟩ := (den_eq_one_iff_exists _).mp h
    have hreverse : (((i : ℚ) - (j : ℚ)) * q).den = 1 := by
      apply (den_eq_one_iff_exists _).mpr
      refine ⟨-z, ?_⟩
      push_cast
      linear_combination -hz
    rw [show (i : ℚ) - (j : ℚ) = ((i - j : ℕ) : ℚ) from (Nat.cast_sub hgt.le).symm]
      at hreverse
    exact nat_mul_nonintegral_below_den q (by omega) (by omega) hreverse

/-- Pairings along a translation orbit read the rescaled translation difference. -/
theorem dilation_column_translation_orbit_pairing {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (a : ℚˣ) (c : ℚ) (i j : ℕ) :
    kernelColumnPairing k
      (((kernelColumnRepresentation k (translation c)) ^ i) (kernelColumnPoint k (dilation a)))
      (((kernelColumnRepresentation k (translation c)) ^ j) (kernelColumnPoint k (dilation a))) =
      k (translation (((j : ℚ) - (i : ℚ)) * (c / (a : ℚ)))) := by
  rw [rational_affine_translation_pow, rational_affine_translation_pow,
    kernelColumnRepresentation_point, kernelColumnRepresentation_point,
    kernelColumnPairing_point_left hk]
  change k ((translation ((i : ℚ) * c) * dilation a)⁻¹ *
    (translation ((j : ℚ) * c) * dilation a)) = _
  rw [tdil_inv_mul_tdil]
  congr 2
  ring

/-- A scaled Haar reading makes a complete cyclic translation orbit orthogonal with constant norm. -/
theorem haar_translation_orbit_pairing {k : AffineGroupQ → ℂ} {z : ℂ}
    (hk : IsHermKernel k)
    (hs : ∀ b : ℚ, k (translation b) = if b.den = 1 then z else 0) (a : ℚˣ) (c : ℚ)
    {i j : ℕ} (hi : i < (c / (a : ℚ)).den) (hj : j < (c / (a : ℚ)).den) :
    kernelColumnPairing k
      (((kernelColumnRepresentation k (translation c)) ^ i) (kernelColumnPoint k (dilation a)))
      (((kernelColumnRepresentation k (translation c)) ^ j) (kernelColumnPoint k (dilation a))) =
      if i = j then z else 0 := by
  rw [dilation_column_translation_orbit_pairing hk, hs]
  by_cases hij : i = j
  · simp only [hij, sub_self, zero_mul, Rat.den_zero, ite_true]
  · rw [if_neg (nat_difference_nonintegral_below_den _ hi hj hij), if_neg hij]

/-- A complete rational translation orbit of a dilation column is orthonormal for the Haar reading. -/
theorem integer_successor_translation_orbit_orthonormal {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k) (a : ℚˣ) (c : ℚ)
    {i j : ℕ} (hi : i < (c / (a : ℚ)).den) (hj : j < (c / (a : ℚ)).den) :
    kernelColumnPairing k
      (((kernelColumnRepresentation k (translation c)) ^ i) (kernelColumnPoint k (dilation a)))
      (((kernelColumnRepresentation k (translation c)) ^ j) (kernelColumnPoint k (dilation a))) =
      if i = j then 1 else 0 :=
  haar_translation_orbit_pairing hk hs a c hi hj

/-- The canonical projection onto the vectors fixed by one rational translation. -/
def translationFixedProjection (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) : End ℂ (kernelColumnSpan k) :=
  locallyPeriodicProjection (kernelColumnRepresentation k (translation b))
    (kernel_translation_locally_periodic hp b)

/-- The squared norm of a cyclic Haar average is the reciprocal of its orbit length. -/
theorem integer_successor_projection_pairing {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (a : ℚˣ) :
    kernelColumnPairing k
      (translationFixedProjection k hp b (kernelColumnPoint k (dilation a)))
      (translationFixedProjection k hp b (kernelColumnPoint k (dilation a))) =
      ((b / (a : ℚ)).den : ℂ)⁻¹ := by
  classical
  let m := (b / (a : ℚ)).den
  let T := kernelColumnRepresentation k (translation b)
  let v := kernelColumnPoint k (dilation a)
  have hm : 0 < m := (b / (a : ℚ)).den_pos
  have hperiod : (T ^ m) v = v := by
    simpa only [affSlope_dilation] using kernel_translation_column_period hp b (dilation a)
  have haverage := kernelColumnPairing_projection_average hk (translation b)
    (kernel_translation_locally_periodic hp b) v v (Nat.ne_of_gt hm) hperiod
  have hterm (j : ℕ) (hj : j ∈ range m) :
      kernelColumnPairing k v ((T ^ j) v) = if j = 0 then 1 else 0 := by
    have h := integer_successor_translation_orbit_orthonormal hk hs a b hm (mem_range.mp hj)
    simpa only [pow_zero, Module.End.one_apply, eq_comm] using h
  have hsum : (∑ j ∈ range m, kernelColumnPairing k v ((T ^ j) v)) = 1 := by
    calc
      (∑ j ∈ range m, kernelColumnPairing k v ((T ^ j) v)) =
          kernelColumnPairing k v ((T ^ 0) v) := by
        apply Finset.sum_eq_single 0
        · intro j hj hj0
          rw [hterm j hj, if_neg hj0]
        · intro h
          exact (h (mem_range.mpr hm)).elim
      _ = 1 := by rw [hterm 0 (mem_range.mpr hm), if_pos rfl]
  rw [hsum, mul_one] at haverage
  exact haverage

theorem integer_successor_projection_pairing_re {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (a : ℚˣ) :
    (kernelColumnPairing k
      (translationFixedProjection k hp b (kernelColumnPoint k (dilation a)))
      (translationFixedProjection k hp b (kernelColumnPoint k (dilation a)))).re =
      ((b / (a : ℚ)).den : ℝ)⁻¹ := by
  rw [integer_successor_projection_pairing hk hs hp]
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
    (Complex.ofReal_re (((b / (a : ℚ)).den : ℝ)⁻¹))

theorem integer_successor_projection_pairing_nonneg {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (a : ℚˣ) :
    0 ≤ (kernelColumnPairing k
      (translationFixedProjection k hp b (kernelColumnPoint k (dilation a)))
      (translationFixedProjection k hp b (kernelColumnPoint k (dilation a)))).re := by
  rw [integer_successor_projection_pairing_re hk hs hp]
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

#print axioms haar_translation_orbit_pairing
#print axioms integer_successor_translation_orbit_orthonormal
#print axioms integer_successor_projection_pairing
#print axioms integer_successor_projection_pairing_nonneg
end GaloisForLFunctions.AdelicKreinGeometry
