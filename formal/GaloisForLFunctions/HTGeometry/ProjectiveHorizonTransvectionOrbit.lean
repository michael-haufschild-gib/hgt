import GaloisForLFunctions.HTGeometry.ProjectiveHorizonJetFrame

/-!
# The transvection orbit of a jet coordinate

An elementary transvection moves a homogeneous jet coordinate by a single multiple of another jet
coordinate of the same order:

`E_(xj)(c) . X_(k,l) = X_(k,l) - c X_(j,l)` when `k = x`, and fixes it otherwise.

The dependence on the transvection coefficient is affine linear.  This is the seed of the
one-parameter orbit description: the orbit map of a transvection through any jet observable is a
rational function of the coefficient, which is what a density argument needs in order to pass from
constant coefficients to a generic one.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- **Transvection orbit of a jet coordinate.**  A transvection with row `x` and column `j` shifts
the `x`-th jet coordinate by a multiple of the `j`-th and fixes the others. -/
theorem linearJetAction_freeCoordinate_transvection {x j : n} (hx : x ≠ j) (c : K)
    (k : n) (l : ℕ) :
    (transvectionSL x j hx c) • freeCoordinate K (n × ℕ) (k, l) =
      freeCoordinate K (n × ℕ) (k, l) -
        (if k = x then algebraMap K (HomogeneousJetField n K) c *
          freeCoordinate K (n × ℕ) (j, l) else 0) := by
  rw [linearJetAction_freeCoordinate, transvectionSL_inv]
  have hentry : ∀ m : n, ((transvectionSL x j hx (-c) : SpecialLinearGroup n K) :
      Matrix n n K) k m =
      (1 : Matrix n n K) k m + (if k = x then (if j = m then -c else 0) else 0) := by
    intro m
    show Matrix.transvection x j (-c) k m = _
    by_cases hkx : k = x
    · rw [hkx, transvection_row_self]
      by_cases hjm : j = m <;> simp [hjm]
    · rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply,
        if_neg (fun h => hkx h.1.symm), add_zero]
      simp [hkx]
  rw [Finset.sum_congr rfl fun m _ => by rw [hentry m, map_add, add_mul],
    Finset.sum_add_distrib]
  have hfirst : ∑ m : n, algebraMap K (HomogeneousJetField n K) ((1 : Matrix n n K) k m) *
      freeCoordinate K (n × ℕ) (m, l) = freeCoordinate K (n × ℕ) (k, l) := by
    rw [Finset.sum_eq_single k]
    · rw [Matrix.one_apply_eq, map_one, one_mul]
    · intro m _ hm
      rw [Matrix.one_apply_ne (Ne.symm hm), map_zero, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ k) hcon
  rw [hfirst]
  by_cases hkx : k = x
  · have hsecond : ∑ m : n, algebraMap K (HomogeneousJetField n K)
        (if k = x then (if j = m then -c else 0) else 0) *
          freeCoordinate K (n × ℕ) (m, l) =
        -(algebraMap K (HomogeneousJetField n K) c * freeCoordinate K (n × ℕ) (j, l)) := by
      rw [Finset.sum_eq_single j]
      · rw [if_pos hkx, if_pos rfl, map_neg, neg_mul]
      · intro m _ hm
        rw [if_pos hkx, if_neg (Ne.symm hm), map_zero, zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ j) hcon
    rw [hsecond, if_pos hkx, ← sub_eq_add_neg]
  · have hsecond : ∑ m : n, algebraMap K (HomogeneousJetField n K)
        (if k = x then (if j = m then -c else 0) else 0) *
          freeCoordinate K (n × ℕ) (m, l) = 0 := by
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [if_neg hkx, map_zero, zero_mul]
    rw [hsecond, if_neg hkx, add_zero, sub_zero]

/-- A transvection fixes every jet coordinate outside its row. -/
theorem linearJetAction_freeCoordinate_transvection_of_ne {x j : n} (hx : x ≠ j) (c : K)
    {k : n} (hk : k ≠ x) (l : ℕ) :
    (transvectionSL x j hx c) • freeCoordinate K (n × ℕ) (k, l) =
      freeCoordinate K (n × ℕ) (k, l) := by
  rw [linearJetAction_freeCoordinate_transvection hx c k l, if_neg hk, sub_zero]

/-- On its own row a transvection acts by an affine-linear shift in the coefficient. -/
theorem linearJetAction_freeCoordinate_transvection_self {x j : n} (hx : x ≠ j) (c : K)
    (l : ℕ) :
    (transvectionSL x j hx c) • freeCoordinate K (n × ℕ) (x, l) =
      freeCoordinate K (n × ℕ) (x, l) -
        algebraMap K (HomogeneousJetField n K) c * freeCoordinate K (n × ℕ) (j, l) := by
  rw [linearJetAction_freeCoordinate_transvection hx c x l, if_pos rfl]

/-- The transvection coefficients compose additively on jet coordinates, so a transvection orbit is
a one-parameter additive family. -/
theorem transvectionSL_mul_same {x j : n} (hx : x ≠ j) (c d : K) :
    transvectionSL x j hx c * transvectionSL x j hx d = transvectionSL x j hx (c + d) := by
  apply Subtype.ext
  show Matrix.transvection x j c * Matrix.transvection x j d = Matrix.transvection x j (c + d)
  exact Matrix.transvection_mul_transvection_same _ _ hx c d

end

end GaloisForLFunctions.HTGeometry
