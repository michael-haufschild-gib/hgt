import GaloisForLFunctions.HTGeometry.AffineBorderEntry

/-!
# The class of starting vectors the affine peel preserves

The newest entry agrees with the border entry up to degree `−2`.  On that class the newest column
behaves exactly as it does for the border row itself: the scalar operator already sends the border
entry two degrees down, so every entry below the border has degree `−2`, and the scaled column's
value at infinity is `(1 + deg g₁ − deg g₂, 0, …, 0)`.

For a polynomial head that residue is a positive integer.  For a rational one it is an integer of
either sign, and the base case of the peel needs it nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

namespace AffineFam

variable (E : AffineFam)

/-- The starting vectors the peel preserves. -/
def BorderShape (g₁ g₂ : Polynomial ℂ) (m : ℕ) (u : ℕ → CascadeField) : Prop :=
  TopDegLE m (-2) (u m - E.toPairFam.headBorder (ratFact g₁ g₂ m) m m)

theorem borderShape_headBorder (g₁ g₂ : Polynomial ℂ) (m : ℕ) :
    E.BorderShape g₁ g₂ m (E.toPairFam.headBorder (ratFact g₁ g₂ m) m) := by
  rw [BorderShape, sub_self]
  exact topDegLE_zero m (-2)

/-! ## The column below the border -/

theorem topDegLE_topShift_of_shape {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {n : ℕ} {u : ℕ → CascadeField} (hshape : E.BorderShape g₁ g₂ (n + 1) u)
    (hmem : u (n + 1) ∈ coordField (n + 1)) :
    TopDegLE (n + 1) (-2) (E.toPairFam.topShift (n + 1) (u (n + 1))) := by
  have hsplit : u (n + 1)
      = E.toPairFam.headBorder (ratFact g₁ g₂ (n + 1)) (n + 1) (n + 1)
        + (u (n + 1) - E.toPairFam.headBorder (ratFact g₁ g₂ (n + 1)) (n + 1) (n + 1)) := by
    ring
  rw [hsplit, E.toPairFam.topShift_add]
  refine TopDegLE.add (E.topDegLE_topShift_headBorder hg₁ hg₂ n) ?_
  refine E.topShift_topDegLE ?_ hshape
  exact sub_mem hmem
    (E.toPairFam.headBorder_mem_coordField
      (ratFact_mem_coordField (le_refl (n + 1)) g₁ g₂) (n + 1))

/-- **Every entry below the border has degree `−2`.** -/
theorem topDegLE_iterate_of_shape {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {n : ℕ} {u : ℕ → CascadeField} (hshape : E.BorderShape g₁ g₂ (n + 1) u)
    (hmem : u (n + 1) ∈ coordField (n + 1)) (r : ℕ) :
    TopDegLE (n + 1) (-2)
      (((E.toPairFam.topShift (n + 1))^[r])
        (E.toPairFam.topShift (n + 1) (u (n + 1)))) := by
  have hbase : TopDegLE (n + 1) (-2) (E.toPairFam.topShift (n + 1) (u (n + 1))) :=
    E.topDegLE_topShift_of_shape hg₁ hg₂ hshape hmem
  induction r with
  | zero => simpa using hbase
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      refine E.topShift_topDegLE ?_ ih
      exact E.iterate_topShift_mem_coordField (E.topShift_mem_coordField hmem) r

/-! ## The residue at the border -/

theorem topLim_fx_mul_of_shape {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {n : ℕ} {u : ℕ → CascadeField} (hshape : E.BorderShape g₁ g₂ (n + 1) u) :
    TopLim (n + 1) (fx (n + 1) * u (n + 1))
      (algebraMap ℂ CascadeField (1 + (g₁.natDegree : ℂ) - (g₂.natDegree : ℂ))) := by
  have hsplit : fx (n + 1) * u (n + 1)
      = fx (n + 1) * E.toPairFam.headBorder (ratFact g₁ g₂ (n + 1)) (n + 1) (n + 1)
        + fx (n + 1)
          * (u (n + 1) - E.toPairFam.headBorder (ratFact g₁ g₂ (n + 1)) (n + 1) (n + 1)) := by
    ring
  rw [hsplit]
  have h2 : TopLim (n + 1) (fx (n + 1)
      * (u (n + 1) - E.toPairFam.headBorder (ratFact g₁ g₂ (n + 1)) (n + 1) (n + 1))) 0 := by
    rw [TopLim, sub_zero]
    have h := TopDegLE.mul (topDegLE_fx (n + 1)) hshape
    simpa using h
  have hsum := TopLim.add (E.topLim_fx_mul_headBorder hg₁ hg₂ n) h2
  rw [add_zero] at hsum
  exact hsum

/-- **The scaled newest column of a shaped vector vanishes below the border.** -/
theorem topLim_fx_mul_iterate_of_shape {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {n : ℕ} {u : ℕ → CascadeField} (hshape : E.BorderShape g₁ g₂ (n + 1) u)
    (hmem : u (n + 1) ∈ coordField (n + 1)) (r : ℕ) :
    TopLim (n + 1)
      (fx (n + 1) * (((E.toPairFam.gradShift (n + 1))^[r + 1]) u (n + 1))) 0 := by
  rw [TopLim, sub_zero, E.toPairFam.iterate_gradShift_top, Function.iterate_succ_apply]
  have h := TopDegLE.mul (topDegLE_fx (n + 1))
    (E.topDegLE_iterate_of_shape hg₁ hg₂ hshape hmem r)
  simpa using h

/-! ## The base case -/

/-- The residue of a rational head is nonzero exactly when the degrees do not differ by `−1`. -/
theorem residue_ne_zero {g₁ g₂ : Polynomial ℂ}
    (hres : ((g₁.natDegree : ℤ) - (g₂.natDegree : ℤ)) ≠ -1) :
    (1 + (g₁.natDegree : ℂ) - (g₂.natDegree : ℂ)) ≠ 0 := by
  have hcast : (1 + (g₁.natDegree : ℂ) - (g₂.natDegree : ℂ))
      = ((1 + (g₁.natDegree : ℤ) - (g₂.natDegree : ℤ) : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Int.cast_ne_zero]
  omega

/-- **A shaped newest entry is nonzero.** -/
theorem ne_zero_of_borderShape {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hres : ((g₁.natDegree : ℤ) - (g₂.natDegree : ℤ)) ≠ -1)
    {n : ℕ} {u : ℕ → CascadeField} (hshape : E.BorderShape g₁ g₂ (n + 1) u) :
    u (n + 1) ≠ 0 := by
  intro hzero
  have hlim := E.topLim_fx_mul_of_shape hg₁ hg₂ hshape
  rw [hzero, mul_zero] at hlim
  have hne : (algebraMap ℂ CascadeField (1 + (g₁.natDegree : ℂ) - (g₂.natDegree : ℂ))) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℂ CascadeField).injective).mpr (residue_ne_zero hres)
  exact hne (topLim_unique (topFree_algebraMap_complex (n + 1) _) (topFree_zero (n + 1))
    hlim topLim_const)

end AffineFam

end GaloisForLFunctions.HTGeometry
