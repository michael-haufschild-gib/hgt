import GaloisForLFunctions.HTGeometry.PairTopDegree

/-!
# The class of starting vectors the peel preserves

Dividing the peeled vector by the newest denominator leaves a factor on its leading term, and the
shifted operator sees that factor, so a degree profile is not preserved.  What is preserved is the
exact leading term: the newest entry agrees with the border entry up to degree `−2`.

On that class the newest column behaves exactly as it does for the border row itself: the scalar
operator already sends the border entry two degrees down, so every entry below the border has degree
`−2`, and the scaled column's value at infinity is `(1 + deg g, 0, …, 0)`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ} {α β : Polynomial ℂ} {m' : ℕ}

/-- The starting vectors the peel preserves: the newest entry is the border entry up to degree
`−2`. -/
def PairBorderShape (p : ℕ → MvPolynomial (Fin 2) ℂ) (g : Polynomial ℂ) (m : ℕ)
    (u : ℕ → CascadeField) : Prop :=
  TopDegLE m (-2) (u m - headBorder p g m m)

theorem pairBorderShape_headBorder (p : ℕ → MvPolynomial (Fin 2) ℂ) (g : Polynomial ℂ) (m : ℕ) :
    PairBorderShape p g m (headBorder p g m) := by
  rw [PairBorderShape, sub_self]
  exact topDegLE_zero m (-2)

/-! ## The column below the border -/

theorem topDegLE_pairTopShift_of_shape (hα : α ≠ 0) {g : Polynomial ℂ} (hg : g ≠ 0)
    (hp : p m' = affinePair α β) {u : ℕ → CascadeField}
    (hshape : PairBorderShape p g (m' + 1) u)
    (hmem : u (m' + 1) ∈ coordField (m' + 1)) :
    TopDegLE (m' + 1) (-2) (pairTopShift p (m' + 1) (u (m' + 1))) := by
  have hsplit : u (m' + 1)
      = headBorder p g (m' + 1) (m' + 1)
        + (u (m' + 1) - headBorder p g (m' + 1) (m' + 1)) := by ring
  rw [hsplit, pairTopShift_add]
  refine TopDegLE.add (topDegLE_pairTopShift_headBorder hα hg hp) ?_
  exact pairTopShift_topDegLE hp
    (sub_mem hmem (headBorder_mem_coordField g (m' + 1) (m' + 1))) hshape

/-- **Every entry below the border has degree `−2`.** -/
theorem topDegLE_iterate_of_shape (hα : α ≠ 0) {g : Polynomial ℂ} (hg : g ≠ 0)
    (hp : p m' = affinePair α β) {u : ℕ → CascadeField}
    (hshape : PairBorderShape p g (m' + 1) u)
    (hmem : u (m' + 1) ∈ coordField (m' + 1)) (r : ℕ) :
    TopDegLE (m' + 1) (-2)
      (((pairTopShift p (m' + 1))^[r]) (pairTopShift p (m' + 1) (u (m' + 1)))) := by
  have hbase : TopDegLE (m' + 1) (-2) (pairTopShift p (m' + 1) (u (m' + 1))) :=
    topDegLE_pairTopShift_of_shape hα hg hp hshape hmem
  induction r with
  | zero => simpa using hbase
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      refine pairTopShift_topDegLE hp ?_ ih
      exact iterate_pairTopShift_mem_coordField (pairTopShift_mem_coordField hmem) r

/-! ## The residue at the border -/

/-- **The border entry of a shaped vector has the same residue.** -/
theorem topLim_fx_mul_of_shape (hα : α ≠ 0) (g : Polynomial ℂ) (hp : p m' = affinePair α β)
    {u : ℕ → CascadeField} (hshape : PairBorderShape p g (m' + 1) u) :
    TopLim (m' + 1) (fx (m' + 1) * u (m' + 1))
      (algebraMap ℂ CascadeField (1 + (g.natDegree : ℂ))) := by
  have hsplit : fx (m' + 1) * u (m' + 1)
      = fx (m' + 1) * headBorder p g (m' + 1) (m' + 1)
        + fx (m' + 1) * (u (m' + 1) - headBorder p g (m' + 1) (m' + 1)) := by ring
  rw [hsplit]
  have h2 : TopLim (m' + 1)
      (fx (m' + 1) * (u (m' + 1) - headBorder p g (m' + 1) (m' + 1))) 0 := by
    rw [TopLim, sub_zero]
    have h := TopDegLE.mul (topDegLE_fx (m' + 1)) hshape
    simpa using h
  have hsum := TopLim.add (topLim_fx_mul_headBorder hα g hp) h2
  rw [add_zero] at hsum
  exact hsum

/-- **The scaled newest column of a shaped vector vanishes below the border.** -/
theorem topLim_fx_mul_iterate_of_shape (hα : α ≠ 0) {g : Polynomial ℂ} (hg : g ≠ 0)
    (hp : p m' = affinePair α β) {u : ℕ → CascadeField}
    (hshape : PairBorderShape p g (m' + 1) u)
    (hmem : u (m' + 1) ∈ coordField (m' + 1)) (r : ℕ) :
    TopLim (m' + 1)
      (fx (m' + 1) * (((pairGradShift p (m' + 1))^[r + 1]) u (m' + 1))) 0 := by
  rw [TopLim, sub_zero, iterate_pairGradShift_top, Function.iterate_succ_apply]
  have h := TopDegLE.mul (topDegLE_fx (m' + 1))
    (topDegLE_iterate_of_shape hα hg hp hshape hmem r)
  simpa using h

/-! ## The base case -/

/-- **A shaped newest entry is nonzero**: its scaled value at infinity is `1 + deg g`. -/
theorem ne_zero_of_pairBorderShape (hα : α ≠ 0) (g : Polynomial ℂ)
    (hp : p m' = affinePair α β) {u : ℕ → CascadeField}
    (hshape : PairBorderShape p g (m' + 1) u) : u (m' + 1) ≠ 0 := by
  intro hzero
  have hlim := topLim_fx_mul_of_shape hα g hp hshape
  rw [hzero, mul_zero] at hlim
  have hne : (algebraMap ℂ CascadeField (1 + (g.natDegree : ℂ))) ≠ 0 := by
    refine (map_ne_zero_iff _ (algebraMap ℂ CascadeField).injective).mpr ?_
    have : ((g.natDegree : ℂ)).re = (g.natDegree : ℝ) := by simp
    intro hc
    have hre : (1 : ℝ) + (g.natDegree : ℝ) = 0 := by
      have := congrArg Complex.re hc
      simpa using this
    have : (0 : ℝ) ≤ (g.natDegree : ℝ) := Nat.cast_nonneg _
    linarith
  exact hne (topLim_unique (topFree_algebraMap_complex (m' + 1) _) (topFree_zero (m' + 1))
    hlim topLim_const)

end GaloisForLFunctions.HTGeometry
