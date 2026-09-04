import GaloisForLFunctions.HTGeometry.StrelitzMaximumNorm

/-!
# Canonical slope of the logarithmic maximum modulus

For a real convex function, the infimum of all right secants is a choice-free version of its
right derivative.  It is finite, lies between every left and right secant, is monotone, and agrees
with the ordinary derivative wherever that derivative exists.

Applied to the logarithmic maximum modulus, this supplies the exact scalar slope used in the
Strelitz enlarged-set argument.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Set

noncomputable section

/-- Choice-free right slope of a convex real function: the infimum of all strict right secants. -/
def convexRightSlope (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  sInf (Set.range fun y : Set.Ioi x => slope f x y.1)

/-- Right secants of a globally convex real function have a finite common lower bound. -/
theorem bddBelow_range_slope_Ioi_of_convexOn {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (x : ℝ) :
    BddBelow (Set.range fun y : Set.Ioi x => slope f x y.1) := by
  refine ⟨slope f (x - 1) x, ?_⟩
  rintro q ⟨y, rfl⟩
  simpa [slope, div_eq_mul_inv, mul_comm] using
    (convexOn_iff_slope_mono_adjacent.mp hf).2
      (x := x - 1) (y := x) (z := y.1)
      (by simp) (by simp) (by linarith) y.property

/-- The canonical right slope is at most every strict right secant. -/
theorem convexRightSlope_le_slope {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {x y : ℝ} (hxy : x < y) :
    convexRightSlope f x ≤ slope f x y := by
  apply csInf_le (bddBelow_range_slope_Ioi_of_convexOn hf x)
  exact ⟨⟨y, hxy⟩, rfl⟩

/-- Every strict left secant is at most the canonical right slope. -/
theorem slope_le_convexRightSlope {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {y x : ℝ} (hyx : y < x) :
    slope f x y ≤ convexRightSlope f x := by
  apply le_csInf (Set.range_nonempty _)
  rintro q ⟨z, rfl⟩
  rw [slope_comm f x y]
  simpa [slope, div_eq_mul_inv, mul_comm] using
    (convexOn_iff_slope_mono_adjacent.mp hf).2
      (x := y) (y := x) (z := z.1)
      (by simp) (by simp) hyx z.property

/-- Canonical right slopes of a globally convex function are monotone. -/
theorem monotone_convexRightSlope {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) : Monotone (convexRightSlope f) := by
  intro x y hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  · calc
      convexRightSlope f x ≤ slope f x y := convexRightSlope_le_slope hf hxy
      _ = slope f y x := slope_comm f x y
      _ ≤ convexRightSlope f y :=
        slope_le_convexRightSlope hf (y := x) (x := y) hxy

/-- At a differentiability point, the canonical right slope is the ordinary derivative. -/
theorem convexRightSlope_eq_of_hasDerivAt {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {x d : ℝ} (hd : HasDerivAt f d x) :
    convexRightSlope f x = d := by
  have hright : Tendsto (slope f x) (nhdsWithin x (Set.Ioi x)) (nhds d) :=
    hd.tendsto_slope.mono_left (nhdsWithin_mono x (by
      intro y hy hEq
      exact hy.ne hEq.symm))
  have hleft : Tendsto (slope f x) (nhdsWithin x (Set.Iio x)) (nhds d) :=
    hd.tendsto_slope.mono_left (nhdsWithin_mono x (by
      intro y hy hEq
      exact hy.ne hEq))
  apply le_antisymm
  · apply ge_of_tendsto hright
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact convexRightSlope_le_slope hf hy
  · apply le_of_tendsto hleft
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact slope_le_convexRightSlope hf hy

/-- Canonical logarithmic-radius slope of the exact circle maximum norm. -/
def strelitzMaximumSlope (a : ℕ → ℂ) (x : ℝ) : ℝ :=
  convexRightSlope (strelitzLogMaximum a) x

/-- The exact maximum slope is at most every later logarithmic secant. -/
theorem strelitzMaximumSlope_le_slope
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {x y : ℝ} (hxy : x < y) :
    strelitzMaximumSlope a x ≤ slope (strelitzLogMaximum a) x y := by
  exact convexRightSlope_le_slope (convexOn_strelitzLogMaximum ha hn₀) hxy

/-- Every earlier logarithmic secant is at most the exact maximum slope. -/
theorem slope_le_strelitzMaximumSlope
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {y x : ℝ} (hyx : y < x) :
    slope (strelitzLogMaximum a) x y ≤ strelitzMaximumSlope a x := by
  exact slope_le_convexRightSlope (convexOn_strelitzLogMaximum ha hn₀) hyx

/-- The exact logarithmic maximum slope is monotone. -/
theorem monotone_strelitzMaximumSlope
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    Monotone (strelitzMaximumSlope a) := by
  exact monotone_convexRightSlope (convexOn_strelitzLogMaximum ha hn₀)

end

end GaloisForLFunctions.HTGeometry
