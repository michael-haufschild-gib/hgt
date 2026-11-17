import GaloisForLFunctions.HilbertMetric.Optimization.SimplexBregmanBarycenter

/-!
# The three-state simplex has unbounded four-point defect

The four-point obstruction used in arXiv:2610.36124 applies directly to
the corpus's positive simplex laws. Their Hilbert cross-ratio distance
is exactly the variation norm of the parameter difference. Explicit
squares have defect proportional to their scale. The exact log-ratio
model also identifies the sole degeneracy: common additive shifts.
-/

namespace GaloisForLFunctions.HilbertMetric.Geometry.SimplexFourPoint
open Optimization
noncomputable section

/-- Variation of a three-coordinate vector, measured by its pairwise differences. -/
def variation (x : Fin 3 → ℝ) : ℝ :=
  max |x 0 - x 1| (max |x 0 - x 2| |x 1 - x 2|)

/-- Hilbert distance in the natural-parameter chart. -/
def simplexDistance (c d : Fin 3 → ℝ) : ℝ := variation (fun i => c i - d i)

/-- Cross-ratio coordinates of the actual normalized probability laws. -/
def logRatioDifference (c d : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  Real.log (simplexSampling c i / simplexSampling c j) -
    Real.log (simplexSampling d i / simplexSampling d j)

/-- Normalization cancels exactly, retaining all three probability coordinates. -/
theorem logRatioDifference_eq (c d : Fin 3 → ℝ) (i j : Fin 3) :
    logRatioDifference c d i j = -(c i - d i - (c j - d j)) := by
  rw [logRatioDifference, simplexSampling_ratio, simplexSampling_ratio,
    Real.log_exp, Real.log_exp]
  ring

/-- The parameter metric is literally the Hilbert cross-ratio metric of the output laws. -/
theorem simplexDistance_cross_ratios (c d : Fin 3 → ℝ) :
    simplexDistance c d = max |logRatioDifference c d 0 1|
      (max |logRatioDifference c d 0 2| |logRatioDifference c d 1 2|) := by
  simp only [logRatioDifference_eq, abs_neg, simplexDistance, variation]

theorem simplexDistance_nonneg (c d : Fin 3 → ℝ) : 0 ≤ simplexDistance c d :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem simplexDistance_comm (c d : Fin 3 → ℝ) : simplexDistance c d = simplexDistance d c := by
  have h (i j : Fin 3) : c i - d i - (c j - d j) = -(d i - c i - (d j - c j)) := by ring
  simp only [simplexDistance, variation, h, abs_neg]

/-- The triangle inequality holds before quotienting out the additive gauge. -/
theorem simplexDistance_triangle (c d e : Fin 3 → ℝ) :
    simplexDistance c e ≤ simplexDistance c d + simplexDistance d e := by
  have h (i j : Fin 3) :
      |c i - e i - (c j - e j)| ≤
        |c i - d i - (c j - d j)| + |d i - e i - (d j - e j)| := by
    have he : c i - e i - (c j - e j) =
        (c i - d i - (c j - d j)) + (d i - e i - (d j - e j)) := by ring
    rw [he]
    exact abs_add_le _ _
  unfold simplexDistance variation
  apply max_le
  · exact (h 0 1).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · apply max_le
    · exact (h 0 2).trans (add_le_add
        ((le_max_left _ _).trans (le_max_right _ _))
        ((le_max_left _ _).trans (le_max_right _ _)))
    · exact (h 1 2).trans (add_le_add
        ((le_max_right _ _).trans (le_max_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _)))

/-- Zero Hilbert distance identifies exactly the same normalized probability law. -/
theorem simplexDistance_zero_iff (c d : Fin 3 → ℝ) :
    simplexDistance c d = 0 ↔ simplexSampling c = simplexSampling d := by
  rw [← simplexLogChart_eq_iff]
  constructor
  · intro h
    have h01 : |c 0 - d 0 - (c 1 - d 1)| ≤ 0 := by
      have hb : |c 0 - d 0 - (c 1 - d 1)| ≤ simplexDistance c d := le_max_left _ _
      rwa [h] at hb
    have h02 : |c 0 - d 0 - (c 2 - d 2)| ≤ 0 := by
      have hb : |c 0 - d 0 - (c 2 - d 2)| ≤ simplexDistance c d :=
        (le_max_left _ _).trans (le_max_right _ _)
      rwa [h] at hb
    have e01 := abs_eq_zero.mp (le_antisymm h01 (abs_nonneg _))
    have e02 := abs_eq_zero.mp (le_antisymm h02 (abs_nonneg _))
    funext i
    simp only [simplexLogChart_eq]
    fin_cases i
    · change c 0 - c 0 = d 0 - d 0
      ring
    · change c 0 - c 1 = d 0 - d 1
      linarith only [e01]
    · change c 0 - c 2 = d 0 - d 2
      linarith only [e02]
  · intro h
    have he (i : Fin 3) : c 0 - c i = d 0 - d i := by
      simpa only [simplexLogChart_eq] using congrFun h i
    have h01 : c 0 - d 0 - (c 1 - d 1) = 0 := by linarith only [he 1]
    have h02 : c 0 - d 0 - (c 2 - d 2) = 0 := by linarith only [he 2]
    have h12 : c 1 - d 1 - (c 2 - d 2) = 0 := by linarith only [he 1, he 2]
    simp only [simplexDistance, variation, h01, h02, h12, abs_zero, max_self]

/-- The only metric degeneracy is addition of one common scalar to every parameter. -/
theorem simplexDistance_zero_iff_shift (c d : Fin 3 → ℝ) :
    simplexDistance c d = 0 ↔ ∃ b : ℝ, ∀ i, c i = d i + b := by
  rw [simplexDistance_zero_iff, ← simplexLogChart_eq_iff]
  constructor
  · intro h
    refine ⟨c 0 - d 0, ?_⟩
    intro i
    have hi := congrFun h i
    simp only [simplexLogChart_eq] at hi
    linarith only [hi]
  · rintro ⟨b, hb⟩
    funext i
    simp only [simplexLogChart_eq, hb]
    ring

/-- Four explicit parameter vectors form squares of arbitrarily large metric defect. -/
def squarePoint (a : ℝ) (k : Fin 4) : Fin 3 → ℝ :=
  ![![0, 0, 0], ![a, 0, 0], ![0, a, 0], ![a, a, 0]] k

/-- The two crossed-pair sums differ from either other pairing by exactly the scale. -/
theorem square_four_point_defect (a : ℝ) :
    simplexDistance (squarePoint a 0) (squarePoint a 3) +
        simplexDistance (squarePoint a 1) (squarePoint a 2) -
      max (simplexDistance (squarePoint a 0) (squarePoint a 1) +
        simplexDistance (squarePoint a 3) (squarePoint a 2))
        (simplexDistance (squarePoint a 0) (squarePoint a 2) +
          simplexDistance (squarePoint a 3) (squarePoint a 1)) = |a| := by
  have htwo : |a + a| = 2 * |a| := by rw [← two_mul, abs_mul]; norm_num
  have hle : |a| ≤ 2 * |a| := by linarith only [abs_nonneg a]
  simp [simplexDistance, variation, squarePoint, abs_neg, max_self, htwo, max_eq_left hle]
  ring

/-- No uniform Gromov four-point constant exists for the positive three-state simplex. -/
theorem no_uniform_four_point_constant :
    ¬ ∃ δ : ℝ, ∀ c d e f : Fin 3 → ℝ,
      simplexDistance c e + simplexDistance d f ≤
        max (simplexDistance c d + simplexDistance e f)
          (simplexDistance c f + simplexDistance e d) + 2 * δ := by
  rintro ⟨δ, hδ⟩
  let a := 2 * |δ| + 1
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h := hδ (squarePoint a 0) (squarePoint a 1) (squarePoint a 3) (squarePoint a 2)
  have he := square_four_point_defect a
  rw [abs_of_nonneg ha] at he
  have hd := le_abs_self δ
  dsimp [a] at he
  linarith only [h, he, hd]

#print axioms simplexDistance_cross_ratios
#print axioms simplexDistance_triangle
#print axioms simplexDistance_zero_iff
#print axioms simplexDistance_zero_iff_shift
#print axioms square_four_point_defect
#print axioms no_uniform_four_point_constant
end
end GaloisForLFunctions.HilbertMetric.Geometry.SimplexFourPoint
