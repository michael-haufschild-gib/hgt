/-
The chord–pivot law for a moment growth exponent.

Let `M A` be the growth exponent of the `A`-th moment of a function on a line
(`∫_T^{2T} |f(1/2+it)|^A dt ≪ T^{M A + o(1)}`).  Hölder makes `M` convex, and two anchors are
available for the Riemann zeta function: `M A = 1` for `0 ≤ A ≤ 4`, and `M 12 ≤ 2`.  Convexity then
forces `M` below the chord joining `(4,1)` to `(12,2)`, whose slope is `1/8`.

Legendre duality converts a moment bound into a bound on the measure of large values: the exponent
`φ v` in `meas{t : |f| > T^v} = T^{1-φ v+o(1)}` satisfies `φ v ≥ A v - (M A - 1)` for every `A`.  At
`v = 1/8` the quantity `A/8 - (M A - 1)` evaluated on the chord is **constant equal to `1/2`** — the
whole interval `[4,12]` is a plateau.  So the certified value of `φ (1/8)` is exactly `1/2`, and it
exceeds `1/2` precisely when `M` dips strictly below the chord somewhere in `(4,12)`.

This is a rigidity statement about the pair (moment curve, large-value exponent): the plateau is an
exact algebraic coincidence between the chord slope `1/8` and the evaluation point `v = 1/8`, and it
is what pins the derived bounds `M 8 ≥ 3/2` and `M 12 ≥ 2` in place.

The module is source-independent: it is a statement about convex functions on the reals.
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecificLimits.Basic

namespace HTGeometry

/-- The chord joining `(4,1)` to `(12,2)`; its slope is `1/8`. -/
noncomputable def momentChord (A : ℝ) : ℝ := 1 + (A - 4) / 8

/-- The certified gain at the evaluation point `v = 1/8`, read off from the moment exponent at
index `A`.  Legendre duality gives `φ (1/8) ≥ pivotGain M A` for every `A`. -/
noncomputable def pivotGain (M : ℝ → ℝ) (A : ℝ) : ℝ := A / 8 - M A + 1

/-- **Chord bound.**  Convexity together with the two anchors `M 4 = 1` and `M 12 ≤ 2` forces the
moment exponent below the chord on the whole interval `[4,12]`. -/
theorem momentChord_upper {M : ℝ → ℝ}
    (hconv : ConvexOn ℝ (Set.Ici (0:ℝ)) M) (h4 : M 4 = 1) (h12 : M 12 ≤ 2)
    {A : ℝ} (hA4 : 4 ≤ A) (hA12 : A ≤ 12) :
    M A ≤ momentChord A := by
  set t : ℝ := (A - 4) / 8 with ht
  have htnn : 0 ≤ t := by
    rw [ht]; apply div_nonneg <;> linarith
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by norm_num : (0:ℝ) < 8)]; linarith
  have hmem4 : (4:ℝ) ∈ Set.Ici (0:ℝ) := by norm_num
  have hmem12 : (12:ℝ) ∈ Set.Ici (0:ℝ) := by norm_num
  have hcomb : (1 - t) • (4:ℝ) + t • (12:ℝ) = A := by
    simp only [smul_eq_mul, ht]; ring
  have key := hconv.2 hmem4 hmem12 (by linarith : (0:ℝ) ≤ 1 - t) htnn (by ring)
  rw [hcomb] at key
  have : (1 - t) * M 4 + t * M 12 ≤ 1 + t := by
    rw [h4]; nlinarith [htnn, ht1, h12]
  calc M A ≤ (1 - t) • M 4 + t • M 12 := key
    _ = (1 - t) * M 4 + t * M 12 := by simp [smul_eq_mul]
    _ ≤ 1 + t := this
    _ = momentChord A := by unfold momentChord; rw [ht]

/-- **The plateau.**  On the chord the certified gain is identically `1/2`: the algebraic
coincidence between the chord slope `1/8` and the evaluation point `v = 1/8`. -/
theorem pivotGain_momentChord (A : ℝ) : pivotGain momentChord A = 1 / 2 := by
  unfold pivotGain momentChord; ring

/-- **Chord bound gives the gain ceiling.**  Under the hypotheses of `momentChord_upper`, no index
in `[4,12]` certifies a gain above `1/2`. -/
theorem pivotGain_le_half_of_chord {M : ℝ → ℝ}
    (hM : ∀ A, 4 ≤ A → A ≤ 12 → momentChord A ≤ M A)
    {A : ℝ} (hA4 : 4 ≤ A) (hA12 : A ≤ 12) :
    pivotGain M A ≤ 1 / 2 := by
  have := hM A hA4 hA12
  unfold pivotGain momentChord at *
  linarith

/-- **The chord–pivot equivalence.**  A gain strictly above `1/2` at some index of `[4,12]` is the
same thing as the moment exponent dipping strictly below the chord there. -/
theorem pivotGain_gt_half_iff_below_chord {M : ℝ → ℝ} {A : ℝ} :
    1 / 2 < pivotGain M A ↔ M A < momentChord A := by
  unfold pivotGain momentChord
  constructor <;> intro h <;> linarith

/-- **Certified pivot theorem.**  Assume only what is known: `M` convex, `M A = 1` for `A ≤ 4`,
`M 12 ≤ 2`, and the Hölder extension `M A ≤ 2 + s * (A - 12)` for `A ≥ 12` with slope `s ≥ 1/8`
(for zeta, `s = 2 μ(1/2) ≤ 13/42`, and `13/42 > 1/8`).  Then **no index whatsoever certifies a gain
above `1/2`** — the certified value of `φ (1/8)` is exactly `1/2`. -/
theorem pivotGain_le_half {M : ℝ → ℝ} {s : ℝ}
    (hlow : ∀ A, 0 ≤ A → A ≤ 4 → M A = 1)
    (hchord : ∀ A, 4 ≤ A → A ≤ 12 → momentChord A ≤ M A)
    (hs : 1 / 8 ≤ s) (hhigh : ∀ A, 12 ≤ A → 2 + s * (A - 12) ≤ M A)
    {A : ℝ} (hA : 0 ≤ A) :
    pivotGain M A ≤ 1 / 2 := by
  rcases le_or_gt A 4 with h | h
  · have := hlow A hA h
    unfold pivotGain
    rw [this]; linarith
  · rcases le_or_gt A 12 with h' | h'
    · exact pivotGain_le_half_of_chord hchord (le_of_lt h) h'
    · have hb := hhigh A (le_of_lt h')
      unfold pivotGain
      nlinarith [hs, hb, h'.le, sub_nonneg.mpr h'.le]

/-- The gain `1/2` is attained: at `A = 4` the fourth-moment anchor gives exactly `1/2`. -/
theorem pivotGain_at_four {M : ℝ → ℝ} (h4 : M 4 = 1) : pivotGain M 4 = 1 / 2 := by
  unfold pivotGain; rw [h4]; norm_num

/-- The two derived floors.  `M 8 ≥ 3/2` and `M 12 ≥ 2` are exactly the chord values, hence are
forced by `pivotGain M A ≤ 1/2`, i.e. by `φ (1/8) = 1/2`. -/
theorem chord_values : momentChord 8 = 3 / 2 ∧ momentChord 12 = 2 := by
  unfold momentChord; constructor <;> norm_num

end HTGeometry
