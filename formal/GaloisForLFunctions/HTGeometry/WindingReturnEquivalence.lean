import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-!
# Continuous recurrence and integer winding are the same approximation problem

Anchor a finite spectrum at its lowest level and record the gap phases in turns,
`t g_j/(2π)`.  A *continuous `r`-return* asks every one of them to be within `r` of an integer; a
*winding `r`-return* asks a single integer `q` to put every projective ratio `g_j/g_0` within `r` of
the integer lattice.

The two are equivalent up to the fixed factor `1 + A`, where `A` bounds the ratios.  One direction
is exact: evaluating at the time `2π q/g_0` turns a winding return into a continuous return with the
same radius, because the anchored phase at that time *is* the ratio times `q`.  The other direction
reads the winding number off the anchor phase and pays `A` times the anchor error on each
coordinate.

Since the loss is a fixed multiplicative constant on the radius and a bounded distortion between the
time `t` and the winding `q`, the two first-hit functions have the same logarithmic exponent -- the
continuous problem in `d+1` phases is the winding problem in `d` ratios, one dimension fewer,
because time itself supplies one winding direction.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Winding

variable {d : ℕ}

/-- The anchored gap phase at time `t`, measured in turns. -/
def gapTurn (g : Fin (d + 1) → ℝ) (t : ℝ) (j : Fin (d + 1)) : ℝ := t * g j / (2 * π)

/-- The projective ratio coordinates, anchored at the first gap. -/
def gapRatio (g : Fin (d + 1) → ℝ) (j : Fin (d + 1)) : ℝ := g j / g 0

/-- Every anchored gap phase is within `r` of a whole number of turns. -/
def ContinuousReturn (g : Fin (d + 1) → ℝ) (r t : ℝ) : Prop :=
  ∀ j, latticeClose (gapTurn g t j) r

/-- A single integer winding puts every projective ratio within `r` of the integer lattice. -/
def WindingReturn (g : Fin (d + 1) → ℝ) (r : ℝ) (q : ℤ) : Prop :=
  ∀ j, latticeClose ((q : ℝ) * gapRatio g j) r

theorem gapRatio_zero (g : Fin (d + 1) → ℝ) (hg0 : g 0 ≠ 0) : gapRatio g 0 = 1 := by
  rw [gapRatio, div_self hg0]

/-- The anchor phase scales the ratios to the other phases. -/
theorem gapTurn_zero_mul_gapRatio (g : Fin (d + 1) → ℝ) (hg0 : g 0 ≠ 0) (t : ℝ)
    (j : Fin (d + 1)) : gapTurn g t 0 * gapRatio g j = gapTurn g t j := by
  rw [gapTurn, gapTurn, gapRatio]
  field_simp

/-- **The winding direction is exact.**  Evaluating at the time `2π q/g_0` turns a winding return
into a continuous return of the same radius. -/
theorem continuousReturn_of_windingReturn (g : Fin (d + 1) → ℝ) (hg0 : g 0 ≠ 0) {r : ℝ} {q : ℤ}
    (h : WindingReturn g r q) : ContinuousReturn g r (2 * π * (q : ℝ) / g 0) := by
  intro j
  have hpi : (2 : ℝ) * π ≠ 0 := by
    have := Real.pi_ne_zero
    positivity
  have heq : gapTurn g (2 * π * (q : ℝ) / g 0) j = (q : ℝ) * gapRatio g j := by
    rw [gapTurn, gapRatio]
    field_simp
  rw [heq]
  exact h j

/-- **The continuous direction costs the ratio bound.**  A continuous `r`-return supplies a winding
`r(1+A)`-return, with `q` read off the anchor phase. -/
theorem exists_windingReturn_of_continuousReturn (g : Fin (d + 1) → ℝ) (hg0 : g 0 ≠ 0)
    {r A t : ℝ} (hA : ∀ j, |gapRatio g j| ≤ A) (h : ContinuousReturn g r t) :
    ∃ q : ℤ, |gapTurn g t 0 - (q : ℝ)| < r ∧ WindingReturn g (r * (1 + A)) q := by
  obtain ⟨q, hq⟩ := h 0
  have hAnn : 0 ≤ A := le_trans (abs_nonneg _) (hA 0)
  have hrpos : 0 ≤ r := le_of_lt (lt_of_le_of_lt (abs_nonneg _) hq)
  refine ⟨q, hq, fun j => ?_⟩
  obtain ⟨p, hp⟩ := h j
  refine ⟨p, ?_⟩
  have hkey : (q : ℝ) * gapRatio g j - (p : ℝ)
      = -((gapTurn g t 0 - (q : ℝ)) * gapRatio g j) + (gapTurn g t j - (p : ℝ)) := by
    have := gapTurn_zero_mul_gapRatio g hg0 t j
    linarith [this]
  have hbound : |(gapTurn g t 0 - (q : ℝ)) * gapRatio g j| ≤ r * A := by
    rw [abs_mul]
    exact mul_le_mul (le_of_lt hq) (hA j) (abs_nonneg _) hrpos
  calc |(q : ℝ) * gapRatio g j - (p : ℝ)|
      = |-((gapTurn g t 0 - (q : ℝ)) * gapRatio g j) + (gapTurn g t j - (p : ℝ))| := by rw [hkey]
    _ ≤ |(gapTurn g t 0 - (q : ℝ)) * gapRatio g j| + |gapTurn g t j - (p : ℝ)| := by
        rw [← abs_neg ((gapTurn g t 0 - (q : ℝ)) * gapRatio g j)] at *
        exact abs_add_le _ _
    _ < r * A + r := by linarith [hp, hbound]
    _ = r * (1 + A) := by ring

/-- The winding number read off a continuous return is bounded by the elapsed time. -/
theorem abs_winding_le_of_continuousReturn (g : Fin (d + 1) → ℝ) {r t : ℝ} {q : ℤ}
    (hq : |gapTurn g t 0 - (q : ℝ)| < r) :
    |(q : ℝ)| ≤ |t| * |g 0| / (2 * π) + r := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hturn : |gapTurn g t 0| = |t| * |g 0| / (2 * π) := by
    rw [gapTurn, abs_div, abs_mul, abs_of_pos hpi]
  have := abs_sub_abs_le_abs_sub (gapTurn g t 0) (q : ℝ)
  rw [hturn] at this
  have habs : |(q : ℝ)| - |t| * |g 0| / (2 * π) ≤ |gapTurn g t 0 - (q : ℝ)| := by
    have h2 := abs_sub_abs_le_abs_sub ((q : ℝ)) (gapTurn g t 0)
    rw [abs_sub_comm ((q : ℝ)) (gapTurn g t 0), hturn] at h2
    linarith
  linarith [le_of_lt hq]

/-- **The equivalence, in the form the exponent statement consumes.**  A continuous `r`-return at
time `t` and a winding `r(1+A)`-return at winding `q` occur together, with `q` controlled by `t` and
`t = 2π q/g_0` recovering the continuous return exactly. -/
theorem continuousReturn_iff_exists_windingReturn (g : Fin (d + 1) → ℝ) (hg0 : g 0 ≠ 0)
    {r A : ℝ} (hA : ∀ j, |gapRatio g j| ≤ A) :
    ((∃ t : ℝ, ContinuousReturn g r t) → ∃ q : ℤ, WindingReturn g (r * (1 + A)) q) ∧
      ((∃ q : ℤ, WindingReturn g r q) → ∃ t : ℝ, ContinuousReturn g r t) := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨q, -, hq⟩ := exists_windingReturn_of_continuousReturn g hg0 hA ht
    exact ⟨q, hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨2 * π * (q : ℝ) / g 0, continuousReturn_of_windingReturn g hg0 hq⟩

end Winding

end

end GaloisForLFunctions.HTGeometry
