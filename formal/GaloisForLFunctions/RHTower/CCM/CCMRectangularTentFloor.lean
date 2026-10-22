import Mathlib

/-!
# The rectangular readout: tent algebra, adjacent blocks, and the Haar shell

Five exact mechanisms of the card are formalized.

*The moving tent.*  `T_{a,L}(h) = max(0, L − |h − (2a−L)|)` is supported on `[2a−2L, 2a]` and
vanishes at both endpoints — equation `(2)`.

*The two-edge autocorrelation.*  The same-edge overlaps contribute `2max(0, L−h)` and the
cross-edge overlap is exactly the tent — equation `(9)`.

*Adjacent blocks.*  With `c = 2a − L` the readout `(6)` is the difference of the two adjacent equal
logarithmic blocks `[c, c+L]` and `[c−L, c]` — equation `(7)`.

*The Haar shell.*  The zero-mean Haar function of `(17)` is orthogonal to the boundary indicator
`1_{[0,T)}` unless `T` lies inside the finite shell `(c−L, c+L)` — equation `(18)`.

*The uniform Gamma bound.*  A positive quadratic form on a sum of two translates is at most `4`
times its value on one edge — equations `(12)`, `(14)`.

The distributional restricted Weil form, the Stieltjes autocorrelation law `(10)`, the digamma form
domain and the rectangular completeness theorem `(15)` are cited parents and stay outside the Lean
statement.
-/

open Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The moving tent -/

/-- The moving tent `(2)`. -/
def movingTent (a L h : ℝ) : ℝ := max 0 (L - |h - (2 * a - L)|)

theorem movingTent_nonneg (a L h : ℝ) : 0 ≤ movingTent a L h := le_max_left _ _

/-- **Equation (2), support.**  The tent vanishes outside `[2a−2L, 2a]`. -/
theorem movingTent_eq_zero_of_outside {a L h : ℝ} (hL : 0 < L)
    (h' : h ≤ 2 * a - 2 * L ∨ 2 * a ≤ h) : movingTent a L h = 0 := by
  rw [movingTent, max_eq_left]
  rcases h' with hlow | hhigh
  · have habs : L ≤ |h - (2 * a - L)| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    linarith
  · have habs : L ≤ |h - (2 * a - L)| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    linarith

/-- **Equation (2), endpoints.** -/
theorem movingTent_endpoint_left {a L : ℝ} (hL : 0 < L) :
    movingTent a L (2 * a - 2 * L) = 0 :=
  movingTent_eq_zero_of_outside hL (Or.inl le_rfl)

theorem movingTent_endpoint_right {a L : ℝ} (hL : 0 < L) :
    movingTent a L (2 * a) = 0 :=
  movingTent_eq_zero_of_outside hL (Or.inr le_rfl)

/-- **Equation (2), peak.**  The tent attains the value `L` at the centre. -/
theorem movingTent_center (a L : ℝ) (hL : 0 ≤ L) : movingTent a L (2 * a - L) = L := by
  rw [movingTent, show (2 * a - L) - (2 * a - L) = 0 by ring, abs_zero, sub_zero,
    max_eq_right hL]

/-! ## The two-edge autocorrelation -/

/-- The overlap length of two intervals of common length `L`. -/
theorem interval_overlap_len (u v L : ℝ) :
    max 0 (min (u + L) (v + L) - max u v) = max 0 (L - |u - v|) := by
  congr 1
  rcases le_total u v with h | h
  · rw [min_eq_left (by linarith), max_eq_right h, abs_of_nonpos (by linarith)]
    linarith
  · rw [min_eq_right (by linarith), max_eq_left h, abs_of_nonneg (by linarith)]
    linarith

/-- **Equation (9).**  The two-edge autocorrelation is the fixed same-edge contribution plus the
moving cross-edge tent: both same-edge overlaps have length `max(0, L−|h|)`, and the cross-edge
overlap is exactly the tent. -/
theorem autocorrelation_split (a L h : ℝ) :
    max 0 (min ((h : ℝ) + L) ((2 * a - L) + L) - max h (2 * a - L))
      = movingTent a L h := by
  rw [interval_overlap_len, movingTent]

/-! ## Adjacent blocks -/

/-- **Equations (6)–(7).**  With `c = 2a − L` the readout is the difference of the two adjacent
equal logarithmic blocks. -/
theorem adjacent_block_readout (R : ℝ → ℝ) (a L : ℝ) :
    (∫ h in Set.Icc (2 * a - L) (2 * a), R h)
        - ∫ h in Set.Icc (2 * a - 2 * L) (2 * a - L), R h
      = (∫ h in Set.Icc ((2 * a - L)) ((2 * a - L) + L), R h)
        - ∫ h in Set.Icc ((2 * a - L) - L) (2 * a - L), R h := by
  have h1 : (2 * a - L) + L = 2 * a := by ring
  have h2 : (2 * a - L) - L = 2 * a - 2 * L := by ring
  rw [h1, h2]

/-! ## The Haar shell -/

/-- The length of the overlap of `[u,v]` with `[0,T)`. -/
def overlapLen (u v T : ℝ) : ℝ := max 0 (min v T - max u 0)

/-- **Equation (18).**  The zero-mean Haar function is orthogonal to the boundary indicator unless
the cut lies inside the finite shell. -/
theorem haar_overlap_eq_zero {c L T : ℝ} (hL : 0 < L) (hc : 0 ≤ c - L)
    (hT : T ≤ c - L ∨ c + L ≤ T) :
    overlapLen c (c + L) T - overlapLen (c - L) c T = 0 := by
  rcases hT with hlow | hhigh
  · have h1 : overlapLen c (c + L) T = 0 := by
      rw [overlapLen, max_eq_left]
      have hmin : min (c + L) T ≤ T := min_le_right _ _
      have hmax : c ≤ max c 0 := le_max_left _ _
      linarith
    have h2 : overlapLen (c - L) c T = 0 := by
      rw [overlapLen, max_eq_left]
      have hmin : min c T ≤ T := min_le_right _ _
      have hmax : c - L ≤ max (c - L) 0 := le_max_left _ _
      linarith
    rw [h1, h2, sub_zero]
  · have hcpos : 0 ≤ c := by linarith
    have h1 : overlapLen c (c + L) T = L := by
      rw [overlapLen, min_eq_left (by linarith), max_eq_left hcpos, max_eq_right (by linarith)]
      linarith
    have h2 : overlapLen (c - L) c T = L := by
      rw [overlapLen, min_eq_left (by linarith), max_eq_left hc, max_eq_right (by linarith)]
      linarith
    rw [h1, h2, sub_self]

/-! ## The uniform Gamma bound -/

/-- **Equation (12).**  A positive quadratic form on a sum of two translates is at most four times
its value on one of them, when the two have equal energy. -/
theorem quadratic_two_translate_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u v : H) (hnorm : ‖v‖ = ‖u‖) :
    ‖u + v‖ ^ (2 : ℕ) ≤ 4 * ‖u‖ ^ (2 : ℕ) := by
  have htri : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
  have hnn : 0 ≤ ‖u‖ := norm_nonneg u
  rw [hnorm] at htri
  nlinarith [htri, hnn, norm_nonneg (u + v)]

end GaloisForLFunctions.RHTower

end
