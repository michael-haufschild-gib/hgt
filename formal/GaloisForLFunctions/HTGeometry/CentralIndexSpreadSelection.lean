import GaloisForLFunctions.HTGeometry.CentralIndexWindowLipschitz
import GaloisForLFunctions.HTGeometry.MonotoneIncrementMeasure

/-!
# Radii at which the central index barely moves

The window estimate needs one number to be small: the spread of the central index across the
sampling window.  That spread is an increment of the nondecreasing function `y ↦ nu(e^y)` over a step
of length `2H`, and a nondecreasing function cannot have large increments often — its total rise is
a fixed budget.

The measure bound for monotone increments therefore selects the radius: on any interval longer than
`2H (total rise) / s`, some point has spread below `s`.  No regularity of the coefficients is used,
only that the central index is nondecreasing.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- The central index is nondecreasing in the logarithmic variable. -/
theorem monotone_centralIndex_exp (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    Monotone fun y : ℝ => (centralIndex a (Real.exp y) : ℝ) := by
  intro p q hpq
  have h := centralIndex_mono ha (Real.exp_pos p) (Real.exp_le_exp.mpr hpq) hn₀
  show ((centralIndex a (Real.exp p) : ℕ) : ℝ) ≤ ((centralIndex a (Real.exp q) : ℕ) : ℝ)
  exact_mod_cast h

/-- **A radius with small spread.**  If the total rise of the central index across `[c, d + 2H]`,
scaled by `2H / s`, is shorter than the sampling interval, then some point of that interval has
central-index spread below `s`. -/
theorem exists_small_centralIndexSpread
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d H s : ℝ}
    (hcd : c ≤ d) (hH : 0 < H) (hs : 0 < s)
    (hsmall : 2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp c) : ℝ)) / s < d - c) :
    ∃ y ∈ Icc c d, centralIndexSpread a (y + H) H < s := by
  classical
  set T : ℝ → ℝ := fun y : ℝ => (centralIndex a (Real.exp y) : ℝ) with hT
  have hmono : Monotone T := monotone_centralIndex_exp ha hn₀
  set E : Set ℝ := {y ∈ Icc c d | s ≤ T (y + 2 * H) - T y} with hE
  have hbound := Nevanlinna.volume_increment_ge_le hmono hcd (by linarith : (0 : ℝ) ≤ 2 * H) hs
  have hEsub : E ⊆ Icc c d := fun y hy => hy.1
  have hEfin : volume E ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hEsub)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hnsub : ¬ (Icc c d ⊆ E) := by
    intro hsub
    have hle : volume (Icc c d) ≤ volume E := measure_mono hsub
    have hIcc : (volume (Icc c d)).toReal = d - c := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    have hlereal : (volume (Icc c d)).toReal ≤ (volume E).toReal :=
      ENNReal.toReal_mono hEfin hle
    rw [hIcc] at hlereal
    have := le_trans hlereal hbound
    linarith
  obtain ⟨y, hy, hyE⟩ := Set.not_subset.mp hnsub
  refine ⟨y, hy, ?_⟩
  have hnot : ¬ (s ≤ T (y + 2 * H) - T y) := fun h => hyE ⟨hy, h⟩
  have hrw : centralIndexSpread a (y + H) H = T (y + 2 * H) - T y := by
    rw [centralIndexSpread, hT, show y + H + H = y + 2 * H from by ring,
      show y + H - H = y from by ring]
  rw [hrw]
  exact not_le.mp hnot

/-! ## Lipschitz data at the selected radius -/

/-- Any constant above `spread / v₀` is a Lipschitz constant on scales `[v₀, H]`. -/
theorem centralIndex_le_add_of_spread_le
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H v₀ L : ℝ} (hv₀ : 0 < v₀)
    (hL : centralIndexSpread a x H / v₀ ≤ L) :
    ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp (x + v)) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + L * v := by
  intro v hv hvH
  have hbase := centralIndex_le_add_spread_div_mul (x := x) (H := H) ha hn₀ hv₀ v hv hvH
  have hvpos : (0 : ℝ) < v := lt_of_lt_of_le hv₀ hv
  have hstep : centralIndexSpread a x H / v₀ * v ≤ L * v :=
    mul_le_mul_of_nonneg_right hL hvpos.le
  linarith

/-- The same on the lower side. -/
theorem sub_of_spread_le_le_centralIndex
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H v₀ L : ℝ} (hv₀ : 0 < v₀)
    (hL : centralIndexSpread a x H / v₀ ≤ L) :
    ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp x) : ℝ) - L * v
        ≤ (centralIndex a (Real.exp (x - v)) : ℝ) := by
  intro v hv hvH
  have hbase := sub_spread_div_mul_le_centralIndex (x := x) (H := H) ha hn₀ hv₀ v hv hvH
  have hvpos : (0 : ℝ) < v := lt_of_lt_of_le hv₀ hv
  have hstep : centralIndexSpread a x H / v₀ * v ≤ L * v :=
    mul_le_mul_of_nonneg_right hL hvpos.le
  linarith

/-- **A radius at which the central index is Lipschitz on the window.**  Selecting a point of small
spread and dividing by `v₀` produces the two-sided linear bound that the Gaussian decay needs, with
the explicit constant `s / v₀`. -/
theorem exists_radius_lipschitz_centralIndex
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d H v₀ s : ℝ}
    (hcd : c ≤ d) (hH : 0 < H) (hv₀ : 0 < v₀) (hs : 0 < s)
    (hsmall : 2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp c) : ℝ)) / s < d - c) :
    ∃ x ∈ Icc (c + H) (d + H),
      (∀ v : ℝ, v₀ ≤ v → v ≤ H →
          (centralIndex a (Real.exp (x + v)) : ℝ)
            ≤ (centralIndex a (Real.exp x) : ℝ) + (s / v₀) * v)
        ∧ ∀ v : ℝ, v₀ ≤ v → v ≤ H →
          (centralIndex a (Real.exp x) : ℝ) - (s / v₀) * v
            ≤ (centralIndex a (Real.exp (x - v)) : ℝ) := by
  obtain ⟨y, hy, hspread⟩ := exists_small_centralIndexSpread ha hn₀ hcd hH hs hsmall
  refine ⟨y + H, ⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_, ?_⟩
  · refine centralIndex_le_add_of_spread_le ha hn₀ hv₀ ?_
    exact div_le_div_of_nonneg_right hspread.le hv₀.le
  · refine sub_of_spread_le_le_centralIndex ha hn₀ hv₀ ?_
    exact div_le_div_of_nonneg_right hspread.le hv₀.le

end GaloisForLFunctions.HTGeometry
