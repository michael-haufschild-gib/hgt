import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheDepthBecomesVisibleJustAboveTheNyquistAperture
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionIntervalIsTheWholeRange

/-!
# A uniform deficit bound already passes the trans-Nyquist gate

Every reading the programme has examined fails the trans-Nyquist gate: at each bounded aperture a
depth-`½` lattice shares the reading of the on-line lattice, at every coercivity level and in every
depth unit. The only reading known to pass was exact positivity on all compactly supported tests —
an exact equality constraint that no estimate delivers.

A strictly weaker reading passes. Fix any level `η` and ask only for a **uniform deficit bound**:
for every aperture, the polar-constrained Weil form is at least `−η‖f‖²`. The on-line lattice
satisfies it (`uniformDeficit_onLineLattice`) and **no** off-line lattice does, at any level
(`not_uniformDeficit_offLineLattice`), because the lattice ground energy of a depth-`δ` lattice
deepens without bound along the aliasing index:

`−L · latticeFloor L δ (m+1) ≥ L · m · (m δ²L²/2 − 1) → ∞`

(`exists_aperture_not_weilFloorAtLevel`, from `latticeFloor_eq` and `1 + y²/2 ≤ cosh y`).

Hence `uniformDeficit_separates_the_transNyquist_pair`: the reading separates the pair that every
bounded reading identifies, so it passes the gate — while demanding no positivity at all, only that
the deficit not grow with the aperture.

This locates the real content of the unbounded certificate once more, and more sharply than
`theGradedApertureJumpIsUniformityItself`: not positivity, not a margin, but the *absence of growth*
in the deficit. A mechanism may lose any fixed amount of energy at every aperture and still decide
the pair; it may not lose an amount that grows.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. Two elementary hyperbolic estimates -/

/-- `1 + y²/2 ≤ cosh y` for `y ≥ 0`, from `y/2 ≤ sinh (y/2)`. -/
theorem one_add_sq_half_le_cosh {y : ℝ} (hy : 0 ≤ y) : 1 + y ^ 2 / 2 ≤ Real.cosh y := by
  have hhalf : (0 : ℝ) ≤ y / 2 := by linarith
  have h1 : y / 2 ≤ Real.sinh (y / 2) := Real.self_le_sinh_iff.mpr hhalf
  have h0 : (0 : ℝ) ≤ Real.sinh (y / 2) := Real.sinh_nonneg_iff.mpr hhalf
  have h3 : Real.cosh y = 2 * Real.sinh (y / 2) ^ 2 + 1 := by
    have hc := Real.cosh_two_mul (y / 2)
    rw [show 2 * (y / 2) = y by ring, Real.cosh_sq] at hc
    linarith
  rw [h3]
  nlinarith

/-- `cosh (m x) · sinh x ≤ sinh ((m+1) x)` for `x ≥ 0`: drop the nonnegative summand of the
addition formula. -/
theorem cosh_mul_sinh_le_sinh_succ {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    Real.cosh ((m : ℝ) * x) * Real.sinh x ≤ Real.sinh (((m : ℝ) + 1) * x) := by
  have hmx : (0 : ℝ) ≤ (m : ℝ) * x := by positivity
  have hsplit : ((m : ℝ) + 1) * x = (m : ℝ) * x + x := by ring
  rw [hsplit, Real.sinh_add]
  have h1 : (0 : ℝ) ≤ Real.sinh ((m : ℝ) * x) := Real.sinh_nonneg_iff.mpr hmx
  have h2 : (0 : ℝ) < Real.cosh x := Real.cosh_pos x
  nlinarith

/-! ### 2. The lattice deficit grows without bound -/

/-- **The deficit of an off-line lattice outgrows every level.** At a suitable aperture the
polar-constrained Weil form of a depth-`δ` lattice falls below `−η‖f‖²`. -/
theorem exists_aperture_not_weilFloorAtLevel {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (η : ℝ) :
    ∃ a : ℝ, L / 2 < a ∧ ¬ WeilFloorAtLevel (offLineLatticeConfig hL hδ hδ') a η := by
  have hx0 : (0 : ℝ) < δ * L := by positivity
  have hs0 : (0 : ℝ) < Real.sinh (δ * L) := Real.sinh_pos_iff.mpr hx0
  obtain ⟨m, hm⟩ := exists_nat_gt (max (4 / (δ * L) ^ 2) ((η + 1) / L))
  have hm1 : (4 : ℝ) / (δ * L) ^ 2 < (m : ℝ) := lt_of_le_of_lt (le_max_left _ _) hm
  have hm2 : (η + 1) / L < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_trans (by positivity) hm1
  have hmsq : (2 : ℝ) ≤ (m : ℝ) * (δ * L) ^ 2 / 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (δ * L) ^ 2)] at hm1
    linarith
  have hmL : η + 1 ≤ L * (m : ℝ) := by
    rw [div_lt_iff₀ hL] at hm2
    linarith
  -- the aliasing index `m + 1`
  have hratio : Real.cosh ((m : ℝ) * (δ * L)) ≤
      Real.sinh (((m : ℝ) + 1) * (δ * L)) / Real.sinh (δ * L) :=
    (le_div_iff₀ hs0).mpr (cosh_mul_sinh_le_sinh_succ hx0.le m)
  have hcosh : 1 + ((m : ℝ) * (δ * L)) ^ 2 / 2 ≤ Real.cosh ((m : ℝ) * (δ * L)) :=
    one_add_sq_half_le_cosh (by positivity)
  have hfloor : latticeFloor L δ (m + 1) ≤ (m : ℝ) - ((m : ℝ) * (δ * L)) ^ 2 / 2 := by
    rw [latticeFloor_eq hx0 (m + 1)]
    push_cast
    linarith
  have hdeep : η < -(L * latticeFloor L δ (m + 1)) := by
    have hmul := mul_le_mul_of_nonneg_left hfloor hL.le
    have hkey : L * ((m : ℝ) * ((m : ℝ) * (δ * L) ^ 2 / 2 - 1)) ≤
        -(L * latticeFloor L δ (m + 1)) := by linarith
    have hextra : 0 ≤ L * (m : ℝ) * ((m : ℝ) * (δ * L) ^ 2 / 2 - 2) :=
      mul_nonneg (mul_nonneg hL.le hmpos.le) (by linarith)
    linarith
  refine ⟨((m : ℝ) + 1) * L / 2, by nlinarith [hmpos], ?_⟩
  have hceil : ⌈2 * (((m : ℝ) + 1) * L / 2) / L⌉₊ = m + 1 := by
    rw [show 2 * (((m : ℝ) + 1) * L / 2) / L = ((m : ℝ) + 1) by field_simp]
    rw [show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
  rw [offLineLattice_weilFloor_iff hL hδ hδ' (by nlinarith [hmpos] : L / 2 < ((m : ℝ) + 1) * L / 2)
    η, hceil]
  exact not_le.mpr hdeep

/-! ### 3. The uniform-deficit reading -/

/-- A **uniform deficit bound**: at every aperture the polar-constrained Weil form is at least
`−η‖f‖²`, with one level `η` for all apertures. No positivity is asked for. -/
def uniformDeficit (η : ℝ) (Z : TemperedZeroConfig) : Prop :=
  ∀ a : ℝ, 0 < a → WeilFloorAtLevel Z.1 a η

/-- The on-line lattice satisfies it at every nonnegative level. -/
theorem uniformDeficit_onLineLattice {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η) :
    uniformDeficit η (onLineLattice hL) := by
  intro a _ f hf hfs _ _
  have hpos : 0 ≤ ((onLineLattice hL).1.W f f).re := re_W_onLineLatticeConfig_nonneg hL f
  have hint : (0 : ℝ) ≤ ∫ u, ‖f u‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  nlinarith

/-- **No off-line lattice satisfies it, at any level.** -/
theorem not_uniformDeficit_offLineLattice {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (η : ℝ) : ¬ uniformDeficit η (offLineLattice hL hδ hδ') := by
  intro h
  obtain ⟨a, ha, hnot⟩ := exists_aperture_not_weilFloorAtLevel hL hδ hδ' η
  exact hnot (h a (by linarith))

/-! ### 4. It passes the gate -/

/-- **The uniform-deficit reading passes the trans-Nyquist gate.** It separates the pair that every
bounded-aperture reading identifies — a depth-`½` lattice against the on-line lattice — at every
level, while requiring no positivity. -/
theorem uniformDeficit_separates_the_transNyquist_pair {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η) :
    uniformDeficit η (offLineLattice hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl) ≠
      uniformDeficit η (onLineLattice hL) := by
  intro heq
  exact not_uniformDeficit_offLineLattice hL (by norm_num) le_rfl η
    (heq ▸ uniformDeficit_onLineLattice hL hη)

/-- **The content of the unbounded certificate is the absence of growth.** The reading asks for no
margin and no positivity, only that one deficit level serve every aperture; that already decides
the trans-Nyquist pair, which no bounded reading does at any level or in any unit. -/
theorem theGateIsPassedByNonGrowth {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η) :
    uniformDeficit η (onLineLattice hL) ∧
      (∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ hδ' : δ ≤ 1 / 2,
        ¬ uniformDeficit η (offLineLattice hL hδ hδ')) ∧
      uniformDeficit η (offLineLattice hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl) ≠
        uniformDeficit η (onLineLattice hL) :=
  ⟨uniformDeficit_onLineLattice hL hη,
    fun _ hδ hδ' => not_uniformDeficit_offLineLattice hL hδ hδ' η,
    uniformDeficit_separates_the_transNyquist_pair hL hη⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
