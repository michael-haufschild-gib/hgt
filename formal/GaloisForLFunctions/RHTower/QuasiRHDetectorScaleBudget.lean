import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The seven-eighths detector's exponent budget

Changing the two low detector scales shifts the Gram bound and principal signal
equally. Increasing total slot length exposes a reflected-budget face with no
hybrid or retained-kernel saving. Charging that face gives a sharp minimum of
seven eighths. These are exponent identities, not lower bounds on arithmetic
energy and not an obstruction to stronger arithmetic estimates.
-/

namespace RHTower.QuasiRHDetectorScaleBudget

noncomputable section

def lowGramExponent (x y : ℝ) : ℝ := (5 * x + y) / 12

def principalShift (x slots : ℝ) : ℝ := x / 3 - 5 / 6 + slots / 6

/-- Redistributing the two scales preserves the resulting zero boundary. -/
theorem fixed_slot_boundary (x : ℝ) :
    lowGramExponent x (5 / 6 - x) - principalShift x (1 / 6) = 7 / 8 := by
  unfold lowGramExponent principalShift
  ring

theorem retuned_nominal_boundary (x slots : ℝ) :
    lowGramExponent x (1 - slots - x) - principalShift x slots =
      11 / 12 - slots / 4 := by
  unfold lowGramExponent principalShift
  ring

def hybridSaving (v z : ℝ) : ℝ := min v (min z ((v + z) / 3))

def reflectedExponent (O H S B z v l e T : ℝ) : ℝ :=
  O / 2 + max H (v + l) - S - B + z - hybridSaving v z - l -
    2 * e / 3 - max 0 (T - v - 3 * l - e) / 2

/-- A continuum of admissible exponent configurations with zero retained length.
The excess is positive for every positive increase in total slot length. -/
theorem zero_retained_length_witness :
    ∀ h : Set.Icc (0 : ℝ) (5 / 6),
      let slots := 1 / 6 + (h : ℝ)
      let p := 1 - slots
      let d := 1 / 6 - (h : ℝ) / 5
      let H := 1 / 2 - 3 * (h : ℝ) / 5
      let z := 6 * (h : ℝ) / 5
      0 ≤ d ∧ d ≤ 1 / 6 ∧ d ≤ slots ∧ 0 ≤ H ∧ 0 ≤ z ∧
        z = slots - d ∧ H = p - 2 * d ∧ 2 * H + z - 1 = 0 ∧
        reflectedExponent 0 H 0 0 z 0 0 0 (2 * H + z - 1) =
          (p - 2 * d) + 6 * (h : ℝ) / 5 := by
  intro h
  have h0 := h.property.1
  have h1 := h.property.2
  have hH : 0 ≤ 1 / 2 - 3 * (h : ℝ) / 5 := by linarith
  have hz : 0 ≤ 6 * (h : ℝ) / 5 := by linarith
  have hT : 2 * (1 / 2 - 3 * (h : ℝ) / 5) + 6 * (h : ℝ) / 5 - 1 = 0 := by ring
  have hs : hybridSaving 0 (6 * (h : ℝ) / 5) = 0 := by
    unfold hybridSaving
    simp only [zero_add]
    exact min_eq_left (le_min hz (by linarith))
  dsimp only
  refine ⟨by linarith, by linarith, by linarith, hH, hz, by ring, by ring, hT, ?_⟩
  rw [hT]
  simp only [reflectedExponent, hs, zero_add, add_zero, zero_div,
    sub_zero, mul_zero, max_self, max_eq_left hH]
  ring

/-- The energy allowance required by the zero-retained-length face. -/
def reflectedLoss (slots : ℝ) : ℝ := max 0 ((6 * slots - 1) / 5)

/-- The nominal boundary after paying half the reflected-energy loss. -/
def retunedBoundary (slots : ℝ) : ℝ :=
  11 / 12 - slots / 4 + reflectedLoss slots / 2

theorem retunedBoundary_exact (slots : ℝ) :
    retunedBoundary slots = 7 / 8 +
      max ((1 / 6 - slots) / 4) ((7 / 20) * (slots - 1 / 6)) := by
  unfold retunedBoundary reflectedLoss
  by_cases h : slots ≤ 1 / 6
  · rw [max_eq_left (by linarith : (6 * slots - 1) / 5 ≤ 0),
      max_eq_left (by linarith : (7 / 20) * (slots - 1 / 6) ≤ (1 / 6 - slots) / 4)]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ (6 * slots - 1) / 5),
      max_eq_right (by linarith : (1 / 6 - slots) / 4 ≤ (7 / 20) * (slots - 1 / 6))]
    ring

/-- The budget has a unique minimum at total slot length one sixth. -/
theorem retunedBoundary_sharp_minimum :
    (∀ slots : ℝ, 7 / 8 ≤ retunedBoundary slots) ∧
      (∀ slots : ℝ, retunedBoundary slots = 7 / 8 ↔ slots = 1 / 6) := by
  constructor
  · intro slots
    rw [retunedBoundary_exact]
    have hleft := le_max_left ((1 / 6 - slots) / 4) ((7 / 20) * (slots - 1 / 6))
    have hright := le_max_right ((1 / 6 - slots) / 4) ((7 / 20) * (slots - 1 / 6))
    linarith
  · intro slots
    constructor
    · intro h
      rw [retunedBoundary_exact] at h
      have hleft := le_max_left ((1 / 6 - slots) / 4) ((7 / 20) * (slots - 1 / 6))
      have hright := le_max_right ((1 / 6 - slots) / 4) ((7 / 20) * (slots - 1 / 6))
      linarith
    · rintro rfl
      norm_num [retunedBoundary, reflectedLoss]

/-- Exact sensitivity to a saving in the Gram power at the original scales. -/
theorem gram_power_saving_boundary (saving : ℝ) :
    ((17 / 48 + (1 / 6 - saving) * (1 / 8)) / 2) -
        principalShift (17 / 48) (1 / 6) = 7 / 8 - saving / 16 := by
  unfold principalShift
  ring

end

end RHTower.QuasiRHDetectorScaleBudget
