import GaloisForLFunctions.RHTower.Sieve.HeathBrownPrimitiveWindow
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowSharpDelta

/-!
# Primitive directions in a Heath--Brown logarithmic collision window

The logarithmic near-product condition confines every primitive direction to an explicit
multiplicative slope interval.  Farey packing and the source's elementary exponential-width bound
then give the `O(delta Q^(2 : ℕ))` nonexceptional-direction count with explicit constant four.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- An absolute logarithmic bound is exactly a two-sided exponential ratio bound. -/
theorem exp_neg_le_self_le_exp_of_abs_log_le {r delta : ℝ}
    (hr : 0 < r) (h : |Real.log r| ≤ delta) :
    Real.exp (-delta) ≤ r ∧ r ≤ Real.exp delta := by
  have hb := abs_le.mp h
  constructor
  · have := Real.exp_le_exp.mpr hb.1
    rwa [Real.exp_log hr] at this
  · have := Real.exp_le_exp.mpr hb.2
    rwa [Real.exp_log hr] at this

/-- Primitive positive directions satisfying one normalized logarithmic collision condition. -/
def heathBrownPrimitiveLogWindow
    (Q : ℕ) (m1 m2 delta : ℝ) : Finset (ℕ × ℕ) :=
  (heathBrownPrimitiveSquare Q).filter fun p =>
    |Real.log ((m1 * (p.1 : ℝ)) / (m2 * (p.2 : ℝ)))| ≤ delta

theorem mem_heathBrownPrimitiveLogWindow
    {Q : ℕ} {m1 m2 delta : ℝ} {p : ℕ × ℕ} :
    p ∈ heathBrownPrimitiveLogWindow Q m1 m2 delta ↔
      p ∈ heathBrownPrimitiveSquare Q ∧
        |Real.log ((m1 * (p.1 : ℝ)) / (m2 * (p.2 : ℝ)))| ≤ delta := by
  simp [heathBrownPrimitiveLogWindow]

/-- A logarithmic product collision places the primitive slope in its exact exponential window. -/
theorem heathBrownPrimitiveLogWindow_slope_mem
    {Q : ℕ} {m1 m2 delta : ℝ} (hm1 : 0 < m1) (hm2 : 0 < m2)
    {p : ℕ × ℕ} (hp : p ∈ heathBrownPrimitiveLogWindow Q m1 m2 delta) :
    (m2 / m1) * Real.exp (-delta) ≤ heathBrownFareyValue p ∧
      heathBrownFareyValue p ≤ (m2 / m1) * Real.exp delta := by
  have hp' := mem_heathBrownPrimitiveLogWindow.mp hp
  have hpp := mem_heathBrownPrimitiveSquare.mp hp'.1
  have hp1 : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hpp.1
  have hp2 : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast hpp.2.2.1
  let r : ℝ := (m1 * (p.1 : ℝ)) / (m2 * (p.2 : ℝ))
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨hlow, hupp⟩ := exp_neg_le_self_le_exp_of_abs_log_le hr hp'.2
  have hslope : heathBrownFareyValue p = (m2 / m1) * r := by
    dsimp [r, heathBrownFareyValue]
    field_simp
  rw [hslope]
  exact ⟨mul_le_mul_of_nonneg_left hlow (by positivity),
    mul_le_mul_of_nonneg_left hupp (by positivity)⟩

/-- **Heath--Brown primitive logarithmic-window count.** If `m2 ≤ m1` and `0 < delta ≤ 1`,
the collision window contains at most `4 delta Q² + 1` primitive directions. -/
theorem card_heathBrownPrimitiveLogWindow_le
    {Q : ℕ} (hQ : 1 ≤ Q) {m1 m2 delta : ℝ}
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm : m2 ≤ m1)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    ((heathBrownPrimitiveLogWindow Q m1 m2 delta).card : ℝ) ≤
      4 * delta * (Q : ℝ) ^ (2 : ℕ) + 1 := by
  let a := (m2 / m1) * Real.exp (-delta)
  let b := (m2 / m1) * Real.exp delta
  have hratio0 : 0 < m2 / m1 := div_pos hm2 hm1
  have hab : a ≤ b := by
    dsimp [a, b]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) hratio0.le
  have hsub : heathBrownPrimitiveLogWindow Q m1 m2 delta ⊆
      heathBrownPrimitiveWindow Q a b := by
    intro p hp
    rw [heathBrownPrimitiveWindow, Finset.mem_filter]
    exact ⟨(mem_heathBrownPrimitiveLogWindow.mp hp).1,
      heathBrownPrimitiveLogWindow_slope_mem hm1 hm2 hp⟩
  have hcardNat := Finset.card_le_card hsub
  have hcardReal :
      ((heathBrownPrimitiveLogWindow Q m1 m2 delta).card : ℝ) ≤
        ((heathBrownPrimitiveWindow Q a b).card : ℝ) := by exact_mod_cast hcardNat
  have hpack := card_heathBrownPrimitiveWindow_le hQ hab
  have hratio1 : m2 / m1 ≤ 1 := (div_le_one hm1).mpr hm
  have hexp := exp_sub_exp_neg_le_four_mul hdelta0 hdelta1
  have hwidth : b - a ≤ 4 * delta := by
    dsimp [a, b]
    have hfactor : b - a = (m2 / m1) *
        (Real.exp delta - Real.exp (-delta)) := by
      dsimp [b, a]
      ring
    rw [hfactor]
    have hdiff0 : 0 ≤ Real.exp delta - Real.exp (-delta) := by
      exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
    calc
      (m2 / m1) * (Real.exp delta - Real.exp (-delta)) ≤
          1 * (Real.exp delta - Real.exp (-delta)) :=
        mul_le_mul_of_nonneg_right hratio1 hdiff0
      _ ≤ 4 * delta := by simpa using hexp
  calc
    ((heathBrownPrimitiveLogWindow Q m1 m2 delta).card : ℝ) ≤
        ((heathBrownPrimitiveWindow Q a b).card : ℝ) := hcardReal
    _ ≤ (b - a) * (Q : ℝ) ^ (2 : ℕ) + 1 := hpack
    _ ≤ 4 * delta * (Q : ℝ) ^ (2 : ℕ) + 1 := by
      gcongr

end

end RHTower.Sieve
