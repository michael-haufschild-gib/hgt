import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# One-period sublevel measure of the cosine

Within one period the deep sublevel set `{cos ≤ -1/2}` is exactly the middle third interval
`[2π/3, 4π/3]`, of measure `2π/3`: a single-frequency mean-zero oscillation spends exactly one
third of every period at depth `1/2` of its amplitude.  This is the one-period anchor for
negative-density lower bounds of nonzero almost-periodic anomalies: any carrier admitting a
one-sided lower bound on more than two thirds of logarithmic scales is incompatible with a
persistent single-frequency cosine deficit.
-/

open Real Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- Value anchor: `cos (2π/3) = -1/2`. -/
theorem cos_two_pi_div_three : Real.cos (2 * π / 3) = -(1 / 2) := by
  have h : (2 : ℝ) * π / 3 = π - π / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]

/-- Value anchor: `cos (4π/3) = -1/2`. -/
theorem cos_four_pi_div_three : Real.cos (4 * π / 3) = -(1 / 2) := by
  have h : (4 : ℝ) * π / 3 = 2 * π - 2 * π / 3 := by ring
  rw [h, Real.cos_two_pi_sub, cos_two_pi_div_three]

/-- **The one-period deep sublevel set of the cosine is the middle third.** -/
theorem cos_sublevel_period_eq :
    {v ∈ Icc (0 : ℝ) (2 * π) | Real.cos v ≤ -(1 / 2)} =
      Icc (2 * π / 3) (4 * π / 3) := by
  have hpi := Real.pi_pos
  ext v
  simp only [mem_setOf_eq, mem_Icc]
  constructor
  · rintro ⟨⟨h0, h2⟩, hcos⟩
    constructor
    · by_contra hlt
      rw [not_le] at hlt
      have hvpi : v ∈ Icc (0 : ℝ) π := ⟨h0, by linarith⟩
      have h23 : (2 * π / 3) ∈ Icc (0 : ℝ) π := ⟨by positivity, by linarith⟩
      have := Real.strictAntiOn_cos hvpi h23 hlt
      rw [cos_two_pi_div_three] at this
      linarith
    · by_contra hlt
      rw [not_le] at hlt
      have href : Real.cos v = Real.cos (2 * π - v) := by
        rw [Real.cos_two_pi_sub]
      have hmem : (2 * π - v) ∈ Icc (0 : ℝ) π := ⟨by linarith, by linarith⟩
      have h23 : (2 * π / 3) ∈ Icc (0 : ℝ) π := ⟨by positivity, by linarith⟩
      have hlt' : 2 * π - v < 2 * π / 3 := by linarith
      have := Real.strictAntiOn_cos hmem h23 hlt'
      rw [cos_two_pi_div_three, ← href] at this
      linarith
  · rintro ⟨hl, hr⟩
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rcases le_total v π with hvpi | hvpi
    · have h23 : (2 * π / 3) ∈ Icc (0 : ℝ) π := ⟨by positivity, by linarith⟩
      have hv : v ∈ Icc (0 : ℝ) π := ⟨by linarith, hvpi⟩
      rcases eq_or_lt_of_le hl with heq | hlt
      · rw [← heq, cos_two_pi_div_three]
      · have := Real.strictAntiOn_cos h23 hv hlt
        rw [cos_two_pi_div_three] at this
        linarith
    · have href : Real.cos v = Real.cos (2 * π - v) := by
        rw [Real.cos_two_pi_sub]
      have h23 : (2 * π / 3) ∈ Icc (0 : ℝ) π := ⟨by positivity, by linarith⟩
      have hmem : (2 * π - v) ∈ Icc (0 : ℝ) π := ⟨by linarith, by linarith⟩
      rcases eq_or_lt_of_le (show 2 * π / 3 ≤ 2 * π - v by linarith) with heq | hlt
      · rw [href, ← heq, cos_two_pi_div_three]
      · have := Real.strictAntiOn_cos h23 hmem hlt
        rw [cos_two_pi_div_three, ← href] at this
        linarith

/-- **One-period sublevel measure: exactly one third of the period.** -/
theorem volume_cos_sublevel_period :
    volume {v ∈ Icc (0 : ℝ) (2 * π) | Real.cos v ≤ -(1 / 2)} =
      ENNReal.ofReal (2 * π / 3) := by
  rw [cos_sublevel_period_eq, Real.volume_Icc]
  congr 1
  ring

end GaloisForLFunctions.HTGeometry
