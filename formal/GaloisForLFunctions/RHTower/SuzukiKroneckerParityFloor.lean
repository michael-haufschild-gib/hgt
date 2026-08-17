import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.MeanInequalities

/-!
# The quantitative parity floor of a violated arctangent relation

A finite integer relation among the ordinates whose arctangent phases miss `πℤ` by `Δ` forces every
aperture phase vector to stay a definite distance from the collapse point.  The mechanism is two
elementary inequalities: Cauchy–Schwarz splits the relation defect between the relation coefficients
and the phase distances, and Jordan's inequality `sin d ≥ 2d/π` on `[0, π/2]` converts squared
distances into the odd ultraviolet energy.

The result is an aperture-independent floor `4Δ²/(π² ∑ n²/w)`, which is exactly the card's `(370)`.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **Jordan's inequality in squared form.** -/
theorem sq_jordan {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ Real.pi / 2) :
    (2 / Real.pi) ^ 2 * d ^ 2 ≤ Real.sin d ^ 2 := by
  have hj := Real.mul_le_sin h0 h1
  have hnn : 0 ≤ 2 / Real.pi * d := by
    have := Real.pi_pos
    positivity
  nlinarith [hj, hnn]

/-- **`(370)`: a violated arctangent relation gives an aperture-independent odd energy floor.** -/
theorem parity_energy_floor {ι : Type*} (s : Finset ι) (n w d : ι → ℝ) {Δ : ℝ}
    (hw : ∀ i ∈ s, 0 < w i) (hd0 : ∀ i ∈ s, 0 ≤ d i) (hd1 : ∀ i ∈ s, d i ≤ Real.pi / 2)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ ∑ i ∈ s, |n i| * d i)
    (hS : 0 < ∑ i ∈ s, n i ^ 2 / w i) :
    4 * Δ ^ 2 / (Real.pi ^ 2 * ∑ i ∈ s, n i ^ 2 / w i)
      ≤ ∑ i ∈ s, w i * Real.sin (d i) ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  -- Cauchy--Schwarz with the split `|n| d = (|n|/√w) * (√w d)`
  have hsplit : ∀ i ∈ s, |n i| * d i = (|n i| / Real.sqrt (w i)) * (Real.sqrt (w i) * d i) := by
    intro i hi
    have hwi := hw i hi
    have hsq : Real.sqrt (w i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hwi)
    field_simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => |n i| / Real.sqrt (w i)) (fun i => Real.sqrt (w i) * d i)
  have hA : (∑ i ∈ s, (|n i| / Real.sqrt (w i)) ^ 2) = ∑ i ∈ s, n i ^ 2 / w i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hwi := hw i hi
    rw [div_pow, sq_abs, Real.sq_sqrt hwi.le]
  have hB : (∑ i ∈ s, (Real.sqrt (w i) * d i) ^ 2) = ∑ i ∈ s, w i * d i ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hwi := hw i hi
    rw [mul_pow, Real.sq_sqrt hwi.le]
  have hprod : (∑ i ∈ s, |n i| * d i) ^ 2
      ≤ (∑ i ∈ s, n i ^ 2 / w i) * ∑ i ∈ s, w i * d i ^ 2 := by
    rw [← hA, ← hB]
    calc (∑ i ∈ s, |n i| * d i) ^ 2
        = (∑ i ∈ s, (|n i| / Real.sqrt (w i)) * (Real.sqrt (w i) * d i)) ^ 2 := by
          rw [Finset.sum_congr rfl hsplit]
      _ ≤ _ := hcs
  have hΔsq : Δ ^ 2 ≤ (∑ i ∈ s, n i ^ 2 / w i) * ∑ i ∈ s, w i * d i ^ 2 := by
    have hmono : Δ ^ 2 ≤ (∑ i ∈ s, |n i| * d i) ^ 2 := by
      have hsum0 : 0 ≤ ∑ i ∈ s, |n i| * d i := le_trans hΔ0 hΔ
      nlinarith [hΔ, hΔ0, hsum0]
    linarith [hmono, hprod]
  -- Jordan on each term
  have hjordan : (2 / Real.pi) ^ 2 * (∑ i ∈ s, w i * d i ^ 2)
      ≤ ∑ i ∈ s, w i * Real.sin (d i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hwi := hw i hi
    have hji := sq_jordan (hd0 i hi) (hd1 i hi)
    nlinarith [hji, hwi]
  have hdsum : Δ ^ 2 / (∑ i ∈ s, n i ^ 2 / w i) ≤ ∑ i ∈ s, w i * d i ^ 2 := by
    rw [div_le_iff₀ hS]
    linarith [hΔsq]
  have hfinal : 4 * Δ ^ 2 / (Real.pi ^ 2 * ∑ i ∈ s, n i ^ 2 / w i)
      = (2 / Real.pi) ^ 2 * (Δ ^ 2 / (∑ i ∈ s, n i ^ 2 / w i)) := by
    field_simp
    ring
  rw [hfinal]
  have hcoef : (0 : ℝ) < (2 / Real.pi) ^ 2 := by positivity
  calc (2 / Real.pi) ^ 2 * (Δ ^ 2 / (∑ i ∈ s, n i ^ 2 / w i))
      ≤ (2 / Real.pi) ^ 2 * (∑ i ∈ s, w i * d i ^ 2) :=
        mul_le_mul_of_nonneg_left hdsum hcoef.le
    _ ≤ ∑ i ∈ s, w i * Real.sin (d i) ^ 2 := hjordan

end GaloisForLFunctions.RHTower
