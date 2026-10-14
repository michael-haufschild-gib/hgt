import GaloisForLFunctions.HTGeometry.BackwardSummableRecurrence
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The inverse energy of a decreasing genealogy tail profile

The inverse formula is positive exactly at a strict drop. Its energy is bounded
by the telescoping total drop, so it constructs bounded square-summable positive
coefficients from every strictly decreasing profile with boundary value one.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology

def genealogyProfileEnergy (Z : ℕ → ℝ) (n : ℕ) : ℝ :=
  4 * (Z n - Z (n + 1)) / (2 * Z (n + 1) - Z (n + 2))

def genealogyProfileCoefficient (Z : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (genealogyProfileEnergy Z n)

theorem genealogyProfile_one_le {Z : ℕ → ℝ} (hZ : Antitone Z)
    (hlim : Tendsto Z atTop (𝓝 1)) (n : ℕ) : 1 ≤ Z n :=
  hZ.le_of_tendsto hlim n

theorem genealogyProfile_denominator {Z : ℕ → ℝ} (hZ : Antitone Z)
    (hlim : Tendsto Z atTop (𝓝 1)) (n : ℕ) : 1 ≤ 2 * Z (n + 1) - Z (n + 2) := by
  have h1 := genealogyProfile_one_le hZ hlim (n + 1)
  have h2 := hZ (Nat.le_succ (n + 1))
  linarith

theorem genealogyProfileEnergy_nonneg {Z : ℕ → ℝ} (hZ : Antitone Z)
    (hlim : Tendsto Z atTop (𝓝 1)) (n : ℕ) : 0 ≤ genealogyProfileEnergy Z n := by
  have hd := genealogyProfile_denominator hZ hlim n
  have hs := hZ (Nat.le_succ n)
  dsimp [genealogyProfileEnergy]
  positivity

theorem genealogyProfileEnergy_pos {Z : ℕ → ℝ} (hZ : StrictAnti Z)
    (hlim : Tendsto Z atTop (𝓝 1)) (n : ℕ) : 0 < genealogyProfileEnergy Z n := by
  apply div_pos
  · have hs := hZ (Nat.lt_succ_self n)
    linarith
  · have hd := genealogyProfile_denominator hZ.antitone hlim n
    linarith

theorem genealogyProfileEnergy_le_drop {Z : ℕ → ℝ} (hZ : Antitone Z)
    (hlim : Tendsto Z atTop (𝓝 1)) (n : ℕ) :
    genealogyProfileEnergy Z n ≤ 4 * (Z n - Z (n + 1)) := by
  have hd := genealogyProfile_denominator hZ hlim n
  have hs := hZ (Nat.le_succ n)
  apply (div_le_iff₀ (by linarith : 0 < 2 * Z (n + 1) - Z (n + 2))).mpr
  nlinarith [mul_nonneg (show 0 ≤ Z n - Z (n + 1) by linarith)
    (show 0 ≤ 2 * Z (n + 1) - Z (n + 2) - 1 by linarith)]

theorem genealogyProfileEnergy_sum_le {Z : ℕ → ℝ} (hZ : Antitone Z)
    (hlim : Tendsto Z atTop (𝓝 1)) (N : ℕ) :
    (∑ n ∈ Finset.range N, genealogyProfileEnergy Z n) ≤ 4 * (Z 0 - Z N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have h := genealogyProfileEnergy_le_drop hZ hlim N
      linarith

theorem genealogyProfileEnergy_summable {Z : ℕ → ℝ} (hZ : Antitone Z)
    (hlim : Tendsto Z atTop (𝓝 1)) : Summable (genealogyProfileEnergy Z) := by
  apply summable_of_sum_range_le (c := 4 * (Z 0 - 1)) (genealogyProfileEnergy_nonneg hZ hlim)
  intro N
  have hs := genealogyProfileEnergy_sum_le hZ hlim N
  have h1 := genealogyProfile_one_le hZ hlim N
  linarith

theorem genealogyProfileEnergy_tsum_le {Z : ℕ → ℝ} (hZ : Antitone Z)
    (hlim : Tendsto Z atTop (𝓝 1)) :
    (∑' n, genealogyProfileEnergy Z n) ≤ 4 * (Z 0 - 1) := by
  apply le_of_tendsto_of_tendsto'
    (genealogyProfileEnergy_summable hZ hlim).hasSum.tendsto_sum_nat tendsto_const_nhds
  intro N
  have hs := genealogyProfileEnergy_sum_le hZ hlim N
  have h1 := genealogyProfile_one_le hZ hlim N
  linarith

theorem genealogyProfileEnergy_le {Z : ℕ → ℝ} (hZ : Antitone Z)
    (hlim : Tendsto Z atTop (𝓝 1)) (n : ℕ) :
    genealogyProfileEnergy Z n ≤ 4 * (Z 0 - 1) := by
  have hd := genealogyProfileEnergy_le_drop hZ hlim n
  have h0 := hZ (Nat.zero_le n)
  have h1 := genealogyProfile_one_le hZ hlim (n + 1)
  linarith

theorem genealogyProfile_recurrence {Z : ℕ → ℝ} (hZ : Antitone Z)
    (hlim : Tendsto Z atTop (𝓝 1)) (n : ℕ) :
    Z n = Z (n + 1) + genealogyProfileEnergy Z n / 4 *
      (2 * Z (n + 1) - Z (n + 2)) := by
  have hd := genealogyProfile_denominator hZ hlim n
  have he : genealogyProfileEnergy Z n / 4 * (2 * Z (n + 1) - Z (n + 2)) =
      Z n - Z (n + 1) := by
    dsimp [genealogyProfileEnergy]
    calc
      _ = (Z n - Z (n + 1)) / (2 * Z (n + 1) - Z (n + 2)) *
          (2 * Z (n + 1) - Z (n + 2)) := by ring
      _ = _ := div_mul_cancel₀ _ (by linarith)
  linarith

theorem genealogyProfileCoefficient_pos {Z : ℕ → ℝ} (hZ : StrictAnti Z)
    (hlim : Tendsto Z atTop (𝓝 1)) (n : ℕ) : 0 < genealogyProfileCoefficient Z n :=
  Real.sqrt_pos.mpr (genealogyProfileEnergy_pos hZ hlim n)

theorem genealogyProfileCoefficient_sq {Z : ℕ → ℝ} (hZ : Antitone Z)
    (hlim : Tendsto Z atTop (𝓝 1)) (n : ℕ) :
    genealogyProfileCoefficient Z n ^ 2 = genealogyProfileEnergy Z n :=
  Real.sq_sqrt (genealogyProfileEnergy_nonneg hZ hlim n)

theorem genealogyProfileCoefficient_bound {Z : ℕ → ℝ} (hZ : Antitone Z)
    (hlim : Tendsto Z atTop (𝓝 1)) (n : ℕ) :
    genealogyProfileCoefficient Z n ≤ Real.sqrt (4 * (Z 0 - 1)) :=
  Real.sqrt_le_sqrt (genealogyProfileEnergy_le hZ hlim n)

theorem genealogyProfileCoefficient_summable_sq {Z : ℕ → ℝ} (hZ : Antitone Z)
    (hlim : Tendsto Z atTop (𝓝 1)) : Summable (fun n => genealogyProfileCoefficient Z n ^ 2) := by
  simpa only [genealogyProfileCoefficient_sq hZ hlim] using genealogyProfileEnergy_summable hZ hlim

end
end GaloisForLFunctions.HTGeometry
