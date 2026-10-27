import GaloisForLFunctions.RHTower.XiLogDerivLineOneWindowLower
import GaloisForLFunctions.RHTower.XiOrderedZeroCopyEnumeration
import GaloisForLFunctions.RHTower.XiTaylorCoefficientsLogConcave
import Mathlib.Tactic

/-!
# Xi zero bands at every height

Fixed-width zero counts, reflected across the real axis when necessary,
provide a logarithmic number of zero copies at a bounded positive distance
from every ordinate.
-/

open Finset RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Every ordinate has a separated, bounded-width band containing at least
`log (|t| + 4)` Xi zero copies. -/
theorem exists_xi_zero_logarithmic_band :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ t : ℝ, ∃ F : Finset XiZeroCopy,
      (∀ q ∈ F, 1 ≤ |(q.1 : ℂ).im - t| ∧ |(q.1 : ℂ).im - t| ≤ H) ∧
      Real.log (|t| + 4) ≤ (F.card : ℝ) := by
  classical
  obtain ⟨h, hh, T₀, hT₀, hcount⟩ := exists_xiZeroCount_window_ge_log
  let H := T₀ + 2 * h + 1
  have hH : 1 ≤ H := by dsimp [H]; linarith
  refine ⟨H, hH, fun t => ?_⟩
  let T := |t| + T₀ + h + 1
  let F : Finset XiZeroCopy := xiCopiesPos (T + h) \ xiCopiesPos (T - h)
  have hT : T₀ ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hlow : 0 ≤ T - h := by dsimp [T]; linarith [abs_nonneg t]
  have hab : T - h ≤ T + h := by linarith
  have hsub : xiCopiesPos (T - h) ⊆ xiCopiesPos (T + h) := by
    intro q hq
    exact mem_xiCopiesPos.mpr
      ⟨(mem_xiCopiesPos.mp hq).1.trans hab, (mem_xiCopiesPos.mp hq).2⟩
  have hcardlo : ((xiCopiesPos (T - h)).card : ℝ) = (xiZeroCount (T - h) : ℝ) := by
    exact_mod_cast intCast_card_xiCopiesPos hlow
  have hcardhi : ((xiCopiesPos (T + h)).card : ℝ) = (xiZeroCount (T + h) : ℝ) := by
    exact_mod_cast intCast_card_xiCopiesPos (hlow.trans hab)
  have hcard : (F.card : ℝ) =
      (xiZeroCount (T + h) : ℝ) - (xiZeroCount (T - h) : ℝ) := by
    dsimp only [F]
    rw [Finset.cast_card_sdiff hsub, hcardhi, hcardlo]
  have hmany : Real.log (|t| + 4) ≤ (F.card : ℝ) := by
    calc
      _ ≤ Real.log T := Real.log_le_log (by positivity) (by dsimp [T]; linarith only [hT₀, hh])
      _ ≤ (xiZeroCount (T + h) : ℝ) - (xiZeroCount (T - h) : ℝ) := hcount T hT
      _ = (F.card : ℝ) := hcard.symm
  have hband : ∀ q ∈ F, 1 ≤ (q.1 : ℂ).im - |t| ∧
      (q.1 : ℂ).im - |t| ≤ H := by
    intro q hq
    have hq' : q ∈ xiCopiesPos (T + h) ∧ q ∉ xiCopiesPos (T - h) := by
      simpa [F] using hq
    have ⟨hqhi, hqpos⟩ := mem_xiCopiesPos.mp hq'.1
    rw [abs_of_pos hqpos] at hqhi
    have hqlo : T - h < (q.1 : ℂ).im := by
      by_contra h
      apply hq'.2
      apply mem_xiCopiesPos.mpr
      exact ⟨by rw [abs_of_pos hqpos]; linarith only [h], hqpos⟩
    dsimp only [T, H] at *
    constructor <;> linarith only [hqlo, hqhi, hT₀, hh]
  by_cases ht : 0 ≤ t
  · refine ⟨F, ?_, hmany⟩
    intro q hq
    have hqband := hband q hq
    have ht' : |t| = t := abs_of_nonneg ht
    have hnonneg : 0 ≤ (q.1 : ℂ).im - t := by rw [← ht']; linarith [hqband.1]
    rw [abs_of_nonneg hnonneg, ← ht']
    exact hqband
  · refine ⟨F.map xiZeroCopyConjEquiv.toEmbedding, ?_, ?_⟩
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hq
      have hrband := hband r hr
      have ht' : t < 0 := lt_of_not_ge ht
      have him : ((xiZeroCopyConjEquiv r).1 : ℂ).im = -(r.1 : ℂ).im := by
        rw [xiZeroCopyConjEquiv_coe]
        simp
      have heq : -(r.1 : ℂ).im - t = -((r.1 : ℂ).im - |t|) := by
        rw [abs_of_neg ht']
        ring
      change 1 ≤ |((xiZeroCopyConjEquiv r).1 : ℂ).im - t| ∧
        |((xiZeroCopyConjEquiv r).1 : ℂ).im - t| ≤ H
      rw [him, heq, abs_neg, abs_of_nonneg (by linarith [hrband.1])]
      exact hrband
    · simpa only [Finset.card_map] using hmany

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
