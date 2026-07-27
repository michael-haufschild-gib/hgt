import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic

/-!
# Conjugation of Mellin transforms

Complex conjugation commutes with the Mellin transform after conjugating the parameter, because the
kernel `t ^ (s-1)` has positive real base.  For a kernel that is itself conjugation invariant — a
real-valued kernel — this is the Schwarz reflection principle in Mellin form:
`conj (mellin F s) = mellin F (conj s)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Set

/-- Conjugation passes through an indicator of a conjugation-invariant function. -/
theorem conj_indicator {s : Set ℝ} {f : ℝ → ℂ} (hf : ∀ x, (starRingEnd ℂ) (f x) = f x) (t : ℝ) :
    (starRingEnd ℂ) (s.indicator f t) = s.indicator f t := by
  by_cases h : t ∈ s
  · rw [Set.indicator_of_mem h, hf]
  · rw [Set.indicator_of_notMem h, map_zero]

/-- **Conjugation of the Mellin transform.** -/
theorem mellin_conj (F : ℝ → ℂ) (s : ℂ) :
    mellin (fun t => (starRingEnd ℂ) (F t)) ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (mellin F s) := by
  rw [mellin, mellin, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have htpos : (0 : ℝ) < t := ht
  have harg : ((t : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg htpos.le]
    exact ne_of_lt Real.pi_pos
  show ((t : ℂ) ^ ((starRingEnd ℂ) s - 1)) • (starRingEnd ℂ) (F t)
      = (starRingEnd ℂ) ((t : ℂ) ^ (s - 1) • F t)
  rw [smul_eq_mul, smul_eq_mul, map_mul]
  congr 1
  have hcs : (starRingEnd ℂ) s - 1 = (starRingEnd ℂ) (s - 1) := by simp
  rw [hcs, Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

/-- **Reflection principle for a real-valued Mellin kernel.** -/
theorem mellin_conj_of_conj_invariant {F : ℝ → ℂ}
    (hF : ∀ t : ℝ, (starRingEnd ℂ) (F t) = F t) (s : ℂ) :
    mellin F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (mellin F s) := by
  have h := mellin_conj F s
  rwa [show (fun t => (starRingEnd ℂ) (F t)) = F from funext hF] at h

/-- Conjugation of a nonnegative real base raised to a complex power. -/
theorem conj_natCast_cpow_neg (n : ℕ) (s : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-s)) = (n : ℂ) ^ (-((starRingEnd ℂ) s)) := by
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    rw [show ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) by push_cast; ring,
      Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact ne_of_lt Real.pi_pos
  have h := Complex.cpow_conj (n : ℂ) (-s) harg
  rw [show (starRingEnd ℂ) ((n : ℂ)) = (n : ℂ) by simp] at h
  rw [← h, map_neg]

end GaloisForLFunctions.HTGeometry
