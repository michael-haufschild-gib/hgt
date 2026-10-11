import GaloisForLFunctions.RHTower.WeilLogShiftRawOrder
import GaloisForLFunctions.RHTower.WeilLogShiftRawLipschitzComparison
import Mathlib.Data.Finset.Max

/-! An absolute-value potential calibrates every pair in the canonical raw coupling. -/

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalRaw_exists_potential_center (r k : ℕ) :
    ∃ c : ℝ, ∀ i : Fin (r + 1),
      dist (finiteWeilCanonicalRawIndexValue r k i) c -
        dist (finiteWeilCanonicalRawCorrectionValue r k i) c =
          dist (finiteWeilCanonicalRawIndexValue r k i) (finiteWeilCanonicalRawCorrectionValue r k i) := by
  classical
  let X := finiteWeilCanonicalRawIndexValue r k
  let Y := finiteWeilCanonicalRawCorrectionValue r k
  have hY : Monotone Y := finiteWeilCanonicalRawCorrectionValue_monotone r k
  have he : Monotone (fun i => X i - Y i) := finiteWeilCanonicalRawDefect_monotone r k
  have right (x y c : ℝ) (hcy : c ≤ y) (hyx : y ≤ x) :
      dist x c - dist y c = dist x y := by
    rw [Real.dist_eq, Real.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (hcy.trans hyx)),
      abs_of_nonneg (sub_nonneg.mpr hcy), abs_of_nonneg (sub_nonneg.mpr hyx)]
    ring
  have left (x y c : ℝ) (hxy : x ≤ y) (hyc : y ≤ c) :
      dist x c - dist y c = dist x y := by
    rw [Real.dist_eq, Real.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (hxy.trans hyc)),
      abs_of_nonpos (sub_nonpos.mpr hyc), abs_of_nonpos (sub_nonpos.mpr hxy)]
    ring
  let s : Finset (Fin (r + 1)) := Finset.univ.filter (fun i => 0 ≤ X i - Y i)
  by_cases hs : s.Nonempty
  · let j := s.min' hs
    have hj : 0 ≤ X j - Y j := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
    refine ⟨Y j, ?_⟩
    intro i
    by_cases hi : 0 ≤ X i - Y i
    · have hmem : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      have hji : j ≤ i := Finset.min'_le s i hmem
      exact right (X i) (Y i) (Y j) (hY hji) (sub_nonneg.mp hi)
    · have hij : i ≤ j := by
        by_contra hij
        exact hi (hj.trans (he (le_of_lt (lt_of_not_ge hij))))
      exact left (X i) (Y i) (Y j) (le_of_lt (sub_neg.mp (lt_of_not_ge hi))) (hY hij)
  · refine ⟨Y (Fin.last r), ?_⟩
    intro i
    have hi : X i ≤ Y i := by
      apply le_of_lt
      apply sub_neg.mp
      apply lt_of_not_ge
      intro hi
      exact hs ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    exact left (X i) (Y i) (Y (Fin.last r)) hi (hY (Fin.le_last i))

def finiteWeilCanonicalRawPotentialCenter (r k : ℕ) : ℝ :=
  Classical.choose (finiteWeilCanonicalRaw_exists_potential_center r k)

def finiteWeilCanonicalRawPotential (r k : ℕ) (x : ℝ) : ℝ :=
  dist x (finiteWeilCanonicalRawPotentialCenter r k)

theorem finiteWeilCanonicalRawPotential_lipschitz (r k : ℕ) :
    LipschitzWith 1 (finiteWeilCanonicalRawPotential r k) :=
  LipschitzWith.dist_left _

theorem finiteWeilCanonicalRawPotential_calibration (r k : ℕ) (i : Fin (r + 1)) :
    finiteWeilCanonicalRawPotential r k (finiteWeilCanonicalRawIndexValue r k i) -
      finiteWeilCanonicalRawPotential r k (finiteWeilCanonicalRawCorrectionValue r k i) =
        |finiteWeilCanonicalFluctuationResidualValue r k i| := by
  calc
    _ = dist (finiteWeilCanonicalRawIndexValue r k i) (finiteWeilCanonicalRawCorrectionValue r k i) :=
      Classical.choose_spec (finiteWeilCanonicalRaw_exists_potential_center r k) i
    _ = _ := by
      rw [Real.dist_eq, abs_sub_comm]
      rfl

theorem finiteWeilCanonicalRawPotential_integral_gap (r k : ℕ) :
    (∫ x, finiteWeilCanonicalRawPotential r k x ∂(finiteWeilCanonicalRawIndexLaw r k : Measure ℝ)) -
      (∫ x, finiteWeilCanonicalRawPotential r k x ∂(finiteWeilCanonicalRawCorrectionLaw r k : Measure ℝ)) =
        finiteWeilCanonicalRawFluctuationGap r k := by
  rw [finiteWeilCanonicalRawIndexLaw, finiteWeilCanonicalRawCorrectionLaw,
    finiteWeilCanonicalObservableLaw_integral_real, finiteWeilCanonicalObservableLaw_integral_real,
    ← Finset.sum_sub_distrib]
  unfold finiteWeilCanonicalRawFluctuationGap
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_sub, finiteWeilCanonicalRawPotential_calibration]

end RHTower
