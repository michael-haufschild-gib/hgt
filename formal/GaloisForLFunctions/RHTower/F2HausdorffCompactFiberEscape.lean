import GaloisForLFunctions.RHTower.PrimeArchEndpointCalibratedHausdorffRH

/-!
# F2 Hausdorff compact-fibre escape

Compact exact-zeroth normalization and complete Hausdorff positivity do not synchronize a
one-parameter source moment curve with a target moment sequence.  The source curve consists of
Dirac measures on `[0,1]`; the target is the equal mixture of the two endpoint Dirac measures.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Dirac-source moment curve on the unit interval. -/
def f2HausdorffEscapeSourceMoment (a : ℝ) (n : ℕ) : ℝ :=
  a ^ n

/-- Moment sequence of `(delta_0 + delta_1) / 2`. -/
def f2HausdorffEscapeTargetMoment : ℕ → ℝ
  | 0 => 1
  | _ + 1 => 1 / 2

/-- Compact zeroth-moment normalization and complete Hausdorff positivity on both sides do not
force one aperture to match every moment. -/
theorem f2HausdorffCompactFiberEscape :
    IsCompact (Set.Icc (0 : ℝ) 1) ∧
      (Set.Icc (0 : ℝ) 1).Nonempty ∧
      (∀ a ∈ Set.Icc (0 : ℝ) 1,
        f2HausdorffEscapeSourceMoment a 0 = f2HausdorffEscapeTargetMoment 0) ∧
      (∀ a ∈ Set.Icc (0 : ℝ) 1,
        ScaledHausdorffMomentDifferencesNonnegative 1
          (f2HausdorffEscapeSourceMoment a)) ∧
      ScaledHausdorffMomentDifferencesNonnegative 1 f2HausdorffEscapeTargetMoment ∧
      ¬ ∃ a ∈ Set.Icc (0 : ℝ) 1,
        ∀ n : ℕ, f2HausdorffEscapeSourceMoment a n = f2HausdorffEscapeTargetMoment n := by
  have hsourceDiff (a : ℝ) (k r : ℕ) :
      scaledHausdorffMomentDifference 1 (f2HausdorffEscapeSourceMoment a) k r =
        a ^ k * (1 - a) ^ r := by
    induction r generalizing k with
    | zero => simp [scaledHausdorffMomentDifference, f2HausdorffEscapeSourceMoment]
    | succ r ih =>
        rw [scaledHausdorffMomentDifference, ih k, ih (k + 1)]
        rw [pow_succ]
        ring
  have htargetDiffSucc (k r : ℕ) :
      scaledHausdorffMomentDifference 1 f2HausdorffEscapeTargetMoment k (r + 1) =
        if k = 0 then 1 / 2 else 0 := by
    induction r generalizing k with
    | zero =>
        cases k <;>
          norm_num [scaledHausdorffMomentDifference, f2HausdorffEscapeTargetMoment]
    | succ r ih =>
        rw [scaledHausdorffMomentDifference, ih k, ih (k + 1)]
        by_cases hk : k = 0
        · subst k
          norm_num
        · simp [hk]
  have hsourceNonnegative (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
      ScaledHausdorffMomentDifferencesNonnegative 1
        (f2HausdorffEscapeSourceMoment a) := by
    intro k r
    rw [hsourceDiff]
    exact mul_nonneg (pow_nonneg ha.1 k) (pow_nonneg (sub_nonneg.mpr ha.2) r)
  have htargetNonnegative :
      ScaledHausdorffMomentDifferencesNonnegative 1 f2HausdorffEscapeTargetMoment := by
    intro k r
    cases r with
    | zero =>
        cases k <;>
          norm_num [scaledHausdorffMomentDifference, f2HausdorffEscapeTargetMoment]
    | succ r =>
        rw [htargetDiffSucc]
        split <;> norm_num
  have hnoCommon :
      ¬ ∃ a ∈ Set.Icc (0 : ℝ) 1,
        ∀ n : ℕ, f2HausdorffEscapeSourceMoment a n = f2HausdorffEscapeTargetMoment n := by
    rintro ⟨a, _ha, hmatch⟩
    have h₁ := hmatch 1
    have h₂ := hmatch 2
    norm_num [f2HausdorffEscapeSourceMoment, f2HausdorffEscapeTargetMoment] at h₁ h₂
    nlinarith
  refine ⟨isCompact_Icc, Set.nonempty_Icc.mpr (by norm_num), ?_, ?_,
    htargetNonnegative, hnoCommon⟩
  · intro a ha
    simp [f2HausdorffEscapeSourceMoment, f2HausdorffEscapeTargetMoment]
  · exact hsourceNonnegative

end

end RHTower
