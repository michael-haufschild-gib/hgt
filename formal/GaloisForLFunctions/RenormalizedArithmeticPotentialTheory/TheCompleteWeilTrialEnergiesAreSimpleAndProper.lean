import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAdjunctionEnergyHasFiniteSublevels
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanFinitePartIsMinusLogTwoPi
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheConductorTwoIsTheFirstExcitation
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing
import GaloisForLFunctions.HTGeometry.IntegerLogGap

/-!
# The complete Weil trial energies are simple and proper

The shape fixes a common Robin offset. The joint archimedean-pole correction
shifts only conductor one by its squared charge. The charge is at most the
width ratio, below the first arithmetic excitation throughout strict separation;
all other distinctions and logarithmic properness are inherited from adjunction.
-/

noncomputable section

open MeasureTheory Finset
open scoped Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis

/-- The common self-energy finite part at width ratio `c`. -/
def completeWeilSelfFinitePart (φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  Real.log (1 / (2 * Real.pi * c)) + bumpRobin φ 1 / (∫ u, φ u ^ 2)

/-- The limiting joint pole shift, determined by the profile's signed charge. -/
def completeWeilPoleShift (φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  c * (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)

/-- The explicit complete-Weil trial energy attached to a positive conductor. -/
def completeWeilAdjunctionEnergy (φ : ℝ → ℝ) (c : ℝ) (m : ℕ) : ℝ :=
  completeWeilSelfFinitePart φ c + ramanujanAdjunctionEnergy m - Real.eulerMascheroniConstant +
    if m = 1 then completeWeilPoleShift φ c else 0

theorem completeWeilPoleShift_nonneg (φ : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ completeWeilPoleShift φ c := by
  unfold completeWeilPoleShift
  exact div_nonneg (mul_nonneg hc (sq_nonneg _)) (integral_nonneg fun u => sq_nonneg (φ u))

/-- The normalized charge square is at most the support length. -/
theorem completeWeilPoleShift_le {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 ≤ c) : completeWeilPoleShift φ c ≤ c := by
  have hL := ArithmeticLorentzianGeometry.sq_integral_abs_le hφ hφsupp zero_lt_one
  rw [one_mul] at hL
  have hI : |∫ u, φ u| ≤ ∫ u, |φ u| := abs_integral_le_integral_abs
  have hA : 0 ≤ ∫ u, |φ u| := integral_nonneg fun u => abs_nonneg (φ u)
  have hs : (∫ u, φ u) ^ 2 ≤ ∫ u, φ u ^ 2 := by
    nlinarith only [hL, sq_abs (∫ u, φ u),
      mul_nonneg (sub_nonneg.mpr hI) (add_nonneg hA (abs_nonneg (∫ u, φ u)))]
  rw [completeWeilPoleShift, div_le_iff₀ hφ0]
  exact mul_le_mul_of_nonneg_left hs hc

/-- The pole shift stays strictly below the first nontrivial arithmetic excitation. -/
theorem completeWeilAdjunctionEnergy_one_lt {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) {m : ℕ} (hm : 2 ≤ m) :
    completeWeilAdjunctionEnergy φ c 1 < completeWeilAdjunctionEnergy φ c m := by
  have hα : completeWeilPoleShift φ c < 1 :=
    (completeWeilPoleShift_le hφ hφsupp hφ0 hc0).trans_lt hc1
  have hlog : 1 ≤ 2 * Real.log 2 := by
    have h := HTGeometry.one_sub_inv_le_log (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith only [h]
  have hgap := (SelectiveMultiscaleArithmeticPositivity.ramanujanAdjunctionEnergy_sub_one_ge hm).1
  rw [completeWeilAdjunctionEnergy, completeWeilAdjunctionEnergy, if_pos rfl,
    if_neg (by omega), add_zero]
  linarith only [hα, hlog, hgap]

/-- Distinct positive conductors have distinct complete-Weil trial energies. -/
theorem completeWeilAdjunctionEnergy_injectiveOn {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Set.InjOn (completeWeilAdjunctionEnergy φ c) {m : ℕ | 0 < m} := by
  intro m hm n hn he
  change 0 < m at hm
  change 0 < n at hn
  by_cases hm1 : m = 1
  · subst m
    by_contra hn1
    have h := completeWeilAdjunctionEnergy_one_lt hφ hφsupp hφ0 hc0 hc1 (by omega : 2 ≤ n)
    exact (ne_of_lt h) he
  · by_cases hn1 : n = 1
    · subst n
      have h := completeWeilAdjunctionEnergy_one_lt hφ hφsupp hφ0 hc0 hc1 (by omega : 2 ≤ m)
      exact False.elim ((ne_of_lt h) he.symm)
    · apply ramanujanAdjunctionEnergy_injectiveOn hm hn
      simp only [completeWeilAdjunctionEnergy, if_neg hm1, if_neg hn1, add_zero] at he
      linarith only [he]

/-- Shifting one conductor does not destroy properness of the arithmetic energies. -/
theorem finite_completeWeilAdjunctionEnergy_sublevel (φ : ℝ → ℝ) (c T : ℝ) :
    {m : ℕ | 0 < m ∧ completeWeilAdjunctionEnergy φ c m < T}.Finite := by
  let S := {m : ℕ | 0 < m ∧ ramanujanAdjunctionEnergy m <
    T - completeWeilSelfFinitePart φ c + Real.eulerMascheroniConstant}
  have hS : S.Finite := finite_ramanujanAdjunctionEnergy_sublevel _
  refine (hS.union (Set.finite_singleton 1)).subset ?_
  intro m hm
  by_cases hm1 : m = 1
  · exact Or.inr (Set.mem_singleton_iff.mpr hm1)
  · apply Or.inl
    refine ⟨hm.1, ?_⟩
    have h := hm.2
    simp only [completeWeilAdjunctionEnergy, if_neg hm1, add_zero] at h
    linarith only [h]

/-- The finite conductor set below a complete-Weil trial threshold. -/
def completeWeilEnergySublevel (φ : ℝ → ℝ) (c T : ℝ) : Finset ℕ :=
  (finite_completeWeilAdjunctionEnergy_sublevel φ c T).toFinset

@[simp] theorem mem_completeWeilEnergySublevel (φ : ℝ → ℝ) (c T : ℝ) (m : ℕ) :
    m ∈ completeWeilEnergySublevel φ c T ↔ 0 < m ∧ completeWeilAdjunctionEnergy φ c m < T := by
  simp only [completeWeilEnergySublevel, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
