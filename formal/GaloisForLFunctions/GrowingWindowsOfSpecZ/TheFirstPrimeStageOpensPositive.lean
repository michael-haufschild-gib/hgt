import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheTwoCollarFormIsBornZero
import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheEvolutionStartsPositive

/-!
# The first prime stage opens positive

At the first prime stage (`N + 1 = 2`, `ℓ = log 2`) the frozen form `Q_1` is the prime-free
archimedean–polar form, the kick is `−2w₂c_H(log 2)`, `w₂ = log 2/√2`, and the two-collar form is born
zero at `A = log 2` (`twoCollarForm_birth`).

* **The race is won at the start** (`firstStage_criterion_of_le`): for every window length
  `log 2 ≤ A ≤ 181/250` the stage inequality `2w₂c_H(log 2) ≤ S^1_A(H)` holds on every window test:
  short windows are positive (SPATL), and the stage criterion turns window positivity into the
  domination of the kick by the two-collar form.
* **Exactness at the first prime** (`firstStage_kick_le_frozen`): for the same lengths
  `2w₂c_H(log 2) ≤ Q_1(H)` — the prime-free frozen form dominates the kick of the prime `2` on every test
  of these windows, even though the prime-free form alone fails at a finite aperture (DZG): the first
  kick lands inside its interval during the first `181/250 − log 2` of collar width.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open CohomologyOfWindowsOfSpecZ DimensionZeroGeometryOfSpecZ WindowTowerOfSpecZ
  SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri RHTower.WeilMarkovPole

/-- Short windows are nonnegative. -/
theorem weilQuad_nonneg_of_short {A : ℝ} (hA : A ≤ 181 / 250) {G : ℝ → ℝ}
    (hG : IsWindowTest A G) : 0 ≤ weilQuad G := by
  by_cases hG0 : G = 0
  · subst hG0
    have := weilQuad_mul_left 0 (fun _ => (0 : ℝ))
    simp only [zero_mul] at this
    rw [show (0 : ℝ → ℝ) = fun _ => 0 from rfl, this]; simp
  · exact (weilQuad_pos_of_short (mem_realTests_of_isWindowTest hG) hG0 (c := 0) hA
      (by simpa using hG.vanish)).le

theorem windowLevel_eq_two {A : ℝ} (h2 : Real.log 2 ≤ A) (h3 : A < Real.log 3) :
    windowLevel A = 1 + 1 := by
  rw [windowLevel]
  have he2 : (2 : ℝ) ≤ Real.exp A := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]; exact Real.exp_le_exp.mpr h2
  have he3 : Real.exp A < 3 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]; exact Real.exp_lt_exp.mpr h3
  have : ⌊Real.exp A⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (Real.exp_pos A).le]; constructor <;> push_cast <;> linarith
  rw [this]

theorem log_two_lt_bound : Real.log 2 < 181 / 250 := by
  have := Real.log_two_lt_d9
  norm_num at this ⊢
  linarith

theorem bound_lt_log_three : (181 / 250 : ℝ) < Real.log 3 := by
  have h := Real.log_two_gt_d9
  have h3 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  linarith

/-- **The first prime stage opens positive**: for `log 2 ≤ A ≤ 181/250`, the two-collar form of the
first stage dominates the kick of `2` on every window test. -/
theorem firstStage_criterion_of_le {A : ℝ} (h2 : Real.log 2 ≤ A) (hA : A ≤ 181 / 250)
    {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    ((2 * primeJumpWeight (1 + 1) * corr H (Real.log (1 + 1 : ℕ)) : ℝ) : EReal) ≤
      twoCollarForm 1 A H := by
  have hlev := windowLevel_eq_two h2 (lt_of_le_of_lt hA bound_lt_log_three)
  exact (stage_criterion le_rfl hlev).mp (fun G hG => weilQuad_nonneg_of_short hA hG) H hH

/-- **The prime-free frozen form dominates the first kick** on the windows `log 2 ≤ A ≤ 181/250`:
`2w₂c_H(log 2) ≤ Q_1(H)`. -/
theorem firstStage_kick_le_frozen {A : ℝ} (h2 : Real.log 2 ≤ A) (hA : A ≤ 181 / 250)
    {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    2 * primeJumpWeight (1 + 1) * corr H (Real.log (1 + 1 : ℕ)) ≤ stageForm 1 H := by
  have hlev := windowLevel_eq_two h2 (lt_of_le_of_lt hA bound_lt_log_three)
  have := weilQuad_eq_stageForm_sub_corr hH le_rfl hlev
  have hQ := weilQuad_nonneg_of_short hA hH
  linarith

end GaloisForLFunctions.GrowingWindowsOfSpecZ
