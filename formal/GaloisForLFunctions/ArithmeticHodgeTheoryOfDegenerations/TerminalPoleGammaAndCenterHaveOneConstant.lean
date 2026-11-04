import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowsRetainTheSignedGammaMean
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowsRetainTheJointNearCenter
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowsReadTheNearLogarithm

/-!
# One signed constant for the terminal polar Gamma and near center

The terminal logarithm cancels between the near center and downward
prime row. The near and far Gamma constants then cancel the remaining
harmonic finite part, leaving `-log(2π)` times the terminal mean.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  BezoutValuationIncidence

/-- The four literal polar channels before the full center and upward prime row are added. -/
def terminalPolarGammaCenterPair (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  (gapMatrixPair (nearArchimedeanRemainder φ (c / N)) 0 2 (c / N) N
      (fun n => logProfile h ((n : ℝ) / N)) (fun _ => 1) -
    farCrossPair φ (c / N) N (fun n => logProfile h ((n : ℝ) / N)) (fun _ => 1)) / c +
  ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
    (nearCenterPair c N (fun n => logProfile h ((n : ℝ) / N)) (fun _ => 1) / N) -
  Real.log c * (endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
    (logProfile h) 0 2 (c / N) N (fun _ => 1) (fun _ => 1) / c) -
  endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
    (logProfile h) 0 2 (c / N) N (fun _ => 1) (fun j => Real.log ((j : ℝ) / N)) / c

/-- The complete signed sum of the polar Gamma and near-center channels retains one constant. -/
theorem tendsto_terminalPolarGammaCenterPair
    {φ h : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N * Real.log (c N) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => terminalPolarGammaCenterPair φ h (c N) N) atTop
      (𝓝 (-((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * Real.log (2 * Real.pi) *
        ∫ x in (0 : ℝ)..1, logProfile h x)) := by
  have hc0 : ∀ N, 0 < c N := fun N => zero_lt_one.trans_le (hc N)
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    have ht := he.div_atTop (Real.tendsto_log_atTop.comp hcinf)
    apply ht.congr'
    filter_upwards [(Real.tendsto_log_atTop.comp hcinf).eventually_gt_atTop 0] with N hN
    dsimp only [Function.comp_def] at hN ⊢
    field_simp [hN.ne']
  obtain ⟨BF, _, hBF, _⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨LF, hLF⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |logProfile h x - logProfile h y| ≤ ((LF : ℝ) * Real.exp (2 * A)) * |x - y| :=
    fun x _ y _ => abs_logProfile_sub_le hh hsupp hA hBF hLF x y
  have hg := tendsto_weighted_nearArchimedean_sub_farCross_pair_div_overlap
    hφ hφsupp hM (fun x => abs_logProfile_le hBF x)
    (by positivity : 0 ≤ (LF : ℝ) * Real.exp (2 * A)) hFL
    (q := 1) (u := fun _ => 1) (v := fun _ => 1) (B := 1) one_pos
    (by intros; rfl) (by intros; rfl) (by intros; norm_num) (by intros; norm_num)
    hc0 hcinf hcN
  have hmean : periodicMean (fun _ => (1 : ℝ)) 1 = 1 := by simp [periodicMean]
  simp only [hmean, mul_one] at hg
  have hone : ramanujanLagCoefficient 1 = fun _ => (1 : ℝ) :=
    funext ramanujanLagCoefficient_one
  have hn := tendsto_terminal_joint_nearCenter_finite_part hφ hφsupp hM hh hA hsupp
    (m := 1) (l := 1) one_pos one_pos hc hcinf he
  have hl := tendsto_terminal_nearLogRow hφ hφsupp hM hh hA hsupp
    (m := 1) (l := 1) one_pos one_pos hc0 hcinf hcN
  simp only [hone, and_self, if_true, mul_one, one_mul] at hn hl
  have ht := (hg.add hn).sub hl
  have hlog : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2 * Real.pi ≠ 0)]
    congr 1
    ring
  have hconst : -((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) *
        (∫ x in (0 : ℝ)..1, logProfile h x) +
      ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        ((Real.log 2 + Real.eulerMascheroniConstant) * (∫ x in (0 : ℝ)..1, logProfile h x) +
          ∫ x in (0 : ℝ)..1, logProfile (fun y => y * h y) x) -
      ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        (∫ x in (0 : ℝ)..1, logProfile (fun y => y * h y) x) =
      -((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * Real.log (2 * Real.pi) *
        ∫ x in (0 : ℝ)..1, logProfile h x := by
    rw [hlog]
    ring
  rw [hconst] at ht
  exact ht.congr fun N => by unfold terminalPolarGammaCenterPair; ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminalPolarGammaCenterPair
