import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalNearPairsRetainLogarithmicAccuracy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowsRetainTheNearCenterFinitePart
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheNearBlockAlongAGrowingOverlap

/-!
# The joint near-center finite part against a terminal window

The actual near Gram may replace its polar limit inside a logarithmic
subtraction. The remaining near center retains the terminal logarithm
and the diagonal von Mangoldt charge.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence
open RenormalizedArithmeticPotentialTheory.CompletedShell
open ArithmeticFunction (vonMangoldt)

/-- The shell near Gram against a compact terminal window has a logarithmically small error. -/
theorem tendsto_log_mul_terminal_shell_nearGram_error
    {φ h : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N * Real.log (c N) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.log (c N) *
      (endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
          (logProfile h) 0 2 (c N / N) N
          (ramanujanLagCoefficient l) (ramanujanLagCoefficient m) / c N -
        (if m = 1 ∧ l = 1 then ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
          ∫ x in (0 : ℝ)..1, logProfile h x else 0))) atTop (𝓝 0) := by
  obtain ⟨LK, hLK0, hK, hKL⟩ := exists_shellKernel_bounds hφ hφsupp hM
  obtain ⟨BF, _, hBF, _⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨LF, hLF⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |logProfile h x - logProfile h y| ≤ ((LF : ℝ) * Real.exp (2 * A)) * |x - y| :=
    fun x _ y _ => abs_logProfile_sub_le hh hsupp hA hBF hLF x y
  have ht := tendsto_log_mul_endpointNearPairSum_ramanujan_relative_error
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) < 2) hK hKL hLK0
    (fun x => abs_logProfile_le hBF x) (by positivity : 0 ≤ (LF : ℝ) * Real.exp (2 * A))
    hFL hl hm hc hcinf he
  have hmass : 2 * (∫ s in (0 : ℝ)..2, shellAutocorr φ s / ∫ u, φ u ^ 2) =
      (∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 := by
    rw [integral_shellKernel hφ hφsupp hM]
    field_simp
  simpa only [hmass, and_comm] using ht

/-- Subtracting the logarithm times the actual terminal near Gram leaves the signed
near-center finite part. No critical-ratio restriction is required. -/
theorem tendsto_terminal_joint_nearCenter_finite_part
    {φ h : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N * Real.log (c N) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        (nearCenterPair (c N) N
          (fun n => logProfile h ((n : ℝ) / N) * ramanujanLagCoefficient l n)
          (ramanujanLagCoefficient m) / N) -
      Real.log (c N) *
        (endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
          (logProfile h) 0 2 (c N / N) N
          (ramanujanLagCoefficient l) (ramanujanLagCoefficient m) / c N))
      atTop (𝓝 (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        (if m = l then
          (if m = 1 then (Real.log 2 + Real.eulerMascheroniConstant) *
              (∫ x in (0 : ℝ)..1, logProfile h x) +
              ∫ x in (0 : ℝ)..1, logProfile (fun y => y * h y) x
            else -vonMangoldt m * ∫ x in (0 : ℝ)..1, logProfile h x) else 0))) := by
  have hc0 : ∀ N, 0 < c N := fun N => zero_lt_one.trans_le (hc N)
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    have ht := he.div_atTop (Real.tendsto_log_atTop.comp hcinf)
    apply ht.congr'
    filter_upwards [(Real.tendsto_log_atTop.comp hcinf).eventually_gt_atTop 0] with N hN
    dsimp only [Function.comp_def] at hN ⊢
    field_simp [hN.ne']
  have hcenter := tendsto_terminal_nearCenterPair_finite_part hh hA hsupp hm hl hc0 hcinf hcN
  have hnear := tendsto_log_mul_terminal_shell_nearGram_error
    hφ hφsupp hM hh hA hsupp hm hl hc hcinf he
  have ht := (hcenter.const_mul ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2)).sub hnear
  simp only [sub_zero] at ht
  apply ht.congr
  intro N
  split_ifs <;> ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_log_mul_terminal_shell_nearGram_error
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_joint_nearCenter_finite_part
