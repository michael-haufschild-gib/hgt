import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowsReadTheNonpolarCenter
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWeightsReadEitherEndOfANearPair
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNearGammaAndDownwardPrimeRowsCancel
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheNearBlockAlongAGrowingOverlap

/-!
# The terminal divisor jet cancels the nonpolar center charge

The near divisor jet has mean `Λ(m)` against the untwisted terminal
receiver. Its charge is exactly opposite to the harmonic pole charge
in the full center, including each prime-power conductor.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory.CompletedShell
open ArithmeticFunction (vonMangoldt)

/-- The terminal near-jet mean retains its exact von Mangoldt charge. -/
theorem tendsto_terminal_nearDivisorJet_mean
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {m : ℕ} (hm : 0 < m)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => endpointNearPairSum
      (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2) F 0 2 (c N / N) N
      (fun _ => 1) (ramanujanLogDivisorJet m) / c N)
      atTop (𝓝 (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        vonMangoldt m * ∫ x in (0 : ℝ)..1, F x)) := by
  obtain ⟨LK, hLK0, hK, hKL⟩ := exists_shellKernel_bounds hφ hφsupp hM
  have hJ0 : 0 ≤ ramanujanJetBound m := by
    unfold ramanujanJetBound
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hu : ∀ n : ℕ, |(1 : ℝ)| ≤ 1 + ramanujanJetBound m := by
    intro n
    simpa only [abs_one] using le_add_of_nonneg_right hJ0
  have hv : ∀ n, |ramanujanLogDivisorJet m n| ≤ 1 + ramanujanJetBound m :=
    fun n => (abs_ramanujanLogDivisorJet_le m n).trans
      (le_add_of_nonneg_left zero_le_one)
  have hmain := tendsto_endpointNearPairSum_div_overlap
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) < 2) hK hKL hLK0 hF hLF hFL hm
    (u := fun _ => 1) (v := ramanujanLogDivisorJet m)
    (by intros; rfl) (ramanujanLogDivisorJet_add m) hu hv hc hcinf hcN
  have hmu : periodicMean (fun _ => (1 : ℝ)) m = 1 := by
    simp only [periodicMean, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact div_self (by exact_mod_cast hm.ne')
  have hmv : periodicMean (ramanujanLogDivisorJet m) m = vonMangoldt m := by
    simpa only [one_mul] using periodicMean_ramanujanLogDivisorJet hm one_pos
  rw [hmu, hmv, integral_shellKernel hφ hφsupp hM] at hmain
  have heq : 2 * 1 * vonMangoldt m * ((∫ u, φ u) ^ 2 / (2 * ∫ u, φ u ^ 2)) *
      (∫ x in (0 : ℝ)..1, F x) = ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        vonMangoldt m * ∫ x in (0 : ℝ)..1, F x := by
    field_simp [hM.ne'] <;> ring
  rwa [heq] at hmain

/-- The signed sum of the full nonpolar center and its terminal divisor jet has zero limit. -/
theorem tendsto_terminal_nonpolar_center_add_jet
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|)
    {m : ℕ} (hm : 2 ≤ m)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        ((∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          F ((n : ℝ) / N) * BezoutValuationIncidence.ramanujanLagCoefficient m j *
            centerKernel n j) / N) +
      endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2) F 0 2 (c N / N) N
        (fun _ => 1) (ramanujanLogDivisorJet m) / c N) atTop (𝓝 0) := by
  have hcenter := (tendsto_terminal_nonpolar_centerKernel_mean hF hLF hFL hm).const_mul
    ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2)
  have hjet := tendsto_terminal_nearDivisorJet_mean hφ hφsupp hM hF hLF
    (fun x _ y _ => hFL x y) (by omega : 0 < m) hc hcinf hcN
  have ht := hcenter.add hjet
  have heq : ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        (-vonMangoldt m * ∫ x in (0 : ℝ)..1, F x) +
      ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * vonMangoldt m * ∫ x in (0 : ℝ)..1, F x = 0 := by ring
  rwa [heq] at ht

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_nearDivisorJet_mean
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_nonpolar_center_add_jet
