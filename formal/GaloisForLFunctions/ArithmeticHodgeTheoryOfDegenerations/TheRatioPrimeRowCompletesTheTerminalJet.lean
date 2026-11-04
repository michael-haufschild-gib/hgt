import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalConductorPairingsRetainTheDivisorJet
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePrimeRowsReadPoleProfiles

/-!
# The ratio-prime row completes the terminal divisor jet

Above half the horizon the ratio-prime row has no upward multiples.
Its exact downward divisor jet supplies the diagonal omitted by the
near-pair sum. The cancellation is finite and retains every conductor.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell BezoutValuationIncidence
  ArithmeticEffectivityTheory

/-- Above half the horizon, the literal prime row is its downward logarithmic divisor jet. -/
theorem terminal_prime_row_eq_log_sub_jet (m : ℕ) {N n : ℕ}
    (hn : 0 < n) (hnN : n ≤ N) (hhalf : N < 2 * n) :
    (∑ j ∈ Icc 1 N, weilPrimeKernel n j *
      (ramanujanLagCoefficient m j / Real.sqrt j)) =
      (Real.log n * ramanujanLagCoefficient m n - ramanujanLogDivisorJet m n) /
        Real.sqrt n := by
  have hqlo : 1 ≤ N / n := (Nat.le_div_iff_mul_le hn).mpr (by simpa using hnN)
  have hqhi : N / n ≤ 1 := by
    by_contra hh
    have htwo : 2 ≤ N / n := by omega
    have := (Nat.le_div_iff_mul_le hn).mp htwo
    omega
  have hq : N / n = 1 := Nat.le_antisymm hqhi hqlo
  have hup : poleProfileUp (ramanujanLagCoefficient m) (N / n) n = 0 := by
    simp [poleProfileUp, hq]
  have hdown : poleProfileDown (ramanujanLagCoefficient m) n =
      Real.log n * ramanujanLagCoefficient m n - ramanujanLogDivisorJet m n := by
    unfold poleProfileDown
    have he : (∑ d ∈ n.divisors, ramanujanLagCoefficient m d *
        (ArithmeticFunction.vonMangoldt (n / d) : ℝ)) =
        ∑ d ∈ n.divisors, ramanujanLagCoefficient m (n / d) *
          (ArithmeticFunction.vonMangoldt d : ℝ) :=
      (Nat.sum_divisorsAntidiagonal (n := n)
        (fun d e => ramanujanLagCoefficient m d * (ArithmeticFunction.vonMangoldt e : ℝ))).symm.trans
        (Nat.sum_divisorsAntidiagonal' (n := n)
          (fun d e => ramanujanLagCoefficient m d * (ArithmeticFunction.vonMangoldt e : ℝ)))
    rw [he]
    calc
      _ = ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d : ℝ) *
          ramanujanLagCoefficient m (n / d) := sum_congr rfl fun _ _ => mul_comm _ _
      _ = _ := sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m hn
  have hp := sum_weilPrimeKernel_poleProfile (ramanujanLagCoefficient m) hn hnN
  rw [hup, zero_add, hdown] at hp
  simpa only [poleVector, div_eq_mul_inv] using hp

/-- A near pairing with its diagonal retained. -/
def filledEndpointNearPairSum (K F : ℝ → ℝ) (w : ℝ) (N : ℕ)
    (v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
    if |Real.log j - Real.log n| ≤ 2 * w then
      F ((n : ℝ) / N) * v j * K (|Real.log j - Real.log n| / w) /
        (Real.sqrt n * Real.sqrt j)
    else 0

/-- The normalized diagonal is precisely the difference between filled and punctured pairs. -/
theorem filledEndpointNearPairSum_eq {K F : ℝ → ℝ} (hK : K 0 = 1)
    {w : ℝ} (hw : 0 ≤ w) (N : ℕ) (v : ℕ → ℝ) :
    filledEndpointNearPairSum K F w N v =
      endpointNearPairSum K F 0 2 w N (fun _ => 1) v +
        ∑ n ∈ Icc 1 N, F ((n : ℝ) / N) * v n / n := by
  unfold filledEndpointNearPairSum endpointNearPairSum
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have heq : (∑ j ∈ Icc 1 N,
      if |Real.log j - Real.log n| ≤ 2 * w then
        F ((n : ℝ) / N) * v j * K (|Real.log j - Real.log n| / w) /
          (Real.sqrt n * Real.sqrt j) else 0) =
      ∑ j ∈ Icc 1 N,
        (if 0 * w < |Real.log j - Real.log n| ∧
            |Real.log j - Real.log n| ≤ 2 * w then
          F ((n : ℝ) / N) * 1 * v j * K (|Real.log j - Real.log n| / w) /
            (Real.sqrt n * Real.sqrt j) else 0) +
        (if j = n then F ((n : ℝ) / N) * v n / n else 0) := by
    apply sum_congr rfl
    intro j hj
    by_cases hjn : j = n
    · subst j
      simp only [sub_self, abs_zero, zero_mul, lt_self_iff_false, false_and,
        if_false, zero_div, hK, mul_one, if_true, zero_add,
        show (0 : ℝ) ≤ 2 * w by positivity,
        Real.mul_self_sqrt hn0.le]
    · have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
      have hlog : 0 < |Real.log j - Real.log n| := by
        apply abs_pos.mpr
        apply sub_ne_zero.mpr
        rcases lt_or_gt_of_ne hjn with h | h
        · exact (Real.log_lt_log hj0 (by exact_mod_cast h)).ne
        · exact (Real.log_lt_log hn0 (by exact_mod_cast h)).ne'
      simp only [zero_mul, hlog, true_and, if_neg hjn, add_zero, mul_one]
  rw [heq, sum_add_distrib, sum_ite_eq', if_pos hn]

/-- Terminal weights supported above half read the exact prime-row jet before taking any limit. -/
theorem terminal_prime_pair_eq_log_sub_jet {F : ℝ → ℝ}
    (hlow : ∀ x, x ≤ (1 / 2 : ℝ) → F x = 0) {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / Real.sqrt n *
      ∑ j ∈ Icc 1 N, weilPrimeKernel n j *
        (ramanujanLagCoefficient m j / Real.sqrt j)) =
      ∑ n ∈ Icc 1 N, F ((n : ℝ) / N) *
        (Real.log n * ramanujanLagCoefficient m n - ramanujanLogDivisorJet m n) / n := by
  apply sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  by_cases hhalf : N < 2 * n
  · rw [terminal_prime_row_eq_log_sub_jet m (mem_Icc.mp hn).1 (mem_Icc.mp hn).2 hhalf]
    rw [div_mul_div_comm, Real.mul_self_sqrt hn0.le]
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hhalfR : (2 : ℝ) * n ≤ N := by exact_mod_cast (show 2 * n ≤ N by omega)
    have hx : (n : ℝ) / N ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hN0).mpr
      linarith only [hhalfR]
    rw [hlow _ hx, zero_div, zero_mul, zero_mul, zero_div]

/-- The signed ratio-prime channel fills exactly the missing divisor-jet diagonal. -/
theorem terminal_near_jet_sub_prime_pair_eq_filled
    {φ F : ℝ → ℝ} (hM : 0 < ∫ u, φ u ^ 2)
    (hlow : ∀ x, x ≤ (1 / 2 : ℝ) → F x = 0)
    {w : ℝ} (hw : 0 ≤ w) {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
        F 0 2 w N (fun _ => 1) (ramanujanLogDivisorJet m) -
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / Real.sqrt n *
        ∑ j ∈ Icc 1 N, weilPrimeKernel n j *
          (ramanujanLagCoefficient m j / Real.sqrt j)) =
      filledEndpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
        F w N (ramanujanLogDivisorJet m) -
      ∑ n ∈ Icc 1 N, F ((n : ℝ) / N) * Real.log n * ramanujanLagCoefficient m n / n := by
  have hK : (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2) 0 = 1 := by
    rw [shellAutocorr_zero, div_self hM.ne']
  rw [filledEndpointNearPairSum_eq hK hw N, terminal_prime_pair_eq_log_sub_jet hlow hN m]
  have he : (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) *
      (Real.log n * ramanujanLagCoefficient m n - ramanujanLogDivisorJet m n) / n) =
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) * Real.log n * ramanujanLagCoefficient m n / n) -
        ∑ n ∈ Icc 1 N, F ((n : ℝ) / N) * ramanujanLogDivisorJet m n / n := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [he]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.terminal_prime_row_eq_log_sub_jet
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.terminal_near_jet_sub_prime_pair_eq_filled
