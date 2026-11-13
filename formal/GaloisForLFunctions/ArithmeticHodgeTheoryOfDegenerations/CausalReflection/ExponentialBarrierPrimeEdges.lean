import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineExponentialBarrierJumps

/-!
# Prime edges against exponential positive levels

The terminal support cuts off the growing exponential row at each prime
shift. Translation invariance identifies the opposite row with a decaying
multiple of the unshifted pairing.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory

/-- The two orientations of a prime edge make its mixed term symmetric. -/
theorem primePairTerm_symm (F G : ℝ → ℝ) (n : ℕ) :
    primePairTerm F G n = primePairTerm G F n := by
  have hlag (s : ℝ) : (∫ u, F u * G (u - s)) = ∫ u, G u * F (u + s) := by
    calc
      _ = ∫ u, F (u + s) * G (u + s - s) :=
        (integral_add_right_eq_self (fun u => F u * G (u - s)) s).symm
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun u => by
          dsimp only
          rw [add_sub_cancel_right, mul_comm]
  have hplus := hlag (-Real.log (n : ℝ))
  simp only [sub_neg_eq_add, ← sub_eq_add_neg] at hplus
  unfold primePairTerm
  rw [hlag, hplus, add_comm]

theorem primeMixedForm_symm (F G : ℝ → ℝ) : primeMixedForm F G = primeMixedForm G F := by
  unfold primeMixedForm
  exact tsum_congr fun n => primePairTerm_symm F G n

/-- The forward prime row is present only when its shifted endpoint remains negative. -/
theorem CriticalHalfLineEnergyDomain.exponentialBarrier_supported_edge {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t)
    (u h : ℝ) :
    F u * exponentialBarrierPositiveLevel β t F (u + h) +
      F (u + h) * exponentialBarrierPositiveLevel β t F u ≤
      Real.exp (β * h) *
        (Iio (-h)).indicator (fun v => F v * exponentialBarrierPositiveLevel β t F v) u +
      Real.exp (-(β * h)) * (F (u + h) * exponentialBarrierPositiveLevel β t F (u + h)) := by
  by_cases hu : u ∈ Iio (-h)
  · rw [indicator_of_mem hu]
    have he := hF.exponentialBarrier_edge_lower ht β u h
    nlinarith only [he]
  · have huh : 0 ≤ u + h := by
      have hh : -h ≤ u := le_of_not_gt hu
      linarith only [hh]
    rw [indicator_of_notMem hu, hF.support _ huh,
      (hF.exponentialBarrierPositiveLevel_mem hβ ht).support _ huh]
    simp only [mul_zero, zero_mul, add_zero, le_refl]

/-- Integration of one supported edge gives one truncated and one complete diagonal row. -/
theorem CriticalHalfLineEnergyDomain.exponentialBarrier_correlation_row {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) (h : ℝ) :
    (∫ u, F u * exponentialBarrierPositiveLevel β t F (u - h)) +
      (∫ u, F u * exponentialBarrierPositiveLevel β t F (u + h)) ≤
      Real.exp (β * h) * (∫ u in Iio (-h), F u * exponentialBarrierPositiveLevel β t F u) +
      Real.exp (-(β * h)) * (∫ u, F u * exponentialBarrierPositiveLevel β t F u) := by
  let G := exponentialBarrierPositiveLevel β t F
  have hG := hF.exponentialBarrierPositiveLevel_mem hβ ht
  have hFG : Integrable (fun u => F u * G u) := hF.memLp_real.integrable_mul hG.memLp_real
  have hplus : Integrable (fun u => F u * G (u + h)) := hF.memLp_real.integrable_mul
    (hG.memLp_real.comp_measurePreserving (measurePreserving_add_right volume h))
  have hback : Integrable (fun u => F (u + h) * G u) :=
    (hF.memLp_real.comp_measurePreserving (measurePreserving_add_right volume h)).integrable_mul
      hG.memLp_real
  have hind : Integrable ((Iio (-h)).indicator (fun u => F u * G u)) :=
    hFG.integrableOn.integrable_indicator measurableSet_Iio
  have hshift : Integrable (fun u => F (u + h) * G (u + h)) :=
    hFG.comp_measurePreserving (measurePreserving_add_right volume h)
  have hi := integral_mono (hplus.add hback)
    ((hind.const_mul (Real.exp (β * h))).add (hshift.const_mul (Real.exp (-(β * h)))))
    (fun u => hF.exponentialBarrier_supported_edge hβ ht u h)
  have he : (∫ u, F (u + h) * G u) = ∫ u, F u * G (u - h) := by
    calc
      _ = ∫ u, F (u + h) * G (u + h - h) := by
        simp only [add_sub_cancel_right]
      _ = _ := integral_add_right_eq_self (fun u => F u * G (u - h)) h
  have hl : (∫ u, F u * G (u + h) + F (u + h) * G u) =
      (∫ u, F u * G (u - h)) + ∫ u, F u * G (u + h) := by
    rw [integral_add hplus hback, he, add_comm]
  have hr : (∫ u, Real.exp (β * h) * (Iio (-h)).indicator (fun v => F v * G v) u +
      Real.exp (-(β * h)) * (F (u + h) * G (u + h))) =
      Real.exp (β * h) * (∫ u in Iio (-h), F u * G u) +
      Real.exp (-(β * h)) * (∫ u, F u * G u) := by
    rw [integral_add (hind.const_mul _) (hshift.const_mul _), integral_const_mul,
      integral_const_mul, integral_indicator measurableSet_Iio,
      integral_add_right_eq_self (fun u => F u * G u) h]
  rw [hl, hr] at hi
  exact hi

/-- Each prime term obeys the diagonal exponential row bound with its literal coefficient. -/
theorem CriticalHalfLineEnergyDomain.primePairTerm_exponentialBarrier_le {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t)
    {n : ℕ} (hn : 2 ≤ n) :
    primePairTerm F (exponentialBarrierPositiveLevel β t F) n ≤
      vonMangoldtAtom n *
        (Real.exp (β * Real.log (n : ℝ)) *
          (∫ u in Iio (-Real.log (n : ℝ)), F u * exponentialBarrierPositiveLevel β t F u) +
        Real.exp (-(β * Real.log (n : ℝ))) *
          (∫ u, F u * exponentialBarrierPositiveLevel β t F u)) := by
  have ha : 0 ≤ vonMangoldtAtom n := by
    rw [vonMangoldtAtom, if_pos hn]
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_left (hF.exponentialBarrier_correlation_row hβ ht (Real.log n)) ha

#print axioms CriticalHalfLineEnergyDomain.exponentialBarrier_correlation_row
#print axioms CriticalHalfLineEnergyDomain.primePairTerm_exponentialBarrier_le
#print axioms primeMixedForm_symm
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
