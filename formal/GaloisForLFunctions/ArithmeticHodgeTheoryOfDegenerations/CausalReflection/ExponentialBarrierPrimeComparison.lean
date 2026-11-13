import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ExponentialBarrierPrimeEdges
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ExponentialBarrierPrimeRows

/-!
# The complete prime form against an exponential positive level

Finite edge sums are bounded by the support-restricted growing row and the
summable backward row. Absolute summability in the actual weighted domain
passes this estimate to the full prime mixed form.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory

/-- Every exponential positive level obeys the complete prime-row bound on the actual domain. -/
theorem CriticalHalfLineEnergyDomain.primeMixedForm_exponentialBarrier_le {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {β t : ℝ}
    (hβ : 1 / 2 < β) (hβ8 : β < 15 / 2) (ht : 0 ≤ t) :
    primeMixedForm F (exponentialBarrierPositiveLevel β t F) ≤
      ∫ u, (6 * Real.exp (-((β + 1 / 2) * u)) + halfLineExponentialPrimeTail β) *
        (F u * exponentialBarrierPositiveLevel β t F u) := by
  classical
  have hβ0 : 0 < β := by linarith only [hβ]
  let G := exponentialBarrierPositiveLevel β t F
  let H : ℝ → ℝ := fun u => F u * G u
  have hG := hF.exponentialBarrierPositiveLevel hβ0 ht
  have hH : Integrable H := hF.memLp_real.integrable_mul hG.memLp_real
  have hH0 (u : ℝ) : 0 ≤ H u := hF.mul_exponentialBarrierPositiveLevel_nonneg ht β u
  have hHe : Integrable (fun u => H u * Real.exp (-((β + 1 / 2) * u))) :=
    hF.integrable_mul_exponentialBarrierPositiveLevel ht (by linarith only [hβ8]) β
  let A : ℕ → ℝ := fun n => vonMangoldtAtom n * Real.exp (β * Real.log (n : ℝ))
  let B : ℕ → ℝ := fun n => vonMangoldtAtom n * Real.exp (-(β * Real.log (n : ℝ)))
  let q : ℕ → ℝ → ℝ := fun n u =>
    A n * (Iio (-Real.log (n : ℝ))).indicator H u + B n * H u
  have hq (n : ℕ) : Integrable (q n) :=
    ((hH.indicator measurableSet_Iio).const_mul (A n)).add (hH.const_mul (B n))
  have hqint (n : ℕ) : (∫ u, q n u) =
      A n * (∫ u in Iio (-Real.log (n : ℝ)), H u) + B n * ∫ u, H u := by
    calc
      _ = (∫ u, A n * (Iio (-Real.log (n : ℝ))).indicator H u) +
          ∫ u, B n * H u :=
        integral_add ((hH.indicator measurableSet_Iio).const_mul (A n)) (hH.const_mul (B n))
      _ = _ := by
        rw [integral_const_mul, integral_const_mul, integral_indicator measurableSet_Iio]
  have hterm (n : ℕ) : primePairTerm F G n ≤ ∫ u, q n u := by
    have ha : 0 ≤ vonMangoldtAtom n := by
      unfold vonMangoldtAtom
      split_ifs
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
      · exact le_rfl
    have hc := mul_le_mul_of_nonneg_left
      (hF.exponentialBarrier_correlation_row hβ0 ht (Real.log (n : ℝ))) ha
    change primePairTerm F G n ≤ vonMangoldtAtom n *
      (Real.exp (β * Real.log (n : ℝ)) * (∫ u in Iio (-Real.log (n : ℝ)), H u) +
        Real.exp (-(β * Real.log (n : ℝ))) * (∫ u, H u)) at hc
    refine hc.trans_eq ?_
    rw [hqint]
    dsimp only [A, B]
    ring
  have hrow : Integrable (fun u =>
      (6 * Real.exp (-((β + 1 / 2) * u)) + halfLineExponentialPrimeTail β) * H u) := by
    apply ((hHe.const_mul 6).add (hH.const_mul (halfLineExponentialPrimeTail β))).congr
    exact Eventually.of_forall fun u => by dsimp only; ring
  unfold primeMixedForm
  apply (summable_primePairTerm hF.weighted hG.weighted).tsum_le_of_sum_le
  intro s
  calc
    _ ≤ ∑ n ∈ s, ∫ u, q n u := Finset.sum_le_sum fun n _ => hterm n
    _ = ∫ u, ∑ n ∈ s, q n u := (integral_finsetSum s (fun n _ => hq n)).symm
    _ ≤ _ := by
      apply integral_mono (integrable_finsetSum s (fun n _ => hq n)) hrow
      intro u
      have he : (∑ n ∈ s, q n u) =
          (∑ n ∈ s, if u < -Real.log (n : ℝ) then A n else 0) * H u +
            (∑ n ∈ s, B n) * H u := by
        dsimp only [q]
        rw [Finset.sum_add_distrib]
        congr 1
        · calc
            _ = ∑ n ∈ s, (if u < -Real.log (n : ℝ) then A n else 0) * H u := by
              apply Finset.sum_congr rfl
              intro n _
              by_cases hu : u < -Real.log (n : ℝ)
              · simp only [indicator_of_mem hu, if_pos hu]
              · simp only [indicator_of_notMem hu, if_neg hu, mul_zero, zero_mul]
            _ = _ := (Finset.sum_mul s _ _).symm
        · exact (Finset.sum_mul s _ _).symm
      rw [he]
      calc
        _ ≤ (6 * Real.exp (-((β + 1 / 2) * u))) * H u +
            halfLineExponentialPrimeTail β * H u :=
          add_le_add
            (mul_le_mul_of_nonneg_right (sum_exponentialBarrier_prime_forward_le hβ.le s u) (hH0 u))
            (mul_le_mul_of_nonneg_right (sum_exponentialBarrier_prime_backward_le hβ s) (hH0 u))
        _ = _ := by ring

#print axioms CriticalHalfLineEnergyDomain.primeMixedForm_exponentialBarrier_le
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
