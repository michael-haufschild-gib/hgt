import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomReflectedApproximation
import GaloisForLFunctions.RHTower.ThetaCuspNativeOddSchurFarTail

/-!
# Quantitative reflected two-atom approximation through order ten

Every omitted atom stays inside the complete deep-tail majorant. The first two
atoms and all first-atom reflection cancellations remain exact.
-/
namespace RHTower
noncomputable section
set_option maxHeartbeats 1500000

/-- Complete deep-tail derivative majorant. -/
def thetaCuspDeepDerivativeBound (n : ℕ) (x : ℝ) : ℝ :=
  (16*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x

/-- Exact finite error majorant with both linear and quadratic deep-tail terms. -/
def thetaCuspTwoAtomReflectionErrorBound (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
    (|iteratedDeriv i thetaCuspTwoAtomLikelihoodPartition x| *thetaCuspDeepDerivativeBound (n-i) x+
      thetaCuspDeepDerivativeBound i x*|iteratedDeriv (n-i) thetaCuspTwoAtomLikelihoodPartition x| +
      thetaCuspDeepDerivativeBound i x*thetaCuspDeepDerivativeBound (n-i) x)

/-- The relative reflected error is bounded without replacing any retained atom derivative. -/
theorem abs_thetaCuspTwoAtomReflectionErrorJet_le {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspTwoAtomReflectionErrorJet n x| ≤ thetaCuspTwoAtomReflectionErrorBound n x := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hb (k : ℕ) (hk : k ≤ 10) :
      |iteratedDeriv k thetaCuspDeepLikelihoodRemainder x| ≤ thetaCuspDeepDerivativeBound k x :=
    abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le hk hq
  have hbp (k : ℕ) (hk : k ≤ 10) : 0 ≤ thetaCuspDeepDerivativeBound k x :=
    (abs_nonneg _).trans (hb k hk)
  rw [thetaCuspTwoAtomReflectionErrorJet_eq n hx]
  unfold thetaCuspTwoAtomReflectionErrorBound
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ 10 := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hn
  have hj : n-i ≤ 10 := (Nat.sub_le n i).trans hn
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_of_nonneg (show (0 : ℝ) ≤ (n.choose i : ℝ) from Nat.cast_nonneg _)]
  apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  calc
    _ ≤ |iteratedDeriv i thetaCuspTwoAtomLikelihoodPartition x*
          iteratedDeriv (n-i) thetaCuspDeepLikelihoodRemainder x| +
        |iteratedDeriv i thetaCuspDeepLikelihoodRemainder x*
          iteratedDeriv (n-i) thetaCuspTwoAtomLikelihoodPartition x| +
        |iteratedDeriv i thetaCuspDeepLikelihoodRemainder x*
          iteratedDeriv (n-i) thetaCuspDeepLikelihoodRemainder x| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [abs_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (hb (n-i) hj) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hb i hi') (abs_nonneg _)))
        (mul_le_mul (hb i hi') (hb (n-i) hj) (abs_nonneg _) (hbp i hi'))

/-- The full reflected source differs from its two retained atoms by this complete finite bound. -/
theorem abs_thetaCuspNativeReflectionJet_sub_two_le_factored {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeReflectionJet n x-thetaCuspTwoAtomReflectionJet n x| ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*|thetaCuspFirstAtomReflectionJet i x| *
        thetaCuspTwoAtomReflectionErrorBound (n-i) x := by
  rw [thetaCuspNativeReflectionJet_sub_two_eq_factored n (thetaCusp_pos_of_thirtySevenTenths_le hq)]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n.choose i : ℝ) from Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (abs_thetaCuspTwoAtomReflectionErrorJet_le ((Nat.sub_le n i).trans hn) hq)
    (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

/-- Signed two-atom even moment in the same normalization as the complete native Hankel section. -/
def thetaCuspTwoAtomScaledEvenJet (k : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ)^k*thetaCuspTwoAtomReflectionJet (2*k) x/
    (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^k)

/-- The normalized Hankel inputs have explicit two-atom error bars on the whole middle interval. -/
theorem abs_thetaCuspNativeScaledEvenJet_sub_two_le {k : ℕ} (hk : k ≤ 5) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet k x-thetaCuspTwoAtomScaledEvenJet k x| ≤
      (∑ i ∈ Finset.range (2*k+1), ((2*k).choose i : ℝ)*|thetaCuspFirstAtomReflectionJet i x| *
        thetaCuspTwoAtomReflectionErrorBound (2*k-i) x)/
          (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^k) := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hd : 0 < thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^k := by positivity
  have he : thetaCuspNativeScaledEvenJet k x-thetaCuspTwoAtomScaledEvenJet k x =
      (-1 : ℝ)^k*((thetaCuspNativeReflectionJet (2*k) x-thetaCuspTwoAtomReflectionJet (2*k) x)/
        (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^k)) := by
    unfold thetaCuspNativeScaledEvenJet thetaCuspTwoAtomScaledEvenJet
    ring
  rw [he, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right
    (abs_thetaCuspNativeReflectionJet_sub_two_le_factored (by omega : 2*k ≤ 10) hq) hd.le

/-- Pointwise bound beyond the compact energy endpoint, with no extra scale premise. -/
theorem abs_thetaCuspNativeScaledEvenJet_sub_two_le_on_middle {k : ℕ} (hk : k ≤ 5) {x : ℝ}
    (hx : 8/95 ≤ x) :
    |thetaCuspNativeScaledEvenJet k x-thetaCuspTwoAtomScaledEvenJet k x| ≤
      (∑ i ∈ Finset.range (2*k+1), ((2*k).choose i : ℝ)*|thetaCuspFirstAtomReflectionJet i x| *
        thetaCuspTwoAtomReflectionErrorBound (2*k-i) x)/
          (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^k) :=
  abs_thetaCuspNativeScaledEvenJet_sub_two_le hk
    (thirtySevenTenths_le_firstAtomScale_of_energy_endpoint hx)

end
end RHTower
