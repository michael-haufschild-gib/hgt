import GaloisForLFunctions.RHTower.ThetaCuspMiddleReflectedError
import GaloisForLFunctions.RHTower.ThetaCuspMiddleWeightedTail
import GaloisForLFunctions.RHTower.ThetaCuspFirstAtomMiddleProfiles

/-! # Common normalization and complete tail estimates for middle entry errors -/
namespace RHTower
noncomputable section

/-- The quadratic complete tail obeys the same weighted scale transport. -/
theorem thetaCuspDeepTailErrorScale_sq_weighted_middle {k : ℕ} (hk : k ≤ 5) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSingleAtomReflectionScale 1 x^k*thetaCuspDeepTailErrorScale x^2 ≤
      (37/10 : ℝ)^k/21000000000^2 := by
  have hp := thetaCuspDeepTailErrorScale_weighted_middle hk hq
  have h0 := thetaCuspDeepTailErrorScale_weighted_middle (k := 0) (by norm_num) hq
  norm_num only [pow_zero, one_mul] at h0
  have hδ : 0 ≤ thetaCuspDeepTailErrorScale x := by unfold thetaCuspDeepTailErrorScale; positivity
  have hm := mul_le_mul hp h0 hδ (by positivity)
  nlinarith only [hm]

/-- Recover the exact raw even-jet bound from its positive normalization. -/
theorem thetaCuspFirstAtomReflectionJet_le_of_scaled {k : ℕ} {x C : ℝ} (hx : 0 < x)
    (hb : |thetaCuspFirstAtomScaledEvenJet k x| ≤ C) :
    |thetaCuspFirstAtomReflectionJet (2*k) x| ≤
      C*thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^k := by
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale; positivity
  unfold thetaCuspFirstAtomScaledEvenJet at hb
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : 0 < thetaCuspSourceTerm x 1^2*
      thetaCuspSingleAtomReflectionScale 1 x^k)] at hb
  have h := (div_le_iff₀ (by positivity : 0 < thetaCuspSourceTerm x 1^2*
    thetaCuspSingleAtomReflectionScale 1 x^k)).mp hb
  nlinarith only [h]

/-- The complete-to-two-atom normalized error is exactly its raw error divided by positive mass. -/
theorem thetaCuspNativeScaledEvenJet_two_error_eq (k : ℕ) {x : ℝ} (hx : 0 < x) :
    |thetaCuspNativeScaledEvenJet k x-thetaCuspTwoAtomScaledEvenJet k x| =
      |thetaCuspNativeReflectionJet (2*k) x-thetaCuspTwoAtomReflectionJet (2*k) x| /
        (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^k) := by
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale; positivity
  have he : thetaCuspNativeScaledEvenJet k x-thetaCuspTwoAtomScaledEvenJet k x =
      (-1 : ℝ)^k*(thetaCuspNativeReflectionJet (2*k) x-thetaCuspTwoAtomReflectionJet (2*k) x) /
        (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^k) := by
    unfold thetaCuspNativeScaledEvenJet thetaCuspTwoAtomScaledEvenJet
    ring
  rw [he, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : 0 < thetaCuspSourceTerm x 1^2*
      thetaCuspSingleAtomReflectionScale 1 x^k)]

/-- Raw full-source reflection errors retain first-atom cancellations and the complete tail. -/
theorem abs_thetaCuspNativeReflectionJet_sub_two_le_middle {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeReflectionJet n x-thetaCuspTwoAtomReflectionJet n x| ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*|thetaCuspFirstAtomReflectionJet i x| *
        (2*(16*thetaCuspSingleAtomReflectionScale 1 x)^(n-i)*thetaCuspDeepTailErrorScale x+
          (22*thetaCuspSingleAtomReflectionScale 1 x)^(n-i)*thetaCuspDeepTailErrorScale x/50+
          5*(32*thetaCuspSingleAtomReflectionScale 1 x)^(n-i)*thetaCuspDeepTailErrorScale x^2) := by
  apply (abs_thetaCuspNativeReflectionJet_sub_two_le_factored hn hq).trans
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (thetaCuspTwoAtomReflectionErrorBound_le_middle ((Nat.sub_le n i).trans hn) hq)
    (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

end
end RHTower
