import GaloisForLFunctions.HTGeometry.TwoAtomReflectedMajorant
import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomMiddleCooling

/-! # Closed middle bound for the complete reflected tail -/
namespace RHTower
noncomputable section

/-- The full reflected relative error has two linear scales and one quadratic scale. -/
theorem thetaCuspTwoAtomReflectionErrorBound_le_middle {n : ℕ} (hn : n ≤ 10)
    {x : ℝ} (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspTwoAtomReflectionErrorBound n x ≤
      2*(16*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x+
        (22*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x/50+
        5*(32*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x^2 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let δ := thetaCuspDeepTailErrorScale x
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hδ : 0 ≤ δ := by unfold δ thetaCuspDeepTailErrorScale; positivity
  have he := HTGeometry.twoAtom_reflected_majorant_eq n (6*q) (16*q) δ
  have h22 : 6*q+16*q = 22*q := by ring
  have h32 : 16*q+16*q = 32*q := by ring
  rw [h22, h32] at he
  change thetaCuspTwoAtomReflectionErrorBound n x ≤ 2*(16*q)^n*δ+(22*q)^n*δ/50+5*(32*q)^n*δ^2
  rw [← he]
  unfold thetaCuspTwoAtomReflectionErrorBound thetaCuspDeepDerivativeBound
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ 10 := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hn
  have hj : n-i ≤ 10 := (Nat.sub_le n i).trans hn
  apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  apply add_le_add _ le_rfl
  exact add_le_add
    (mul_le_mul_of_nonneg_right
      (abs_iteratedDeriv_thetaCuspTwoAtomLikelihoodPartition_le_middle hi' hq) (by positivity))
    (mul_le_mul_of_nonneg_left
      (abs_iteratedDeriv_thetaCuspTwoAtomLikelihoodPartition_le_middle hj hq) (by positivity))

/-- The literal reflected complete source obeys the collapsed relative bound. -/
theorem abs_thetaCuspTwoAtomReflectionErrorJet_le_middle {n : ℕ} (hn : n ≤ 10)
    {x : ℝ} (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspTwoAtomReflectionErrorJet n x| ≤
      2*(16*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x+
        (22*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x/50+
        5*(32*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x^2 :=
  (abs_thetaCuspTwoAtomReflectionErrorJet_le hn hq).trans
    (thetaCuspTwoAtomReflectionErrorBound_le_middle hn hq)

end
end RHTower
