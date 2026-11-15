import GaloisForLFunctions.HTGeometry.PolynomialForwardDifference

/-!
# Polynomial rigidity for the tropical second-order shift equation

For polynomial sources, the equation `P(x+1)+P(x-1)=c P(x)` has only
zero solutions or affine solutions with `c=2`. Leading coefficients fix
`c`; the exact degree drop under forward difference fixes the degree.
This is a polynomial analogue of the shift equation studied in
Cao–Korhonen–Wang, Lemma 5.2, with an exact classification in this class.
-/

open Polynomial
namespace GaloisForLFunctions.BiScaleUncertainty.TropicalPolynomialRecurrence
open _root_.HTGeometry
noncomputable section

private theorem shift_top_coeff (P : ℂ[X]) (t : ℂ) :
    (P.comp (X + C t)).coeff P.natDegree = P.leadingCoeff := by
  have h := shiftTwist_leadingCoeff (RingEquiv.refl ℂ) t P
  rw [Polynomial.leadingCoeff, shiftTwist_natDegree] at h
  simpa only [shiftTwist_refl, RingEquiv.refl_apply] using h

private theorem fwdDiff_ne_zero {P : ℂ[X]} (hP : 0 < P.natDegree) : fwdDiff P ≠ 0 := by
  intro h
  have hc := fwdDiff_coeff_sub_one hP
  rw [h, Polynomial.coeff_zero] at hc
  have hd : (P.natDegree : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hP)
  have hl : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr
    (fun hz => by simp [hz] at hP)
  exact (mul_ne_zero hd hl) hc.symm

/-- Two vanishing forward differences force affine degree. -/
theorem natDegree_le_one_of_second_difference_zero (P : ℂ[X])
    (h : fwdDiff (fwdDiff P) = 0) : P.natDegree ≤ 1 := by
  by_contra hn
  have hp : 0 < P.natDegree := by omega
  have hd : 0 < (fwdDiff P).natDegree := by rw [natDegree_fwdDiff hp]; omega
  exact fwdDiff_ne_zero hd h

private theorem affine_expansion {P : ℂ[X]} (hP : P.natDegree ≤ 1) :
    P = C (P.coeff 1) * X + C (P.coeff 0) := by
  ext k
  rcases k with _ | k
  · simp
  rcases k with _ | k
  · simp
  · have hk : P.natDegree < k + 2 := by omega
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hk]

/-- Exact classification of polynomial solutions of the centered shift equation. -/
theorem centered_shift_iff (P : ℂ[X]) (c : ℂ) :
    P.comp (X + 1) + P.comp (X - 1) = C c * P ↔
      P = 0 ∨ c = 2 ∧ P.natDegree ≤ 1 := by
  constructor
  · intro h
    by_cases hp : P = 0
    · exact Or.inl hp
    right
    have hcoeff := congrArg (fun Q : ℂ[X] => Q.coeff P.natDegree) h
    have hm : X - 1 = X + C (-1 : ℂ) := by simp only [map_neg, map_one, sub_eq_add_neg]
    have hp1 : X + 1 = X + C (1 : ℂ) := by simp
    rw [Polynomial.coeff_add, hp1, hm, shift_top_coeff, shift_top_coeff,
      Polynomial.coeff_C_mul] at hcoeff
    have hc : c = 2 := by
      have he : (c - 2) * P.leadingCoeff = 0 := by
        change P.leadingCoeff + P.leadingCoeff = c * P.leadingCoeff at hcoeff
        linear_combination -hcoeff
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right
        (Polynomial.leadingCoeff_ne_zero.mpr hp))
    refine ⟨hc, natDegree_le_one_of_second_difference_zero P ?_⟩
    apply Polynomial.funext
    intro z
    have hz := congrArg (fun Q : ℂ[X] => Q.eval (z + 1)) h
    simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      add_sub_cancel_right, hc] at hz
    simp only [fwdDiff_eval, Polynomial.eval_zero]
    linear_combination hz
  · rintro (rfl | ⟨rfl, hP⟩)
    · simp
    · rw [affine_expansion hP]
      simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, map_ofNat]
      ring

#print axioms natDegree_le_one_of_second_difference_zero
#print axioms centered_shift_iff

end
end GaloisForLFunctions.BiScaleUncertainty.TropicalPolynomialRecurrence
