import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryMoments

/-!
# An exact arbitrarily delayed obstruction in actual geometric recovery costs

A monic shifted Chebyshev square has a small base integral. The first actual
geometric cost reduction outweighs that integral. A symbolic dyadic estimate
closes the sign for every family index, with no numerical certificates.
The first negative-square degree is exactly the prescribed dyadic degree;
no positive measure on the real line represents these geometric moments.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial Set MeasureTheory
open _root_.HTGeometry

def recoveryMomentWitness (d : ℕ) : ℝ[X] :=
  C (2/(16 : ℝ)^(d+1)) * (Chebyshev.T ℝ ((d+1 : ℕ) : ℤ)).comp (C 8*X-1)

theorem recoveryMomentWitness_degree (d : ℕ) : (recoveryMomentWitness d).natDegree = d+1 := by
  have hq : (C 8*X-1 : ℝ[X]).natDegree = 1 := by
    change (C 8*X-C 1 : ℝ[X]).natDegree = 1
    rw [natDegree_sub_C, natDegree_C_mul_X _ (by linarith)]
  rw [recoveryMomentWitness, natDegree_C_mul (by positivity), natDegree_comp,
    Chebyshev.natDegree_T, Int.natAbs_natCast, hq, mul_one]

theorem recoveryMomentWitness_monic (d : ℕ) : (recoveryMomentWitness d).Monic := by
  have hq : (C 8*X-1 : ℝ[X]).natDegree = 1 := by
    change (C 8*X-C 1 : ℝ[X]).natDegree = 1
    rw [natDegree_sub_C, natDegree_C_mul_X _ (by linarith)]
  have hqc : (C 8*X-1 : ℝ[X]).leadingCoeff = 8 := by
    rw [← coeff_natDegree, hq]
    simp [Polynomial.coeff_one]
  change (recoveryMomentWitness d).leadingCoeff = 1
  rw [recoveryMomentWitness, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_comp (by rw [hq]; omega), Chebyshev.leadingCoeff_T,
    Chebyshev.natDegree_T, Int.natAbs_natCast, Nat.add_sub_cancel, hqc]
  have he : (2 : ℝ)^d*8^d=16^d := by rw [← mul_pow]; congr 1; ring
  rw [pow_succ, pow_succ]
  field_simp
  nlinarith [he]

theorem recoveryMomentWitness_square_bound (d : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (1/4)) :
    ((recoveryMomentWitness d).eval x)^2 ≤ 4/(16 : ℝ)^(2*(d+1)) := by
  have hb := Chebyshev.abs_eval_T_real_le_one ((d+1 : ℕ) : ℤ)
    (show |8*x-1| ≤ 1 by rw [abs_le]; constructor <;> linarith [hx.1,hx.2])
  have hs : ((Chebyshev.T ℝ ((d+1 : ℕ) : ℤ)).eval (8*x-1))^2 ≤ 1 := by
    nlinarith [abs_le.mp hb]
  simp only [recoveryMomentWitness, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_one]
  have h := mul_le_mul_of_nonneg_left hs (sq_nonneg (2/(16 : ℝ)^(d+1)))
  rw [mul_one] at h
  have he : (2/(16 : ℝ)^(d+1))^2=4/(16 : ℝ)^(2*(d+1)) := by
    rw [div_pow, ← pow_mul]
    congr 1 <;> ring
  rw [mul_pow, ← he]
  exact h

theorem recoveryMomentWitness_base_bound (d : ℕ) :
    momentFunctional recoveryWedgeMoment ((recoveryMomentWitness d)^2) ≤
      4/(16 : ℝ)^(2*(d+1)) := by
  apply recoveryWedgeMoment_eval_le
  intro x hx
  rw [eval_pow]
  exact recoveryMomentWitness_square_bound d x hx

theorem recoverySurgeryMoment_drop_loss (n : ℕ) :
    recoverySurgeryMoment n (n+1)-recoveryWedgeMoment (n+1) ≤
      -1/(32*(n+2 : ℝ)^5*(4 : ℝ)^(n+1)) := by
  have he := recoverySurgeryEpsilon_pos n
  have he1 := recoverySurgeryEpsilon_lt_one n
  have hh : (recoverySurgeryHeight n)^2-1 ≤ -recoverySurgeryEpsilon n/2 := by
    unfold recoverySurgeryHeight
    nlinarith
  have h := mul_le_mul_of_nonneg_right hh (le_of_lt (recoveryWedgeMoment_positive (n+1)))
  have hid : (-recoverySurgeryEpsilon n/2)*recoveryWedgeMoment (n+1) =
      -1/(32*(n+2 : ℝ)^5*(4 : ℝ)^(n+1)) := by
    unfold recoverySurgeryEpsilon recoveryWedgeMoment
    push_cast
    field_simp
    ring
  rw [hid] at h
  nlinarith [recoverySurgeryMoment_drop_upper n]

theorem recoveryMomentWitness_negative_of_large (d : ℕ)
    (hd : 128*(2*d+3 : ℝ)^5 < (4 : ℝ)^(2*(d+1))) :
    momentFunctional (recoverySurgeryMoment (2*d+1)) ((recoveryMomentWitness d)^2) < 0 := by
  have hdeg : ((recoveryMomentWitness d)^2).natDegree = 2*d+1+1 := by
    rw [natDegree_pow, recoveryMomentWitness_degree]
    omega
  have hcoeff : ((recoveryMomentWitness d)^2).coeff (2*d+1+1)=1 := by
    rw [← hdeg]
    exact (recoveryMomentWitness_monic d).pow 2 |>.coeff_natDegree
  rw [recoverySurgeryMomentFunctional_top_change (2*d+1) _ (le_of_eq hdeg),hcoeff,one_mul]
  have hb := recoveryMomentWitness_base_bound d
  have hl := recoverySurgeryMoment_drop_loss (2*d+1)
  have he : (16 : ℝ)^(2*(d+1)) = ((4 : ℝ)^(2*(d+1)))^2 := by
    calc
      _ = ((4 : ℝ)*4)^(2*(d+1)) := by congr 1; ring
      _ = _ := by rw [mul_pow]; ring
  have hs : 4/(16 : ℝ)^(2*(d+1)) < 1/(32*(2*d+3 : ℝ)^5*(4 : ℝ)^(2*(d+1))) := by
    rw [he]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_pos (show 0 < (4 : ℝ)^(2*(d+1)) by positivity)
      (sub_pos.mpr hd)]
  have hen : 2*d+1+1=2*(d+1) := by omega
  rw [hen] at hl
  push_cast at hl
  have hm : (2*(d:ℝ)+1+2) = 2*d+3 := by ring
  rw [hm, neg_div] at hl
  rw [hen]
  linarith

theorem recoveryDyadic_exponent_bound (j : ℕ) : 5*(j+4)+12 ≤ (2 : ℕ)^(j+5) := by
  induction j with
  | zero =>
    have h : (2 : ℕ)^5=32 := by ring
    simpa only [zero_add, h] using (le_refl (32 : ℕ))
  | succ j ih =>
    rw [show j+1+5=(j+5)+1 by omega, pow_succ]
    omega

theorem recoveryDyadic_large (j : ℕ) :
    128*((2 : ℝ)^(j+4)+1)^5 < (4 : ℝ)^((2 : ℕ)^(j+4)) := by
  have htwo : (1 : ℝ) < (2 : ℝ)^(j+4) := one_lt_pow₀ (by linarith) (by omega)
  have hm : (2 : ℝ)^(j+4)+1 < (2 : ℝ)^(j+5) := by
    rw [show j+5=(j+4)+1 by omega, pow_succ (2 : ℝ) (j+4)]
    linarith
  have hp := pow_lt_pow_left₀ hm (show 0 ≤ (2 : ℝ)^(j+4)+1 by positivity) (show 5 ≠ 0 by omega)
  have h128 : (128 : ℝ)=(2 : ℝ)^7 := by ring
  have he : 128*((2 : ℝ)^(j+5))^5=(2 : ℝ)^(5*(j+4)+12) := by
    rw [h128, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hr : (4 : ℝ)^((2 : ℕ)^(j+4)) = (2 : ℝ)^((2 : ℕ)^(j+5)) := by
    rw [show (4 : ℝ)=(2 : ℝ)^2 by ring, ← pow_mul,
      show j+5=(j+4)+1 by omega, pow_succ (2 : ℕ) (j+4)]
    congr 1
    omega
  calc
    _ < 128*((2 : ℝ)^(j+5))^5 := by linarith
    _ = _ := he
    _ ≤ _ := by rw [hr]; exact pow_le_pow_right₀ (by linarith) (recoveryDyadic_exponent_bound j)

theorem recoverySurgery_dyadic_negative (j : ℕ) :
    momentFunctional (recoverySurgeryMoment ((2 : ℕ)^(j+4)-1))
      ((recoveryMomentWitness ((2 : ℕ)^(j+3)-1))^2) < 0 := by
  have hp : 0 < (2 : ℕ)^(j+3) := by positivity
  have he : (2 : ℕ)^(j+4) = 2*(2 : ℕ)^(j+3) := by
    rw [show j+4=(j+3)+1 by omega, pow_succ]
    omega
  have hn : 2*((2 : ℕ)^(j+3)-1)+1 = (2 : ℕ)^(j+4)-1 := by omega
  have hd : 2*((2 : ℕ)^(j+3)-1+1) = (2 : ℕ)^(j+4) := by omega
  have hr : (2*(((2 : ℕ)^(j+3)-1 : ℕ) : ℝ)+3) = (2 : ℝ)^(j+4)+1 := by
    have h : 2*((2 : ℕ)^(j+3)-1)+3 = (2 : ℕ)^(j+4)+1 := by omega
    exact_mod_cast h
  have h := recoveryMomentWitness_negative_of_large ((2 : ℕ)^(j+3)-1) (by
    rw [hr, hd]
    exact recoveryDyadic_large j)
  simpa only [hn] using h

theorem recoverySurgery_dyadic_first_failure (j : ℕ) :
    ∃ P : ℝ[X], P.natDegree=(2 : ℕ)^(j+3) ∧
      momentFunctional (recoverySurgeryMoment ((2 : ℕ)^(j+4)-1)) (P^2) < 0 ∧
      ∀ Q : ℝ[X], Q ≠ 0 → Q.natDegree < (2 : ℕ)^(j+3) →
        0 < momentFunctional (recoverySurgeryMoment ((2 : ℕ)^(j+4)-1)) (Q^2) := by
  have hp : 0 < (2 : ℕ)^(j+3) := by positivity
  refine ⟨recoveryMomentWitness ((2 : ℕ)^(j+3)-1),?_,recoverySurgery_dyadic_negative j,?_⟩
  · rw [recoveryMomentWitness_degree, Nat.sub_add_cancel (by omega)]
  · intro Q hQ hd
    apply recoverySurgeryMoment_square_prefix_positive _ Q hQ
    have he : (2 : ℕ)^(j+4) = 2*(2 : ℕ)^(j+3) := by
      rw [show j+4=(j+3)+1 by omega, pow_succ]
      omega
    omega

theorem recoverySurgery_dyadic_no_measure (j : ℕ) :
    ¬ ∃ μ : Measure ℝ, (∀ k : ℕ, Integrable (fun x : ℝ => x^k) μ) ∧
      ∀ k : ℕ, recoverySurgeryMoment ((2 : ℕ)^(j+4)-1) k = ∫ x, x^k ∂μ := by
  rintro ⟨μ,hint,hm⟩
  have h := momentFunctional_pow_two_nonneg _ hm hint
    (recoveryMomentWitness ((2 : ℕ)^(j+3)-1))
  linarith [recoverySurgery_dyadic_negative j]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
