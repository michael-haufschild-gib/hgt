import GaloisForLFunctions.SelbergClass.Primon.SquarefreeCardinality.ThePrimeFactorsOfEveryTemperatureDerivative
import GaloisForLFunctions.HTGeometry.CosineDepthCountRigidity
import GaloisForLFunctions.HTGeometry.HeatEscapeNonreal
import Mathlib.Analysis.Calculus.DSlope

/-!
# Splitting of the squarefree Gibbs activity root

For m occupied prime modes the zero at activity −1 has multiplicity m
at infinite temperature. Set β=tᵐ and activity equal to −1+tX. After
division by tᵐ the polynomial tends coefficientwise to Xᵐ−∏(1−p).
For m≥3 this gives nonreal activity zeros at all sufficiently small
positive inverse temperatures, despite the strict two-mode Rayleigh law.
-/

open Finset Filter Topology Polynomial RHTower
namespace GaloisForLFunctions.SelbergClass.Primon

noncomputable section

private def energySlope (S : Finset ℕ) := dslope (fun w : ℝ => Real.exp (-(finitePrimeSubsetProduct S : ℝ)*w)) 0

private theorem slope_deriv (S : Finset ℕ) :
    HasDerivAt (fun w : ℝ => Real.exp (-(finitePrimeSubsetProduct S : ℝ)*w)) (-(finitePrimeSubsetProduct S:ℝ)) 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).const_mul (-(finitePrimeSubsetProduct S : ℝ))).exp

private theorem slope_zero (S : Finset ℕ) : energySlope S 0 = -(finitePrimeSubsetProduct S:ℝ) := by
  rw [energySlope,dslope_same,(slope_deriv S).deriv]

private theorem slope_identity (S : Finset ℕ) (w : ℝ) :
    Real.exp (-(finitePrimeSubsetProduct S:ℝ)*w) = 1+w*energySlope S w := by
  have h := sub_smul_dslope (fun w : ℝ => Real.exp (-(finitePrimeSubsetProduct S:ℝ)*w)) 0 w
  simp only [sub_zero,smul_eq_mul,mul_zero,Real.exp_zero] at h
  change _ = 1+w*dslope _ 0 w
  linarith only [h]

private def slopePolynomial (P : Finset ℕ) (v : ℝ) : ℝ[X] :=
  ∑ S ∈ P.powerset, C (energySlope S v)*(X-1)^S.card

/-- Continuous extension in each coefficient of the rescaled cardinality polynomial. -/
def squarefreeActivityBlowup (P : Finset ℕ) (t : ℝ) : ℝ[X] :=
  X^P.card+(slopePolynomial P (t^P.card)).comp (C t*X)

private theorem sum_card_pow {A : Type*} [CommSemiring A] (P : Finset ℕ) (y : A) :
    ∑ S ∈ P.powerset, y^S.card = (1+y)^P.card := by
  have h := Finset.prod_add (fun _ : ℕ => y) (fun _ : ℕ => (1:A)) P
  simpa only [prod_const,one_pow,mul_one,add_comm (1:A)] using h.symm

/-- Exact polynomial identity before taking the high-temperature limit. -/
theorem squarefreeActivity_rescaling (P : Finset ℕ) (t : ℝ) :
    (squarefreeCardinalityPolynomial P (t^P.card)).comp (C t*X-1) =
      C (t^P.card)*squarefreeActivityBlowup P t := by
  let y := (C t*X-1 : ℝ[X])
  have h (S : Finset ℕ) :
      C (Real.exp (-(finitePrimeSubsetProduct S : ℝ)*t^P.card))*y^S.card =
        y^S.card+C (t^P.card)*(C (energySlope S (t^P.card))*y^S.card) := by
    rw [slope_identity,map_add,map_mul,map_one]
    ring
  have he : (1+y)^P.card = C (t^P.card)*X^P.card := by
    rw [show 1+y = C t*X by dsimp [y]; ring,mul_pow,←map_pow]
  simp only [squarefreeCardinalityPolynomial,sum_comp,mul_comp,C_comp,pow_comp,X_comp]
  change (∑ S ∈ P.powerset, C (Real.exp (-(finitePrimeSubsetProduct S : ℝ)*t^P.card))*y^S.card) = _
  simp_rw [h]
  rw [sum_add_distrib,sum_card_pow,he,←mul_sum,squarefreeActivityBlowup,mul_add]
  simp only [slopePolynomial,sum_comp,mul_comp,C_comp,pow_comp,sub_comp,X_comp,one_comp,y]

/-- The limiting root polynomial, including the signed product of all prime gaps. -/
theorem squarefreeActivityBlowup_zero {P : Finset ℕ} (hP : 0 < P.card) :
    squarefreeActivityBlowup P 0 = X^P.card-C (∏ p ∈ P, (1-(p:ℝ))) := by
  have hprod := Finset.prod_add (fun p : ℕ => -(p:ℝ)) (fun _ : ℕ => (1:ℝ)) P
  have hsum : ∑ S ∈ P.powerset, (-(finitePrimeSubsetProduct S:ℝ))*(-1:ℝ)^S.card =
      -(∏ p ∈ P, (1-(p:ℝ))) := by
    rw [←neg_inj,neg_neg,←sum_neg_distrib]
    calc _ = ∑ S ∈ P.powerset, ∏ p ∈ S, -(p:ℝ) := by
               apply sum_congr rfl
               intro S _
               simp only [finitePrimeSubsetProduct,Nat.cast_prod,prod_neg,neg_mul,neg_neg,mul_comm]
         _ = _ := by simpa only [prod_const,one_pow,mul_one,sub_eq_add_neg,add_comm (1:ℝ)] using hprod.symm
  rw [squarefreeActivityBlowup,zero_pow hP.ne',map_zero,zero_mul,comp_zero,slopePolynomial,
    eval_finsetSum]
  simp only [eval_mul,eval_C,eval_pow,eval_sub,eval_X,eval_one,zero_sub,slope_zero,hsum,C_neg,sub_eq_add_neg]

private theorem blowup_degree (P : Finset ℕ) (t : ℝ) : (squarefreeActivityBlowup P t).natDegree ≤ P.card := by
  have ha : (slopePolynomial P (t^P.card)).natDegree ≤ P.card := by
    apply natDegree_sum_le_of_forall_le
    intro S hS
    apply (natDegree_C_mul_le _ _).trans
    exact (natDegree_pow_le.trans (Nat.mul_le_mul_left S.card (show (X-1 : ℝ[X]).natDegree ≤ 1 by simp))).trans
      (by simpa using card_le_card (mem_powerset.mp hS))
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [squarefreeActivityBlowup,coeff_add,comp_C_mul_X_coeff,coeff_eq_zero_of_natDegree_lt (ha.trans_lt hj),zero_mul,add_zero]
  exact coeff_eq_zero_of_natDegree_lt ((natDegree_X_pow_le _).trans_lt hj)

/-- Coefficientwise limit on both sides of the real ramification parameter. -/
theorem squarefreeActivityBlowup_limit {P : Finset ℕ} (hP : 0 < P.card) (j : ℕ) :
    Tendsto (fun t : ℝ => (squarefreeActivityBlowup P t).coeff j) (𝓝 0)
      (𝓝 ((X^P.card-C (∏ p ∈ P, (1-(p:ℝ))) : ℝ[X]).coeff j)) := by
  rw [←squarefreeActivityBlowup_zero hP]
  change ContinuousAt (fun t : ℝ => (squarefreeActivityBlowup P t).coeff j) 0
  simp only [squarefreeActivityBlowup,coeff_add,comp_C_mul_X_coeff,slopePolynomial,finsetSum_coeff,coeff_C_mul]
  apply continuousAt_const.add
  apply ContinuousAt.mul _ (continuousAt_id.pow _)
  apply continuousAt_finsetSum
  intro S _
  apply ContinuousAt.mul _ continuousAt_const
  apply ContinuousAt.comp _ (continuousAt_id.pow _)
  simpa only [zero_pow hP.ne',energySlope] using continuousAt_dslope_same.mpr (slope_deriv S).differentiableAt

private theorem model_not_splits {m : ℕ} (hm : 3 ≤ m) {a : ℝ} (ha : a ≠ 0) :
    ¬ ((X:ℝ[X])^m-C a).Splits := by
  intro hs
  have hn : 0 < m := by omega
  have hx : (X^m-C a : ℝ[X]).eval 0 ≠ 0 := by simp [zero_pow hn.ne',ha]
  have hc := GaloisForLFunctions.HTGeometry.rootMultiplicity_derivative_le_one_of_realRooted
    hs.natDegree_eq_card_roots.le hx
  rw [derivative_sub,derivative_C,sub_zero,derivative_X_pow] at hc
  have hh : m-1 ≤ rootMultiplicity (0:ℝ) (C (m:ℝ)*X^(m-1)) := by
    rw [le_rootMultiplicity_iff (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')) (pow_ne_zero _ X_ne_zero)),
      map_zero,sub_zero]
    exact dvd_mul_left _ _
  omega

/-- For three or more prime modes a neighborhood of positive inverse temperatures
has nonreal activity roots. All positive conditional two-mode tables in the same
ensemble have strictly positive Rayleigh determinant. -/
theorem squarefreeCardinality_eventually_not_splits {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (hm : 3 ≤ P.card) : ∀ᶠ β : ℝ in 𝓝[>] 0, ¬ (squarefreeCardinalityPolynomial P β).Splits := by
  let m := P.card
  have hm' : 0 < m := by dsimp only [m]; omega
  let a : ℝ := ∏ p ∈ P, (1-(p:ℝ))
  have ha : a ≠ 0 := prod_ne_zero_iff.mpr fun p hp => sub_ne_zero.mpr
    (ne_of_lt (by exact_mod_cast (hP p hp).one_lt : (1:ℝ)<p))
  have hq : (X^m-C a : ℝ[X]).natDegree ≤ m := by rw [natDegree_X_pow_sub_C hm']
  have hn := _root_.HTGeometry.eventually_not_splits_of_coeff_limit (blowup_degree P) hq
    (X_pow_sub_C_ne_zero hm' a) (squarefreeActivityBlowup_limit hm') (model_not_splits hm ha)
  have hroot : Tendsto (fun β : ℝ => β^((m:ℝ)⁻¹)) (𝓝[>] 0) (𝓝 0) := by
    have hpos : 0 < (m:ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hm')
    simpa only [Real.zero_rpow hpos.ne'] using
      (((Real.continuous_rpow_const hpos.le).tendsto (0:ℝ)).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0))
  filter_upwards [hroot.eventually hn,self_mem_nhdsWithin] with β hβ hb
  let t := β^((m:ℝ)⁻¹)
  have ht : 0 < t := Real.rpow_pos_of_pos hb _
  have he : t^P.card=β := Real.rpow_inv_natCast_pow hb.le hm'.ne'
  intro hs
  have hy : (C t*X-1 : ℝ[X]).natDegree ≤ 1 := (natDegree_sub_le ..).trans
    (max_le (by simpa using natDegree_C_mul_le t (X:ℝ[X])) (by simp))
  have hfull := hs.comp_of_natDegree_le_one (g:=C t*X-1) hy
  rw [←he,squarefreeActivity_rescaling] at hfull
  exact hβ ((splits_C_mul (pow_ne_zero _ ht.ne')).mp hfull)


end

end GaloisForLFunctions.SelbergClass.Primon
