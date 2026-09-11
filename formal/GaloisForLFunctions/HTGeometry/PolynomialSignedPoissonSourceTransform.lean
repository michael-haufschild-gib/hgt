import GaloisForLFunctions.HTGeometry.GammaShiftConfluentAnnihilator
import GaloisForLFunctions.HTGeometry.PolynomialSignedPoissonProduct

/-! # Exact polynomial source transform for negative Poisson clocks

The ascending-factorial basis identifies the finite difference exponential
with an unrestricted polynomial transform. Parameter differentiation is
minus forward difference; products retain their exact finite signed-square
expansion. The theta seed has an exact two-shift formula.
-/

open Polynomial
namespace HTGeometry.SignedPoisson
noncomputable section

/-- Ascending factorial coordinates, read as ordinary polynomial coefficients. -/
def factorialCoordinatePolynomial : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (GaloisForLFunctions.ascPochhammerBasis ℝ).constr ℝ (fun n => X^n)

theorem factorialCoordinatePolynomial_asc (n : ℕ) :
    factorialCoordinatePolynomial (ascPochhammer ℝ n) = X^n := by
  rw [← GaloisForLFunctions.ascPochhammerBasis_apply]
  exact Module.Basis.constr_basis _ _ _ _

private def multiplyX : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun P := X*P
  map_add' P Q := by ring
  map_smul' r P := by simp only [smul_eq_C_mul,RingHom.id_apply]; ring

private theorem multiplyX_apply (P : ℝ[X]) : multiplyX P = X*P := rfl

/-- Multiplication by the clock index is a polynomial differential operator on its moments. -/
theorem factorialCoordinatePolynomial_X_mul (P : ℝ[X]) :
    factorialCoordinatePolynomial (X*P) =
      X*(factorialCoordinatePolynomial P-(factorialCoordinatePolynomial P).derivative) := by
  have heq : factorialCoordinatePolynomial.comp multiplyX =
      multiplyX.comp (factorialCoordinatePolynomial-Polynomial.derivative.comp factorialCoordinatePolynomial) := by
    apply (GaloisForLFunctions.ascPochhammerBasis ℝ).ext
    intro n
    simp only [LinearMap.comp_apply,LinearMap.sub_apply,GaloisForLFunctions.ascPochhammerBasis_apply,multiplyX_apply]
    have hmul : X*ascPochhammer ℝ n = ascPochhammer ℝ (n+1)-(n : ℝ) • ascPochhammer ℝ n := by
      rw [ascPochhammer_succ_right]
      simp only [smul_eq_C_mul,C_eq_natCast]
      ring
    rw [hmul,map_sub,map_smul,factorialCoordinatePolynomial_asc,factorialCoordinatePolynomial_asc]
    cases n with
    | zero => simp
    | succ n =>
      rw [derivative_X_pow_succ]
      simp only [smul_eq_C_mul,Nat.cast_add,Nat.cast_one,C_add,map_one,pow_succ]
      ring
  exact congrArg (fun T : ℝ[X] →ₗ[ℝ] ℝ[X] => T P) heq

/-- The source-oriented polynomial for a Poisson parameter with negative sign. -/
def negativePoissonPolynomial : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  factorialCoordinatePolynomial.comp (Polynomial.aeval (-X : ℝ[X])).toLinearMap

theorem negativePoissonPolynomial_one : negativePoissonPolynomial 1 = 1 := by
  change factorialCoordinatePolynomial ((Polynomial.aeval (-X : ℝ[X])) 1) = 1
  rw [map_one,← ascPochhammer_zero ℝ,factorialCoordinatePolynomial_asc]
  simp

theorem negativePoissonPolynomial_X_mul (P : ℝ[X]) :
    negativePoissonPolynomial (X*P) =
      X*((negativePoissonPolynomial P).derivative-negativePoissonPolynomial P) := by
  change factorialCoordinatePolynomial ((Polynomial.aeval (-X : ℝ[X])) (X*P)) = _
  rw [map_mul,aeval_X,neg_mul,map_neg,factorialCoordinatePolynomial_X_mul]
  change -(X*(negativePoissonPolynomial P-(negativePoissonPolynomial P).derivative)) = _
  ring

theorem negativePoissonPolynomial_X : negativePoissonPolynomial X = -X := by
  have h := negativePoissonPolynomial_X_mul 1
  simpa [negativePoissonPolynomial_one] using h

theorem negativePoissonPolynomial_X_sq : negativePoissonPolynomial (X^2) = X^2-X := by
  have h := negativePoissonPolynomial_X_mul X
  rw [negativePoissonPolynomial_X] at h
  simp only [derivative_neg,derivative_X] at h
  rw [pow_two,h]
  ring

/-- The literal theta seed is the transformed polynomial 4 J^2 + 2 J. -/
theorem negativePoissonPolynomial_thetaSeed :
    negativePoissonPolynomial ((4 : ℝ) • X^2+(2 : ℝ) • X) = 4*X^2-6*X := by
  rw [map_add,map_smul,map_smul,negativePoissonPolynomial_X_sq,negativePoissonPolynomial_X]
  simp only [smul_eq_C_mul,C_ofNat]
  norm_num
  ring

/-- The signed clock seed for each literal theta atom. -/
def thetaClockSeed : ℝ[X] := (4 : ℝ) • X^2+(2 : ℝ) • X

/-- The clock polynomial that differentiates the literal theta atom. -/
def thetaClockMultiply (P : ℝ[X]) : ℝ[X] := (2 : ℝ) • (X*P)+(1/2 : ℝ) • P

/-- Polynomial forward and backward differences in the source clock. -/
def sourceForwardDifference : ℝ[X] →ₗ[ℝ] ℝ[X] := Polynomial.taylor 1-LinearMap.id

def sourceBackwardDifference : ℝ[X] →ₗ[ℝ] ℝ[X] := LinearMap.id-Polynomial.taylor (-1)

private theorem sourceBackwardDifference_asc_succ (n : ℕ) :
    sourceBackwardDifference (ascPochhammer ℝ (n+1)) =
      ((n+1 : ℕ) : ℝ) • ascPochhammer ℝ n := by
  have h := congrArg (Polynomial.compRingHom (X-1 : ℝ[X]))
    (ascPochhammer_succ_comp_X_add_one ℝ n)
  have hs : (X+1 : ℝ[X]).comp (X-1) = X := by simp
  simp only [map_add,map_nsmul,coe_compRingHom_apply,comp_assoc,hs,comp_X] at h
  change ascPochhammer ℝ (n+1)-Polynomial.taylor (-1) (ascPochhammer ℝ (n+1)) = _
  rw [taylor_apply]
  simp only [map_neg,map_one,← sub_eq_add_neg]
  simp only [nsmul_eq_mul,smul_eq_C_mul,C_eq_natCast] at h ⊢
  linear_combination h

/-- The derivative of the factorial coordinate transform is the backward difference. -/
theorem factorialCoordinatePolynomial_derivative (P : ℝ[X]) :
    (factorialCoordinatePolynomial P).derivative =
      factorialCoordinatePolynomial (sourceBackwardDifference P) := by
  have he : Polynomial.derivative.comp factorialCoordinatePolynomial =
      factorialCoordinatePolynomial.comp sourceBackwardDifference := by
    apply (GaloisForLFunctions.ascPochhammerBasis ℝ).ext
    intro n
    simp only [LinearMap.comp_apply,GaloisForLFunctions.ascPochhammerBasis_apply]
    cases n with
    | zero => simp [ascPochhammer_zero,sourceBackwardDifference,
        show factorialCoordinatePolynomial (1 : ℝ[X]) = 1 from by
          simpa using factorialCoordinatePolynomial_asc 0]
    | succ n =>
      rw [sourceBackwardDifference_asc_succ,map_smul,
        factorialCoordinatePolynomial_asc,factorialCoordinatePolynomial_asc,derivative_X_pow_succ]
      simp only [smul_eq_C_mul,Nat.cast_add,Nat.cast_one]
  exact congrArg (fun T : ℝ[X] →ₗ[ℝ] ℝ[X] => T P) he

private theorem negativePoissonPolynomial_apply (P : ℝ[X]) :
    negativePoissonPolynomial P = factorialCoordinatePolynomial (P.comp (-X)) := rfl

/-- Differentiation in the negative Poisson parameter is minus the clock forward difference. -/
theorem negativePoissonPolynomial_derivative (P : ℝ[X]) :
    (negativePoissonPolynomial P).derivative =
      -negativePoissonPolynomial (sourceForwardDifference P) := by
  have he : sourceBackwardDifference (P.comp (-X)) =
      -(sourceForwardDifference P).comp (-X) := by
    simp only [sourceBackwardDifference,sourceForwardDifference,LinearMap.sub_apply,
      LinearMap.id_apply,taylor_apply,sub_comp,comp_assoc,neg_comp,add_comp,X_comp,one_comp,
      map_neg,map_one]
    ring_nf
  rw [negativePoissonPolynomial_apply,factorialCoordinatePolynomial_derivative,he,map_neg,
    negativePoissonPolynomial_apply]

/-- Every polynomial parameter derivative retains the exact iterated clock difference. -/
theorem iterate_derivative_negativePoissonPolynomial (P : ℝ[X]) (k : ℕ) :
    Polynomial.derivative^[k] (negativePoissonPolynomial P) =
      (-1 : ℝ)^k • negativePoissonPolynomial ((sourceForwardDifference^[k]) P) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,map_smul,negativePoissonPolynomial_derivative,
      Function.iterate_succ_apply']
    simp [pow_succ]

private def sourceEvalZero : ℝ[X] →ₗ[ℝ] ℝ where
  toFun P := P.eval 0
  map_add' P Q := by simp
  map_smul' r P := by simp [eval_smul]

private theorem factorialCoordinatePolynomial_eval_zero (P : ℝ[X]) :
    (factorialCoordinatePolynomial P).eval 0 = P.eval 0 := by
  have he : sourceEvalZero.comp factorialCoordinatePolynomial = sourceEvalZero := by
    apply (GaloisForLFunctions.ascPochhammerBasis ℝ).ext
    intro n
    simp only [LinearMap.comp_apply,GaloisForLFunctions.ascPochhammerBasis_apply]
    change (factorialCoordinatePolynomial (ascPochhammer ℝ n)).eval 0 = (ascPochhammer ℝ n).eval 0
    rw [factorialCoordinatePolynomial_asc]
    cases n <;> simp
  exact congrArg (fun T : ℝ[X] →ₗ[ℝ] ℝ => T P) he

/-- The source-oriented moment preserves the exact clock value at zero. -/
theorem negativePoissonPolynomial_eval_zero (P : ℝ[X]) :
    (negativePoissonPolynomial P).eval 0 = P.eval 0 := by
  rw [negativePoissonPolynomial_apply,factorialCoordinatePolynomial_eval_zero]
  simp

/-- Every parameter coefficient is the exact finite Newton difference at the clock origin. -/
theorem negativePoissonPolynomial_coeff (P : ℝ[X]) (k : ℕ) :
    (negativePoissonPolynomial P).coeff k =
      (-1 : ℝ)^k*((sourceForwardDifference^[k]) P).eval 0/(k.factorial : ℝ) := by
  have h := congrArg (fun Q : ℝ[X] => Q.eval 0) (iterate_derivative_negativePoissonPolynomial P k)
  rw [eval_smul,negativePoissonPolynomial_eval_zero] at h
  have hc := Polynomial.coeff_iterate_derivative (k := k) (negativePoissonPolynomial P) 0
  rw [coeff_zero_eq_eval_zero] at hc
  simp only [zero_add,Nat.descFactorial_self,nsmul_eq_mul] at hc
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  apply (eq_div_iff hk).mpr
  rw [hc] at h
  change (k.factorial : ℝ)*(negativePoissonPolynomial P).coeff k = _ at h
  simpa only [smul_eq_mul,mul_comm] using h

noncomputable local instance (n : ℕ) : AddCommGroup (PolyBelow n) := inferInstance

/-- The bounded nilpotent operator is the same clock difference used in the source formula. -/
theorem difference_power_coe (n k : ℕ) (P : PolyBelow n) :
    (((difference n)^k) P : ℝ[X]) = (sourceForwardDifference^[k]) (P : ℝ[X]) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,difference_coe,ih,Function.iterate_succ_apply']
    rfl

/-- The source-oriented polynomial agrees exactly with the already proved finite signed moment. -/
theorem negativePoissonPolynomial_eval_eq_moment (n : ℕ) (p : ℝ) (P : PolyBelow n) :
    (negativePoissonPolynomial (P : ℝ[X])).eval p = moment n (-p) P := by
  by_cases hp : (P : ℝ[X]) = 0
  · have hP : P = 0 := Subtype.ext hp
    simp [hP,moment]
  have hPdeg : (P : ℝ[X]).natDegree < n :=
    (Polynomial.natDegree_lt_iff_degree_lt hp).2 (Polynomial.mem_degreeLT.mp P.property)
  have hz (k : ℕ) (hk : n ≤ k) : (sourceForwardDifference^[k]) (P : ℝ[X]) = 0 := by
    rw [← difference_power_coe]
    have hh := difference_iterate_zero n k P (hPdeg.trans_le hk)
    rw [hh]
    rfl
  have hcoeff (k : ℕ) (hk : n ≤ k) : (negativePoissonPolynomial (P : ℝ[X])).coeff k = 0 := by
    rw [negativePoissonPolynomial_coeff,hz k hk]
    simp
  have hdeg : (negativePoissonPolynomial (P : ℝ[X])).natDegree < n := by
    by_cases hn : negativePoissonPolynomial (P : ℝ[X]) = 0
    · simp only [hn,natDegree_zero]
      omega
    · by_contra hh
      have hzero := hcoeff _ (Nat.le_of_not_gt hh)
      exact (Polynomial.leadingCoeff_ne_zero.mpr hn) (by simpa only [Polynomial.coeff_natDegree] using hzero)
  rw [Polynomial.eval_eq_sum_range' hdeg]
  have hd : ((-p) • difference n)^n = 0 := by rw [_root_.smul_pow,difference_pow_eq_zero,smul_zero]
  unfold moment
  rw [IsNilpotent.exp_eq_sum hd]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,_root_.smul_pow,map_sum,map_smul,map_rat_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [negativePoissonPolynomial_coeff,← difference_power_coe]
  change ((-1 : ℝ)^k*((((difference n)^k) P : ℝ[X]).eval 0)/(k.factorial : ℝ))*p^k =
    (k.factorial : ℚ)⁻¹ • ((-p)^k*origin n (((difference n)^k) P))
  rw [← Rat.cast_smul_eq_qsmul ℝ]
  simp only [Rat.cast_inv,Rat.cast_natCast,smul_eq_mul]
  change ((-1 : ℝ)^k*((((difference n)^k) P : ℝ[X]).eval 0)/(k.factorial : ℝ))*p^k =
    (k.factorial : ℝ)⁻¹*((-p)^k*((((difference n)^k) P : ℝ[X]).eval 0))
  rw [show (-p)^k = (-1 : ℝ)^k*p^k by simpa using neg_pow p k]
  ring

/-- Multiplication by the clock index becomes an exact shift of the observable. -/
theorem negativePoissonPolynomial_X_mul_shift (P : ℝ[X]) :
    negativePoissonPolynomial (X*P) = -X*negativePoissonPolynomial (Polynomial.taylor 1 P) := by
  rw [negativePoissonPolynomial_X_mul,negativePoissonPolynomial_derivative]
  change X*(-negativePoissonPolynomial (Polynomial.taylor 1 P-P)-negativePoissonPolynomial P) = _
  rw [map_sub]
  ring

/-- Both powers in the physical theta seed reduce to two literal clock shifts. -/
theorem negativePoissonPolynomial_thetaSeed_mul (P : ℝ[X]) :
    negativePoissonPolynomial (thetaClockSeed*P) =
      4*X^2*negativePoissonPolynomial (Polynomial.taylor 2 P)-
        6*X*negativePoissonPolynomial (Polynomial.taylor 1 P) := by
  have hP : thetaClockSeed*P = (4 : ℝ) • (X*(X*P))+(2 : ℝ) • (X*P) := by
    simp only [thetaClockSeed,smul_eq_C_mul,C_ofNat]
    ring
  have hshift : negativePoissonPolynomial (Polynomial.taylor 1 (X*P)) =
      -X*negativePoissonPolynomial (Polynomial.taylor 2 P)+
        negativePoissonPolynomial (Polynomial.taylor 1 P) := by
    rw [Polynomial.taylor_mul,Polynomial.taylor_X]
    simp only [map_one,add_mul,one_mul,map_add,negativePoissonPolynomial_X_mul_shift,
      Polynomial.taylor_taylor]
    norm_num
  rw [hP,map_add,map_smul,map_smul,negativePoissonPolynomial_X_mul_shift,
    hshift,negativePoissonPolynomial_X_mul_shift]
  simp only [smul_eq_C_mul,C_ofNat]
  ring

private def polynomialBelow (P : ℝ[X]) : PolyBelow (P.natDegree+1) :=
  ⟨P,Polynomial.mem_degreeLT.mpr (Polynomial.degree_le_natDegree.trans_lt
    (by exact_mod_cast Nat.lt_succ_self P.natDegree))⟩

/-- The signed product formula applies to the same unrestricted transform as the literal atoms. -/
theorem negativePoissonPolynomial_product (P Q : ℝ[X]) (p : ℝ) :
    (negativePoissonPolynomial (P*Q)).eval p =
      ∑ k ∈ Finset.range (P.natDegree+1), weight (-p) k*
        (negativePoissonPolynomial ((sourceForwardDifference^[k]) P)).eval p*
        (negativePoissonPolynomial ((sourceForwardDifference^[k]) Q)).eval p := by
  have h := moment_product_weight (P.natDegree+1) (Q.natDegree+1) (-p)
    (polynomialBelow P) (polynomialBelow Q)
  simp_rw [← negativePoissonPolynomial_eval_eq_moment,difference_power_coe] at h
  exact h

/-- The physical source transform has the exact finite signed-square expansion. -/
theorem negativePoissonPolynomial_square (P : ℝ[X]) (p : ℝ) :
    (negativePoissonPolynomial (P^2)).eval p =
      ∑ k ∈ Finset.range (P.natDegree+1), weight (-p) k*
        (negativePoissonPolynomial ((sourceForwardDifference^[k]) P)).eval p^2 := by
  simpa only [pow_two,mul_assoc] using negativePoissonPolynomial_product P P p

end
end HTGeometry.SignedPoisson
