import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativePeriodAssembly
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCutoffPowerMoments

/-! The original principal half-square retains all three powers and both Weyl coefficients. -/
open Complex MeasureTheory Set
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse
noncomputable section

/-- The three literal coefficients of the original principal half-square. -/
def nativePrincipalPowerCoefficient (q : XiZeroCopy) : Fin 3 → ℂ :=
  ![reflectedCompletedLambda (2*(q.1:ℂ)-1)^(2 : ℕ)/2,
    reflectedCompletedLambda (2*(q.1:ℂ)-1)*reflectedCompletedLambda (2*(q.1:ℂ)),
    reflectedCompletedLambda (2*(q.1:ℂ))^(2 : ℕ)/2]

/-- The unchanged three height powers of the original principal half-square. -/
def nativePrincipalPowerExponent (q : XiZeroCopy) : Fin 3 → ℂ :=
  ![2-2*(q.1:ℂ),1,2*(q.1:ℂ)]

private theorem principal_shift (s : ℂ) (y : ℝ) :
    principal (s-1/2) ![0,y] =
      reflectedCompletedLambda (2*s-1)*(y:ℂ)^(1-s)+reflectedCompletedLambda (2*s)*(y:ℂ)^s := by
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantCoefficient,
    d4BMCompletedEisensteinCuspConstantMaassFactor,d4BMCompletedEisensteinCuspWeylExponent,
    d4BMCuspSign,Bool.false_eq_true,if_false,if_true,mul_one]
  norm_num only
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
  rw [show (2:ℂ)*(s-1/2)=2*s-1 by ring,
    show (1:ℂ)+(2*s-1)=2*s by ring,
    show (1/2:ℂ)+(-1)*(s-1/2)=1-s by ring,
    show (1/2:ℂ)+1*(s-1/2)=s by ring]

/-- The literal original principal half-square is exactly its three-power expansion. -/
theorem nativePrincipalSquare_eq_power_sum (q : XiZeroCopy) {y : ℝ} (hy : 0 < y) :
    principalSquare q ![0,y] = ∑ j : Fin 3, nativePrincipalPowerCoefficient q j*
      (y:ℂ)^(nativePrincipalPowerExponent q j) := by
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  change (principal ((q.1:ℂ)-1/2) ![0,y])^(2 : ℕ)/2 = _
  rw [principal_shift,Fin.sum_univ_three]
  simp only [nativePrincipalPowerCoefficient,nativePrincipalPowerExponent,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  have hm : ((y:ℂ)^(1-(q.1:ℂ)))^(2 : ℕ)=(y:ℂ)^(2-2*(q.1:ℂ)) := by
    rw [pow_two,← Complex.cpow_add _ _ hn]; congr 1; ring
  have hp : ((y:ℂ)^(q.1:ℂ))^(2 : ℕ)=(y:ℂ)^(2*(q.1:ℂ)) := by
    rw [pow_two,← Complex.cpow_add _ _ hn]; congr 1; ring
  have hx : (y:ℂ)^(1-(q.1:ℂ))*(y:ℂ)^(q.1:ℂ)=(y:ℂ)^(1:ℂ) := by
    rw [← Complex.cpow_add _ _ hn]; congr 1; ring
  calc
    _ = reflectedCompletedLambda (2*(q.1:ℂ)-1)^(2 : ℕ)/2*((y:ℂ)^(1-(q.1:ℂ)))^(2 : ℕ)+
        (reflectedCompletedLambda (2*(q.1:ℂ)-1)*reflectedCompletedLambda (2*(q.1:ℂ)))*
          ((y:ℂ)^(1-(q.1:ℂ))*(y:ℂ)^(q.1:ℂ))+
        reflectedCompletedLambda (2*(q.1:ℂ))^(2 : ℕ)/2*((y:ℂ)^(q.1:ℂ))^(2 : ℕ) := by ring
    _ = _ := by rw [hm,hp,hx]; rfl

/-- Every original principal power lies strictly between zero and two in real part. -/
theorem nativePrincipalPowerExponent_re (q : XiZeroCopy) (j : Fin 3) :
    0 < (nativePrincipalPowerExponent q j).re ∧ (nativePrincipalPowerExponent q j).re < 2 := by
  have hq := xi_divisor_support_re_mem_open_unit q.1
  fin_cases j <;> simp [nativePrincipalPowerExponent] <;> constructor <;> linarith [hq.1,hq.2]

/-- The original complementary moment has the exact finite sum of weighted power integrands. -/
theorem nativePrincipalRemainder_power_sum (q : XiZeroCopy) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    (y:ℂ)^(s-2)*nativePrincipalRemainder q y =
      ∑ j : Fin 3, nativePrincipalPowerCoefficient q j*
        ((1-cutoff ![0,y])*(y:ℂ)^((s-1+nativePrincipalPowerExponent q j)-1)) := by
  rw [nativePrincipalRemainder,nativePrincipalSquare_eq_power_sum q hy,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have he : (y:ℂ)^(s-2)*(y:ℂ)^(nativePrincipalPowerExponent q j) =
      (y:ℂ)^((s-1+nativePrincipalPowerExponent q j)-1) := by
    rw [← Complex.cpow_add _ _ hn]; congr 1; ring
  calc
    _ = nativePrincipalPowerCoefficient q j*((1-cutoff ![0,y])*
      ((y:ℂ)^(s-2)*(y:ℂ)^(nativePrincipalPowerExponent q j))) := by ring
    _ = _ := by rw [he]

/-- The original reflected cutoff moment retains the same three coefficients and reflected exponents. -/
theorem nativeSquareCutoffHeight_power_sum (q : XiZeroCopy) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    (y:ℂ)^(-s-1)*nativeSquareCutoffHeight q y =
      ∑ j : Fin 3, nativePrincipalPowerCoefficient q j*
        (cutoff ![0,y]*(y:ℂ)^((nativePrincipalPowerExponent q j-s)-1)) := by
  rw [nativeSquareCutoffHeight,nativePrincipalSquare_eq_power_sum q hy,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have he : (y:ℂ)^(-s-1)*(y:ℂ)^(nativePrincipalPowerExponent q j) =
      (y:ℂ)^((nativePrincipalPowerExponent q j-s)-1) := by
    rw [← Complex.cpow_add _ _ hn]; congr 1; ring
  calc
    _ = nativePrincipalPowerCoefficient q j*(cutoff ![0,y]*
      ((y:ℂ)^(-s-1)*(y:ℂ)^(nativePrincipalPowerExponent q j))) := by ring
    _ = _ := by rw [he]

end
end RHTower.D4BMJointSource
