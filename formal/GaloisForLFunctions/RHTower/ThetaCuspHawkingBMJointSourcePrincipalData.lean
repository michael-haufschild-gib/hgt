import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceAngularAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceParameters

/-! The actual three principal half-square powers and their independent causal radial chamber. -/
open Set
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMQuadraticMixedSource D4BMModularCore D4BMLaplaceRadial
noncomputable section

def weylCoefficient (q : XiZeroCopy) (branch : Bool) : ℂ :=
  d4BMCompletedEisensteinCuspConstantCoefficient (center q) branch

def principalExponent (q : XiZeroCopy) (i : Fin 3) : ℂ :=
  ![2*(q.1:ℂ),1,2-2*(q.1:ℂ)] i

def principalAmplitude (q : XiZeroCopy) (i : Fin 3) : ℂ :=
  ![(weylCoefficient q true)^(2 : ℕ)/2,weylCoefficient q true*weylCoefficient q false,
    (weylCoefficient q false)^(2 : ℕ)/2] i

/-- The gradient coefficient forced by the literal angular equation of each principal power. -/
def principalGradient (q : XiZeroCopy) (branch : Bool) (i : Fin 3) : ℂ :=
  (principalExponent q i*(principalExponent q i-1)/2-
    (physicalRate q branch+1)*(physicalRate q branch+2))*principalAmplitude q i

def principalFrequency (q : XiZeroCopy) (i : Fin 3) : ℂ :=
  Complex.I*(principalExponent q i-1/2)

/-- Only the explicit cusp powers use these scalar radial parameters. -/
theorem principalFrequency_parameter (q : XiZeroCopy) (i : Fin 3) :
    1/4+(principalFrequency q i)^(2 : ℕ) = principalExponent q i*(1-principalExponent q i) := by
  unfold principalFrequency
  rw [mul_pow,Complex.I_sq]
  ring

private theorem principal_weyl (q : XiZeroCopy) (z : Fin 2 → ℝ) :
    principal (center q) z = weylCoefficient q true*(z 1:ℂ)^(q.1:ℂ)+
      weylCoefficient q false*(z 1:ℂ)^(1-(q.1:ℂ)) := by
  have hm : d4BMCompletedEisensteinCuspWeylExponent (center q) false = 1-(q.1:ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,D4BMGlobalAngularResponse.center]
    ring
  have hp : d4BMCompletedEisensteinCuspWeylExponent (center q) true = (q.1:ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,D4BMGlobalAngularResponse.center]
  simp only [principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantMaassFactor,
    mul_one,hm,hp,weylCoefficient]
  exact add_comm _ _

/-- Exact finite principal decomposition of the original two-leg half-square, including the cross term. -/
theorem principalSquare_expansion (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    principalSquare q z = ∑ i : Fin 3, principalAmplitude q i*(z 1:ℂ)^(principalExponent q i) := by
  rw [principalSquare,principal_weyl]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change (weylCoefficient q true*(z 1:ℂ)^(q.1:ℂ)+
      weylCoefficient q false*(z 1:ℂ)^(1-(q.1:ℂ)))^(2 : ℕ)/2 =
    (weylCoefficient q true)^(2 : ℕ)/2*(z 1:ℂ)^(2*(q.1:ℂ))+
      (weylCoefficient q true*weylCoefficient q false*(z 1:ℂ)^(1:ℂ)+
        (weylCoefficient q false)^(2 : ℕ)/2*(z 1:ℂ)^(2-2*(q.1:ℂ)))
  have he := cusp_power_square (q.1:ℂ) (weylCoefficient q true) (weylCoefficient q false) z hz
  linear_combination (-1/2:ℂ)*he

def PrincipalChamber (q : XiZeroCopy) (w : ℂ) : Prop :=
  ∀ i : Fin 3, Chamber w (principalFrequency q i)

def principalThreshold (q : XiZeroCopy) : ℝ :=
  1+|(principalFrequency q 0).im|+|(principalFrequency q 1).im|+|(principalFrequency q 2).im|

/-- A whole right half-plane lies in all three actual principal radial chambers. -/
theorem principalChamber_of_threshold (q : XiZeroCopy) (w : ℂ)
    (hw : principalThreshold q < w.re) : PrincipalChamber q w := by
  intro i
  have h0 := abs_nonneg (principalFrequency q 0).im
  have h1 := abs_nonneg (principalFrequency q 1).im
  have h2 := abs_nonneg (principalFrequency q 2).im
  unfold principalThreshold at hw
  fin_cases i
  · change |(principalFrequency q 0).im| < w.re
    linarith
  · change |(principalFrequency q 1).im| < w.re
    linarith
  · change |(principalFrequency q 2).im| < w.re
    linarith

theorem principalChamber_re_pos {q : XiZeroCopy} {w : ℂ} (hw : PrincipalChamber q w) : 0 < w.re :=
  chamber_re_pos (hw 0)

/-- The joint source chamber is nonempty for every actual Xi occurrence. -/
theorem principalChamber_exists (q : XiZeroCopy) : ∃ w : ℂ, PrincipalChamber q w := by
  refine ⟨((principalThreshold q+1:ℝ):ℂ),principalChamber_of_threshold q _ ?_⟩
  simp only [Complex.ofReal_re]
  linarith

end
end RHTower.D4BMJointSource
