import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalFundamentalFrequencies

/-! Actual principal radial poles and source poles do not collide with the same-copy physical fundamental targets. -/
open Complex Set
namespace RHTower.D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false

private theorem gamma_nonzero_nonreal (z : ℂ) (hz : z.im ≠ 0) : Gamma z ≠ 0 := by
  apply Gamma_ne_zero
  intro n he
  apply hz
  rw [he]
  simp

/-- Nonreal original Gamma arguments exclude every connection zero, without a positive-frequency restriction. -/
theorem connection_ne_zero_of_nonreal_arguments (w chi : ℂ) (hw : w.im ≠ 0)
    (ha : (gaussC w-gaussA w chi).im ≠ 0) (hb : (gaussC w-gaussB w chi).im ≠ 0) :
    connection w chi ≠ 0 := by
  unfold connection
  exact div_ne_zero (mul_ne_zero (gamma_nonzero_nonreal _ (by simpa [gaussC] using hw))
    (Gamma_ne_zero_of_re_pos (by norm_num)))
    (mul_ne_zero (gamma_nonzero_nonreal _ ha) (gamma_nonzero_nonreal _ hb))

end
end RHTower.D4BMLaplaceRadial

namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every original principal connection argument is nonreal at either fundamental QNM of the same Xi copy. -/
theorem physicalFundamental_principal_arguments_nonreal (q : XiZeroCopy) (side : Bool) (i : Fin 3) :
    (gaussC (physicalFundamentalFrequency q side)-
      gaussA (physicalFundamentalFrequency q side) (principalFrequency q i)).im ≠ 0 ∧
    (gaussC (physicalFundamentalFrequency q side)-
      gaussB (physicalFundamentalFrequency q side) (principalFrequency q i)).im ≠ 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  simp_rw [physicalFundamentalFrequency_eq]
  constructor
  all_goals
    cases side <;> fin_cases i <;> intro he <;> apply hi
    all_goals
      norm_num [gaussC,gaussA,gaussB,principalFrequency,principalExponent,
        Complex.mul_im,Complex.mul_re,Complex.div_im,Complex.div_re] at he
      linarith

/-- None of the three original principal radial denominators vanishes at either actual same-copy target QNM. -/
theorem physicalFundamental_principal_connection_ne_zero (q : XiZeroCopy) (side : Bool) (i : Fin 3) :
    connection (physicalFundamentalFrequency q side) (principalFrequency q i) ≠ 0 :=
  connection_ne_zero_of_nonreal_arguments _ _ (physicalFundamentalFrequency_strip q side).1
    (physicalFundamental_principal_arguments_nonreal q side i).1
    (physicalFundamental_principal_arguments_nonreal q side i).2

end
end RHTower.D4BMJointSource
