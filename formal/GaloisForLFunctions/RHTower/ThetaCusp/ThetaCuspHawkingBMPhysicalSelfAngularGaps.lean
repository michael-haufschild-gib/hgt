import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalResolventAssembly

/-! The actual source-to-itself angular eigenvalue gaps never collide at a Xi zero. -/
open Complex
namespace RHTower.D4BMJointSource
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Exact same-copy gap factors retain all three original principal exponents. -/
theorem physicalAngularGap_self_factors (q : XiZeroCopy) (i : Fin 3) :
    physicalAngularGap q q i =
      ![3*(q.1:ℂ)*(5*(q.1:ℂ)-2)/4,
        (q.1:ℂ)*(2-(q.1:ℂ))/4,
        (3*(q.1:ℂ)-2)*(5*(q.1:ℂ)-4)/4] i := by
  unfold physicalAngularGap physicalRadialFrequency
  rw [physicalAngularParameter_eq,mul_pow,neg_sq,Complex.I_sq]
  fin_cases i <;> norm_num [principalExponent] <;> ring

/-- Every same-copy gap is nonzero, derived from nonreality of the original Xi zero. -/
theorem physicalAngularGap_self_ne_zero (q : XiZeroCopy) (i : Fin 3) : physicalAngularGap q q i ≠ 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  have hlin (a b : ℝ) (ha : a ≠ 0) : (a:ℂ)*(q.1:ℂ)-(b:ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero,sub_zero,Complex.zero_im] at hh
    exact hi ((mul_eq_zero.mp hh).resolve_left ha)
  have hq : (q.1:ℂ) ≠ 0 := by intro he; apply hi; simp [he]
  have h2 : (2:ℂ)-(q.1:ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    norm_num at hh
    exact hi hh
  rw [physicalAngularGap_self_factors]
  fin_cases i
  · exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hq) (hlin 5 2 (by norm_num))) (by norm_num)
  · exact div_ne_zero (mul_ne_zero hq h2) (by norm_num)
  · exact div_ne_zero (mul_ne_zero (hlin 3 2 (by norm_num)) (hlin 5 4 (by norm_num))) (by norm_num)

/-- The complete same-copy resolvent denominator is nonzero for every actual Xi occurrence. -/
theorem physicalAngularGapProduct_self_ne_zero (q : XiZeroCopy) : physicalAngularGapProduct q q ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => physicalAngularGap_self_ne_zero q i)

end
end RHTower.D4BMJointSource
