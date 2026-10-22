import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalFundamentalFrequencies

/-!
# Reflected readers at the original physical clock

At either original fundamental frequency, the normalizable mode for the
reflected Xi label has a nonzero opposite-horizon coefficient. Its exact
Gamma quotient gives the boundary defect, independently of a proposed
local or nonlocal formula for transporting readers.

This excludes identifying these two fixed-frequency boundary modes. It does
not exclude cancellation in the complete nonlinear causal action.
-/

set_option autoImplicit false
open Complex
namespace RHTower.D4BMReflectedReaderBoundary
open D4BMJointSource D4BMLaplaceRadial
noncomputable section

/-- The reflected reader connection at each unchanged fundamental frequency is an explicit Gamma quotient. -/
theorem reflected_connection_eq (q : XiZeroCopy) (side : Bool) :
    connection (physicalFundamentalFrequency q side)
      (physicalRadialFrequency (xiZeroCopyReflectEquiv q)) =
    if side then
      Gamma (-(q.1 : ℂ)/2)*Gamma (1/2 : ℂ) /
        (Gamma (1/4 : ℂ)*Gamma (1/4-(q.1 : ℂ)/2))
    else
      Gamma (-1+(q.1 : ℂ)/2)*Gamma (1/2 : ℂ) /
        (Gamma (-1/4+(q.1 : ℂ)/2)*Gamma (-1/4 : ℂ)) := by
  have hr : I*physicalRadialFrequency (xiZeroCopyReflectEquiv q) = -(q.1 : ℂ)/2 := by
    rw [physicalRadialFrequency, physicalAngularParameter_eq]
    change I*(-I*((1-(q.1 : ℂ)-1)/2)) = _
    ring_nf
    rw [I_sq]
    ring
  have hc : gaussC (physicalFundamentalFrequency q side) =
      if side then -(q.1 : ℂ)/2 else -1+(q.1 : ℂ)/2 := by
    rw [gaussC, physicalFundamentalFrequency_eq]
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
  have ha : gaussC (physicalFundamentalFrequency q side) -
      gaussA (physicalFundamentalFrequency q side)
        (physicalRadialFrequency (xiZeroCopyReflectEquiv q)) =
      if side then (1/4 : ℂ) else -1/4+(q.1 : ℂ)/2 := by
    rw [gaussC, gaussA, hr, physicalFundamentalFrequency_eq]
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
  have hb : gaussC (physicalFundamentalFrequency q side) -
      gaussB (physicalFundamentalFrequency q side)
        (physicalRadialFrequency (xiZeroCopyReflectEquiv q)) =
      if side then 1/4-(q.1 : ℂ)/2 else (-1/4 : ℂ) := by
    rw [gaussC, gaussB, hr, physicalFundamentalFrequency_eq]
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
  rw [connection, ha, hb, hc]
  cases side <;> rfl

private theorem gamma_nonreal (z : ℂ) (hz : z.im ≠ 0) : Gamma z ≠ 0 := by
  apply Gamma_ne_zero
  intro n he
  apply hz
  rw [he]
  simp

private theorem gamma_neg_quarter : Gamma (-1/4 : ℂ) ≠ 0 := by
  apply Gamma_ne_zero
  intro n he
  have hr := congrArg Complex.re he
  norm_num at hr
  have hn : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  have hn0 : n = 0 := by omega
  subst n
  norm_num at hr

/-- The reflected connection is nonzero at both original fundamental frequencies for every Xi occurrence. -/
theorem reflected_connection_ne_zero (q : XiZeroCopy) (side : Bool) :
    connection (physicalFundamentalFrequency q side)
      (physicalRadialFrequency (xiZeroCopyReflectEquiv q)) ≠ 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  have hG (a : ℝ) :
      Gamma ((a : ℂ)+(q.1 : ℂ)/2) ≠ 0 ∧ Gamma ((a : ℂ)-(q.1 : ℂ)/2) ≠ 0 := by
    constructor <;> apply gamma_nonreal <;>
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im,
        Complex.div_ofNat_im, zero_add, zero_sub]
    · exact div_ne_zero hi (by norm_num)
    · exact neg_ne_zero.mpr (div_ne_zero hi (by norm_num))
  have hhalf : Gamma (1/2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hquarter : Gamma (1/4 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  rw [reflected_connection_eq]
  cases side
  · exact div_ne_zero (mul_ne_zero (by simpa using (hG (-1)).1) hhalf)
      (mul_ne_zero (by simpa using (hG (-1/4)).1) gamma_neg_quarter)
  · exact div_ne_zero (mul_ne_zero (by simpa [neg_div] using (hG 0).2) hhalf)
      (mul_ne_zero hquarter (by simpa using (hG (1/4)).2))

/-- The reflected normalizable mode fails the original horizon domain at the unchanged physical frequency. -/
theorem reflected_normalizable_not_original_horizon (q : XiZeroCopy) (side : Bool) :
    ¬ OriginalHorizonC2 (physicalFundamentalFrequency q side)
      (normalizable (physicalFundamentalFrequency q side)
        (physicalRadialFrequency (xiZeroCopyReflectEquiv q))) := by
  have hw := physicalFundamentalFrequency_strip q side
  rw [normalizable_original_horizon_domain_iff _ _ hw.1 (abs_lt.mp hw.2).1]
  exact reflected_connection_ne_zero q side

/-- The exact opposite-horizon coordinate survives for the reflected normalizable reader. -/
theorem reflected_opposite_coefficient_ne_zero (q : XiZeroCopy) (side : Bool) :
    horizonOppositeCoefficient (physicalFundamentalFrequency q side)
      (physicalRadialFrequency (xiZeroCopyReflectEquiv q))
      (normalizable (physicalFundamentalFrequency q side)
        (physicalRadialFrequency (xiZeroCopyReflectEquiv q)))
      (normalizableFirst (physicalFundamentalFrequency q side)
        (physicalRadialFrequency (xiZeroCopyReflectEquiv q))) ≠ 0 := by
  have hw := (physicalFundamentalFrequency_strip q side).1
  rw [normalizable_opposite_coefficient _ _ hw]
  refine div_ne_zero (reflected_connection_ne_zero q side) (mul_ne_zero (by norm_num) ?_)
  intro he
  apply hw
  rw [he, Complex.zero_im]

end
end RHTower.D4BMReflectedReaderBoundary
