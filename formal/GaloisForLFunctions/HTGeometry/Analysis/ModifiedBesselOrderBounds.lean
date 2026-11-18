import GaloisForLFunctions.HTGeometry.ModifiedBesselIOrder
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Bounds for the modified Bessel function of real order

The Gamma-normalized real series is strictly decreasing in the order.
The three-term recurrence turns the positive ratios into explicit continued-fraction bounds.
-/

namespace GaloisForLFunctions.HTGeometry
open Set Filter Topology
noncomputable section

private def realOrderTerm (a v : ℝ) (n : ℕ) : ℝ :=
  (a^2)^n / n.factorial / Real.Gamma (v + n + 1)

private theorem realOrderTerm_cast (a v : ℝ) (n : ℕ) :
    (realOrderTerm a v n : ℂ) = modifiedBesselIOrderCoreTerm a n (v:ℂ) := by
  have he : (v:ℂ) + ((n+1:ℕ):ℂ) = ((v+(n:ℝ)+1:ℝ):ℂ) := by push_cast; ring
  rw [modifiedBesselIOrderCoreTerm,reciprocalGammaEntire,he,Complex.Gamma_ofReal,realOrderTerm]
  push_cast
  rw [pow_mul]
  simp only [div_eq_mul_inv,one_mul]

private theorem realOrderTerm_hasSum (a v : ℝ) :
    HasSum (realOrderTerm a v) (modifiedBesselIOrderCore a (v:ℂ)).re := by
  have hc := ((summableLocallyUniformlyOn_modifiedBesselIOrderCoreTerm a).summable
    (Set.mem_univ (v:ℂ))).hasSum
  have hr := Complex.reCLM.hasSum hc
  convert hr using 1
  funext n
  change realOrderTerm a v n = (modifiedBesselIOrderCoreTerm a n (v:ℂ)).re
  rw [← realOrderTerm_cast,Complex.ofReal_re]

private theorem realOrder_core_cast (a v : ℝ) :
    modifiedBesselIOrderCore a (v:ℂ) = ((∑' n, realOrderTerm a v n : ℝ):ℂ) := by
  rw [modifiedBesselIOrderCore]
  simp_rw [← realOrderTerm_cast]
  exact (Complex.ofRealCLM.map_tsum (realOrderTerm_hasSum a v).summable).symm

/-- Remove the leading power and reciprocal Gamma factor from the real-order series. -/
def normalizedBesselCore (a v : ℝ) : ℝ :=
  Real.Gamma (v+1) * (modifiedBesselIOrderCore a (v:ℂ)).re

private def normalizedTerm (a v : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma (v+1) * realOrderTerm a v n

private theorem normalized_hasSum (a v : ℝ) :
    HasSum (normalizedTerm a v) (normalizedBesselCore a v) :=
  (realOrderTerm_hasSum a v).mul_left _

private theorem order_base_pos (v : Ioi (-1:ℝ)) : 0 < v.val+1 := by linarith [v.property]

private theorem shifted_order_pos (v : Ioi (-1:ℝ)) (n : ℕ) : 0 < v.val+(n:ℝ)+1 := by
  linarith [order_base_pos v, Nat.cast_nonneg (α := ℝ) n]

private theorem normalizedTerm_nonneg (a : ℝ) (v : Ioi (-1:ℝ)) (n : ℕ) :
    0 ≤ normalizedTerm a v n :=
  mul_nonneg (Real.Gamma_pos_of_pos (order_base_pos v)).le
    (div_nonneg (div_nonneg (pow_nonneg (sq_nonneg _) _) (Nat.cast_nonneg _))
      (Real.Gamma_pos_of_pos (shifted_order_pos v n)).le)

private theorem normalizedTerm_zero (a : ℝ) (v : Ioi (-1:ℝ)) : normalizedTerm a v 0 = 1 := by
  simp [normalizedTerm,realOrderTerm,(Real.Gamma_pos_of_pos (order_base_pos v)).ne']

private theorem normalizedTerm_succ (a : ℝ) (v : Ioi (-1:ℝ)) (n : ℕ) :
    normalizedTerm a v (n+1) =
      normalizedTerm a v n * (a^2 / (((n:ℝ)+1)*(v.val+n+1))) := by
  have hG := Real.Gamma_pos_of_pos (shifted_order_pos v n)
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  simp only [normalizedTerm,realOrderTerm,Nat.cast_succ,pow_succ,Nat.factorial_succ,Nat.cast_mul]
  rw [show v.val+((n:ℝ)+1)+1 = (v.val+n+1)+1 by ring,
    Real.Gamma_add_one (shifted_order_pos v n).ne']
  field_simp [hn,hG.ne',(shifted_order_pos v n).ne',show (n:ℝ)+1 ≠ 0 by positivity]
  <;> ring

private theorem normalizedTerm_upper (a : ℝ) (v : Ioi (-1:ℝ)) (n : ℕ) :
    normalizedTerm a v n ≤ (a^2 / (v.val+1))^n / n.factorial := by
  induction n with
  | zero => simp [normalizedTerm_zero]
  | succ n ih =>
    have hn : 0 < (n:ℝ)+1 := by positivity
    have hden : ((n:ℝ)+1)*(v.val+1) ≤ ((n:ℝ)+1)*(v.val+n+1) :=
      mul_le_mul_of_nonneg_left (by linarith [Nat.cast_nonneg (α := ℝ) n]) hn.le
    have hfac := div_le_div_of_nonneg_left (sq_nonneg a) (mul_pos hn (order_base_pos v)) hden
    rw [normalizedTerm_succ]
    calc
      _ ≤ ((a^2/(v.val+1))^n / n.factorial) * (a^2 / (((n:ℝ)+1)*(v.val+1))) :=
        mul_le_mul ih hfac (div_nonneg (sq_nonneg _) (mul_pos hn (shifted_order_pos v n)).le)
          (div_nonneg (pow_nonneg (div_nonneg (sq_nonneg a) (order_base_pos v).le) _)
            (Nat.cast_nonneg _))
      _ = _ := by
        rw [pow_succ,Nat.factorial_succ]
        push_cast
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring

/-- Two-sided, uniform-in-order control by the leading term and an exponential. -/
theorem normalizedBesselCore_bounds (a : ℝ) (v : Ioi (-1:ℝ)) :
    normalizedBesselCore a v ∈ Icc 1 (Real.exp (a^2/(v.val+1))) := by
  have hs := normalized_hasSum a v
  have he := NormedSpace.expSeries_div_hasSum_exp (a^2/(v.val+1))
  constructor
  · rw [← hs.tsum_eq, ← normalizedTerm_zero a v]
    exact hs.summable.le_tsum 0 fun n _ => normalizedTerm_nonneg a v n
  · rw [Real.exp_eq_exp_ℝ,← hs.tsum_eq,← he.tsum_eq]
    exact hs.summable.tsum_le_tsum (normalizedTerm_upper a v) he.summable

/-- The complex-order definition takes strictly positive real values on the entire ray of
orders above minus one. Its normalized leading term controls the range quantitatively. -/
theorem modifiedBessel_real_axis (a : Ioi (0:ℝ)) (v : Ioi (-1:ℝ)) :
    modifiedBesselIOrder (2*a.val) (v.val:ℂ) =
      ((Real.exp (v.val*Real.log a.val) * normalizedBesselCore a v / Real.Gamma (v.val+1) : ℝ):ℂ) := by
  have hG := Real.Gamma_pos_of_pos (order_base_pos v)
  rw [modifiedBesselIOrder,show 2*a.val/2 = a.val by ring, normalizedBesselCore,
    realOrder_core_cast]
  simp only [Complex.ofReal_re,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_exp]
  field_simp [show (Real.Gamma (v.val+1):ℂ) ≠ 0 by exact_mod_cast hG.ne']

theorem modifiedBessel_real_order_pos (a : Ioi (0:ℝ)) (v : Ioi (-1:ℝ)) :
    0 < (modifiedBesselIOrder (2*a.val) (v.val:ℂ)).re := by
  rw [modifiedBessel_real_axis,Complex.ofReal_re]
  exact div_pos (mul_pos (Real.exp_pos _) (zero_lt_one.trans_le (normalizedBesselCore_bounds a v).1))
    (Real.Gamma_pos_of_pos (order_base_pos v))

private theorem normalizedTerm_anti (a : ℝ) {v w : Ioi (-1:ℝ)} (hvw : v ≤ w) (n : ℕ) :
    normalizedTerm a w n ≤ normalizedTerm a v n := by
  induction n with
  | zero => simp [normalizedTerm_zero]
  | succ n ih =>
    rw [normalizedTerm_succ,normalizedTerm_succ]
    have hd : 0 < ((n:ℝ)+1)*(v.val+n+1) :=
      mul_pos (by positivity) (shifted_order_pos v n)
    have hle : ((n:ℝ)+1)*(v.val+n+1) ≤ ((n:ℝ)+1)*(w.val+n+1) :=
      mul_le_mul_of_nonneg_left (by linarith [show v.val ≤ w.val from hvw]) (by positivity)
    exact mul_le_mul ih (div_le_div_of_nonneg_left (sq_nonneg a) hd hle)
      (div_nonneg (sq_nonneg a) (mul_pos (by positivity) (shifted_order_pos w n)).le)
      (normalizedTerm_nonneg a v n)

/-- After leading-term normalization the Bessel function decreases strictly with order.
The first nonconstant coefficient is already strictly decreasing in the order. -/
theorem normalizedBesselCore_strictAnti (a : Ioi (0:ℝ)) :
    StrictAnti (fun v : Ioi (-1:ℝ) => normalizedBesselCore a v) := by
  intro v w hvw
  have hv := normalized_hasSum a v
  have hw := normalized_hasSum a w
  rw [← hv.tsum_eq,← hw.tsum_eq]
  apply Summable.tsum_lt_tsum (i := 1) (normalizedTerm_anti a hvw.le) _ hw.summable hv.summable
  rw [show 1 = 0+1 by rfl, normalizedTerm_succ, normalizedTerm_succ,
    normalizedTerm_zero,normalizedTerm_zero]
  simp only [Nat.cast_zero,zero_add,one_mul,add_zero]
  exact div_lt_div_of_pos_left (sq_pos_of_pos a.property) (order_base_pos v)
    (add_lt_add_right (show v.val < w.val from hvw) 1)

private def raiseOrder (v : Ioi (-1:ℝ)) : Ioi (-1:ℝ) :=
  ⟨v.val+1, by linarith [v.property]⟩

private def besselRealValue (a : Ioi (0:ℝ)) (v : Ioi (-1:ℝ)) :=
  (modifiedBesselIOrder (2*a.val) (v.val:ℂ)).re

private theorem scaledValue (a : Ioi (0:ℝ)) (v : Ioi (-1:ℝ)) :
    besselRealValue a v * Real.Gamma (v.val+1) =
      Real.exp (v.val*Real.log a.val) * normalizedBesselCore a v := by
  rw [besselRealValue,modifiedBessel_real_axis,Complex.ofReal_re]
  exact div_mul_cancel₀ _ (Real.Gamma_pos_of_pos (order_base_pos v)).ne'

/-- Ratio of the values at consecutive orders. -/
def realBesselOrderRatio (a : Ioi (0:ℝ)) (v : Ioi (-1:ℝ)) : ℝ :=
  besselRealValue a (raiseOrder v) / besselRealValue a v

private theorem ratio_pos (a : Ioi (0:ℝ)) (v : Ioi (-1:ℝ)) :
    0 < realBesselOrderRatio a v := div_pos
      (modifiedBessel_real_order_pos _ _) (modifiedBessel_real_order_pos _ _)

/-- Normalization transfers strict decrease to a sharp linear-in-argument upper bound
for the ratio at consecutive orders. -/
theorem realBesselOrderRatio_lt (a : Ioi (0:ℝ)) (v : Ioi (-1:ℝ)) :
    realBesselOrderRatio a v < a.val/(v.val+1) := by
  have h := normalizedBesselCore_strictAnti a
    (show v < raiseOrder v from show v.val < v.val+1 by linarith)
  have he := scaledValue a (raiseOrder v)
  change besselRealValue a (raiseOrder v) * Real.Gamma ((v.val+1)+1) =
    Real.exp ((v.val+1)*Real.log a.val) * normalizedBesselCore a (raiseOrder v) at he
  rw [Real.Gamma_add_one (order_base_pos v).ne', add_mul,one_mul,Real.exp_add,Real.exp_log a.property] at he
  have h₁ := mul_lt_mul_of_pos_left h (mul_pos (Real.exp_pos (v.val*Real.log a.val)) a.property)
  have h₂ := scaledValue a v
  apply (div_lt_div_iff₀ (modifiedBessel_real_order_pos a v) (order_base_pos v)).mpr
  by_contra! hrev
  have hmul := mul_le_mul_of_nonneg_right hrev (Real.Gamma_pos_of_pos (order_base_pos v)).le
  nlinarith only [hmul,h₁,he,congrArg (fun z : ℝ => a.val*z) h₂]

/-- The real-order recurrence gives the first step of the continued fraction. -/
theorem realBesselOrderRatio_reciprocal (a : Ioi (0:ℝ)) (v : Ioi (-1:ℝ)) :
    realBesselOrderRatio a v = a.val / (v.val+1 + a.val*realBesselOrderRatio a (raiseOrder v)) := by
  have h := modifiedBesselIOrder_recurrence (mul_pos (by norm_num : 0 < (2:ℝ)) a.property)
    (((v.val+1:ℝ):ℂ))
  rw [show ((v.val+1:ℝ):ℂ) + 1 = (((raiseOrder (raiseOrder v)).val:ℝ):ℂ) by push_cast; rfl,
    show ((v.val+1:ℝ):ℂ) - 1 = (v.val:ℂ) by push_cast; ring] at h
  have h₂ := congrArg Complex.re h
  have hcoef : (2:ℂ)*((v.val+1:ℝ):ℂ)/((2*a.val:ℝ):ℂ) = (((v.val+1)/a.val:ℝ):ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr a.property.ne']
    <;> ring
  rw [hcoef,Complex.sub_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.ofReal_re] at h₂
  change besselRealValue a (raiseOrder (raiseOrder v)) =
    besselRealValue a v - ((v.val+1)/a.val)*besselRealValue a (raiseOrder v) at h₂
  apply (eq_div_iff (add_pos (order_base_pos v) (mul_pos a.property (ratio_pos _ _))).ne').mpr
  dsimp only [realBesselOrderRatio]
  have ha : a.val ≠ 0 := ne_of_gt a.property
  have hv := (modifiedBessel_real_order_pos a v).ne'
  have hw := (modifiedBessel_real_order_pos a (raiseOrder v)).ne'
  change besselRealValue a v ≠ 0 at hv
  change besselRealValue a (raiseOrder v) ≠ 0 at hw
  field_simp [ha] at h₂
  field_simp [hv,hw]
  nlinarith only [h₂]

/-- The first two continued-fraction convergents enclose the ratio strictly at
every positive argument and every real order greater than minus one. -/
theorem realBesselOrderRatio_bounds (a : Ioi (0:ℝ)) (v : Ioi (-1:ℝ)) :
    realBesselOrderRatio a v ∈ Ioo
      (a.val/(v.val+1+a.val*(a.val/(v.val+2)))) (a.val/(v.val+1)) := by
  refine ⟨?_,realBesselOrderRatio_lt a v⟩
  rw [realBesselOrderRatio_reciprocal a v]
  have h := realBesselOrderRatio_lt a (raiseOrder v)
  change realBesselOrderRatio a (raiseOrder v) < a.val/((v.val+1)+1) at h
  rw [show (v.val+1)+1 = v.val+2 by ring] at h
  exact div_lt_div_of_pos_left a.property (add_pos (order_base_pos v) (mul_pos a.property (ratio_pos _ _)))
    (add_lt_add_left (mul_lt_mul_of_pos_left h a.property) _)

#print axioms modifiedBessel_real_order_pos
#print axioms normalizedBesselCore_strictAnti
#print axioms realBesselOrderRatio_reciprocal
#print axioms realBesselOrderRatio_bounds

end
end GaloisForLFunctions.HTGeometry
