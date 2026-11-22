import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedShift.TraceCorrection

/-!
# Translating the balanced digit recurrence

The quadratic correction leaves a copy of the original partition at
s+1. The mean digit determines the shift which cancels this copy.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift

open BalancedContinuation

abbrev base (t : ExceptionalTime) (j : ℕ) : ℝ := ((BalancedContinuation.dilation t j).val:ℝ)

/-- Shift making the signed child displacements symmetric. -/
def center (t : ExceptionalTime) (j : ℕ) := 1/(2*((radix t j:ℝ)+1))

def digitMoment (t : ExceptionalTime) (j : ℕ) := ∑ d : Fin (radix t j), (d.val:ℂ)

def quadraticNumerator (t : ExceptionalTime) (j : ℕ) (s : ℂ) :=
  firstHeat t j s+∑ d : Fin (radix t j), correctionTrace t j (base t j) (d.val:ℝ) s

theorem base_pos (t : ExceptionalTime) (j : ℕ) : 0 < base t j := by exact_mod_cast (BalancedContinuation.dilation t j).pos

theorem base_sq (t : ExceptionalTime) (j : ℕ) : base t j = (radix t j:ℝ)^2 := by
  simp only [base,BalancedContinuation.dilation,PNat.pow_coe,Nat.cast_pow]

theorem center_pos (t : ExceptionalTime) (j : ℕ) : 0 < center t j := by unfold center; positivity

/-- The digit first moment equals the centering shift times the number of branches and scale gap. -/
theorem center_balance (t : ExceptionalTime) (j : ℕ) :
    (center t j:ℂ)*(radix t j:ℂ)*((base t j:ℂ)-1) = digitMoment t j := by
  let C := radix t j
  have hC : 1 ≤ C := (radix_gt_one t j).le
  have h := congrArg (fun n : ℕ => (n:ℂ)) (Finset.sum_range_id_mul_two C)
  simp only [Nat.cast_mul,Nat.cast_sum,Nat.cast_sub hC,Nat.cast_one,Nat.cast_ofNat] at h
  have hsum : digitMoment t j*2 = (C:ℂ)*((C:ℂ)-1) := by
    rw [digitMoment,Fin.sum_univ_eq_sum_range (fun k : ℕ => (k:ℂ))]
    exact h
  have hne : (C:ℂ)+1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero C)
  rw [center,base_sq]
  push_cast
  change 1/(2*((C:ℂ)+1))*C*((C:ℂ)^2-1) = _
  field_simp [hne]
  linear_combination -((C:ℂ)+1)*hsum

theorem scale_weight (t : ExceptionalTime) (j : ℕ) (s : ℂ) :
    denominator t j s = 1-(radix t j:ℂ)*weight (base t j) s := by
  let l := (logRadix t j).val
  have hB : energy (BalancedContinuation.dilation t j) = 2*l := by rw [BalancedContinuation.dilation,pow_two,energy_mul,two_mul]; rfl
  have hC : Complex.exp (l:ℂ) = (radix t j:ℂ) := by
    rw [← Complex.ofReal_exp]
    change ((Real.exp (Real.log (radix t j:ℝ)):ℝ):ℂ) = _
    rw [Real.exp_log (by exact_mod_cast (tailRadix t j).pos : 0 < (radix t j:ℝ)),Complex.ofReal_natCast]
  have hz : -(s-((1/2:ℝ):ℂ))*(2*(l:ℂ)) = (l:ℂ)+(-s)*(2*(l:ℂ)) := by push_cast; ring
  change 1-Complex.exp (-(s-((1/2:ℝ):ℂ))*(2*(l:ℂ))) = _
  rw [hz,Complex.exp_add,hC,weight_heat (BalancedContinuation.dilation t j) s,heat,hB,Complex.ofReal_mul,Complex.ofReal_ofNat]

/-- The change of scale denominator under s↦s+1 measures exactly the digit first moment. -/
theorem scale_difference (t : ExceptionalTime) (j : ℕ) (s : ℂ) :
    (center t j:ℂ)*(denominator t j (s+1)-denominator t j s) =
      digitMoment t j*weight (base t j) (s+1) := by
  have hb := base_pos t j
  have h : weight (base t j) s = (base t j:ℂ)*weight (base t j) (s+1) := by
    rw [weight_succ hb]
    field_simp [Complex.ofReal_ne_zero.mpr hb.ne']
  rw [scale_weight,scale_weight,h,← center_balance]
  ring

private theorem digit_term (t : ExceptionalTime) (j : ℕ) (d : Fin (radix t j)) (x : Label t j) (s : ℂ) :
    correction t j d x s = remainder (base t j) (d.val:ℝ) (labelValue x) s -
      (s*(d.val:ℂ)*weight (base t j) (s+1))*balancedHeat t j (s+1) x := by
  rw [correction,remainder,← weight_heat,child_value,Nat.cast_add,Nat.cast_mul,
    ← weight_heat,← weight_label,← weight_label]
  change weight ((d.val:ℝ)+base t j*labelValue x) s-weight (base t j) s*weight (labelValue x) s = _
  rw [add_comm (d.val:ℝ),weight_mul (base_pos t j).le (zero_le_one.trans (label_one_le x)),
    weight_mul (base_pos t j).le (zero_le_one.trans (label_one_le x)),Complex.ofReal_natCast]
  ring

theorem digit_expansion (t : ExceptionalTime) (j : ℕ) (w : {s : ℂ // -(1/2) < s.re}) :
    quadraticNumerator t j w.val = numerator t j w.val+
      w.val*(digitMoment t j*weight (base t j) (w.val+1))*balancedPartition t j (w.val+1) := by
  let s := w.val
  let B := base t j
  let P := balancedPartition t j (s+1)
  have hH := ((balanced_heat_summable_iff t j (s+1)).mpr
    (by rw [Complex.add_re,Complex.one_re]; dsimp only [s]; linarith only [w.property])).of_norm
  have hd (d : Fin (radix t j)) : (∑' x : Label t j, correction t j d x s) =
      correctionTrace t j B (d.val:ℝ) s - (d.val:ℂ)*(s*weight B (s+1)*P) := by
    have hR := remainder_summable t j (b := B) (a := (d.val:ℝ)) (base_pos t j)
      (add_pos_of_pos_of_nonneg (base_pos t j) (Nat.cast_nonneg _))
      ⟨s,by dsimp only [s]; linarith only [w.property]⟩
    simp_rw [digit_term t j d _ s]
    rw [Summable.tsum_sub hR (hH.mul_left _),tsum_mul_left]
    change correctionTrace t j B (d.val:ℝ) s - _*P = _
    ring
  change firstHeat t j s+_ = (firstHeat t j s+∑ d, ∑' x, correction t j d x s)+_
  simp only [hd,Finset.sum_sub_distrib,← Finset.sum_mul]
  change firstHeat t j s+_ = firstHeat t j s+(_-digitMoment t j*(s*weight B (s+1)*P))+_
  ring

theorem quadratic_analytic (t : ExceptionalTime) (j : ℕ) (w : {s : ℂ // -(3/2) < s.re}) :
    AnalyticAt ℂ (quadraticNumerator t j) w.val := by
  apply AnalyticAt.add
  · apply Finset.analyticAt_fun_sum
    intro d _
    exact analyticAt_cexp.comp ((analyticAt_id.neg).mul analyticAt_const)
  · exact Finset.analyticAt_fun_sum _ (fun d _ => correction_analytic t j (base_pos t j)
      (add_pos_of_pos_of_nonneg (base_pos t j) (Nat.cast_nonneg d.val)) w)

/-- Analytic background on the second clock line. -/
def background (t : ExceptionalTime) (j : ℕ) (a : ℝ) (s : ℂ) :=
  correctionTrace t j 1 a s + (quadraticNumerator t j s -
    s*(center t j:ℂ)*numerator t j (s+1))/denominator t j s

/-- Two-strip continuation of the shifted balanced partition. -/
def extension (t : ExceptionalTime) (j : ℕ) (a : ℝ) (s : ℂ) :=
  background t j a s+s*((center t j:ℂ)-(a:ℂ))*continuation t j (s+1)

theorem scale_right (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1/2 < z.re}) :
    denominator t j s.val ≠ 0 := by
  intro hz
  obtain ⟨k,hk⟩ := (scaleFactor_zero_iff (logRadix t j) s.val).mp hz
  exact s.property.ne' (congrArg Complex.re hk)

/-- On the absolute convergence half-plane, the numerator is the physical partition times the scale denominator. -/
theorem physical_num (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1/2 < z.re}) :
    numerator t j s.val = denominator t j s.val*balancedPartition t j s.val := by
  have h := (div_eq_iff (scale_right t j s)).mp (continuation_agrees t j s)
  exact h.trans (mul_comm _ _)

theorem extension_agrees (t : ExceptionalTime) (j : ℕ) (a : {v : ℝ // -1 < v})
    (s : {z : ℂ // 1/2 < z.re}) : extension t j a.val s.val = partition t j a.val s.val := by
  let w := s.val
  have h₁ : 1/2 < (w+1).re := by rw [Complex.add_re,Complex.one_re]; dsimp only [w]; linarith only [s.property]
  have hx := digit_expansion t j ⟨w,by dsimp only [w]; linarith only [s.property]⟩
  change quadraticNumerator t j w = numerator t j w+_*_*_ at hx
  rw [← scale_difference,physical_num t j s] at hx
  have hb : (quadraticNumerator t j w-w*(center t j:ℂ)*numerator t j (w+1))/denominator t j w =
      balancedPartition t j w-w*(center t j:ℂ)*balancedPartition t j (w+1) := by
    apply (div_eq_iff (scale_right t j s)).mpr
    rw [hx,physical_num t j ⟨w+1,h₁⟩]
    ring
  rw [(physical_translation t j a s).2,extension,background]
  change correctionTrace t j 1 a.val w+_+w*_*continuation t j (w+1) = _
  rw [hb,continuation_agrees t j ⟨w+1,h₁⟩]
  ring

#print axioms center_balance
#print axioms digit_expansion
#print axioms extension_agrees

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift
