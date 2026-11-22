import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.Partition

/-!
# Inverting the rejected trace at unit inverse temperature

The normalized trace lies strictly between the reciprocals of consecutive
integers. This determines its lowest block, after which the same reading
recovers the winding order by strict monotonicity.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks DyadicAperture.Binary

/-- The unit-temperature trace divided by twice the radial partition. -/
def reading (H : ℕ+) (m : ℕ) : ℝ := 1/((H.val:ℝ)-1)-1/((H.val:ℝ)^m-1)

private theorem reciprocal_difference {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    (x⁻¹-y⁻¹)/((1-x⁻¹)*(1-y⁻¹)) = 1/(x-1)-1/(y-1) := by
  have rearrange (z : ℝ) (hz : 1 < z) : 1-z⁻¹ = (z-1)/z := by
    field_simp [ne_of_gt (lt_trans zero_lt_one hz)]
  rw [rearrange x hx,rearrange y hy]
  field_simp [ne_of_gt (lt_trans zero_lt_one hx),ne_of_gt (lt_trans zero_lt_one hy),
    sub_ne_zero.mpr hx.ne',sub_ne_zero.mpr hy.ne']
  ring

private theorem real_weight (x : ℝ) (hx : 1 < x) (m : ℕ) (hm : 1 < m) :
    2*x⁻¹*(1-(x⁻¹)^(m-1))/((1-x⁻¹)*(1-(x⁻¹)^m)) = 2*(1/(x-1)-1/(x^m-1)) := by
  have hpow : x⁻¹*(x⁻¹)^(m-1) = (x^m)⁻¹ := by
    rw [← pow_succ',Nat.sub_add_cancel hm.le,inv_pow]
  have hnum : 2*x⁻¹*(1-(x⁻¹)^(m-1)) = 2*(x⁻¹-(x^m)⁻¹) := by
    rw [← hpow]; ring
  rw [hnum,inv_pow,mul_div_assoc,reciprocal_difference hx (one_lt_pow₀ hx (by omega))]

theorem unit_trace_formula (t : ExceptionalTime) :
    response t 1 = (riemannZeta 2*2)*(reading (block t) (windingOrder t) : ℂ) := by
  let H := block t
  let m := windingOrder t
  have hH : (1:ℝ) < H.val := by exact_mod_cast block_nontrivial t
  have hr := congrArg Complex.ofReal (real_weight (H.val:ℝ) hH m (order_nontrivial t))
  push_cast at hr
  unfold response
  rw [mul_one,heat_eq_cpow,Complex.cpow_neg_one,mul_assoc]
  apply congrArg (riemannZeta 2 * ·)
  unfold factor reading
  push_cast
  exact hr

private def unitTemperature (t : ExceptionalTime) : {s : ℂ // AbsoluteHeat (rejected t.val) s} :=
  ⟨1,(sectorHeat_iff _ _).mp ((rejected_heat_iff _ _).mpr fun _ => by norm_num)⟩

def unitTrace (t : ExceptionalTime) : ℂ :=
  ContinuousLinearMap.opTrace (sectorHeat (rejected t.val) (unitTemperature t))

theorem unitTrace_eq (t : ExceptionalTime) : unitTrace t = response t 1 := response_trace t (unitTemperature t)

def normalizedUnitTrace (t : ExceptionalTime) : ℝ := (unitTrace t/(riemannZeta 2*2)).re

theorem normalizedUnitTrace_eq (t : ExceptionalTime) :
    normalizedUnitTrace t = reading (block t) (windingOrder t) := by
  have hz : riemannZeta (2:ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num)
  unfold normalizedUnitTrace
  rw [unitTrace_eq,unit_trace_formula,mul_comm (riemannZeta 2*2),mul_div_cancel_right₀ _ (mul_ne_zero hz two_ne_zero)]
  rfl

/-- The lowest block is read from disjoint reciprocal intervals. -/
theorem reading_interval (H : ℕ+) (m : ℕ) (hH : 1 < H.val) (hm : 1 < m) :
    1/(H.val:ℝ) < reading H m ∧ reading H m < 1/((H.val:ℝ)-1) := by
  let x : ℝ := H.val
  have hx : 1 < x := by change (1:ℝ) < (H.val:ℝ); exact_mod_cast hH
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hp : x^2 ≤ x^m := pow_le_pow_right₀ hx.le (by omega)
  have hg : x*(x-1) < x^m-1 := by nlinarith only [hp,hx]
  have hpos := mul_pos hx₀ (sub_pos.mpr hx)
  have hi := one_div_lt_one_div_of_lt hpos hg
  have hdiff : 1/(x-1)-1/x = 1/(x*(x-1)) := by
    field_simp [hx₀.ne',sub_ne_zero.mpr hx.ne']
    ring
  change 1/x < 1/(x-1)-1/(x^m-1) ∧ 1/(x-1)-1/(x^m-1) < 1/(x-1)
  exact ⟨by linarith only [hdiff,hi],sub_lt_self _ (one_div_pos.mpr (hpos.trans hg))⟩

/-- The ceiling of the reciprocal normalized operator trace is the lowest product. -/
theorem recover_block (t : ExceptionalTime) : ⌈1/normalizedUnitTrace t⌉ = ((block t).val : ℤ) := by
  rw [normalizedUnitTrace_eq,Int.ceil_eq_iff,Int.cast_natCast]
  have hx : (1:ℝ) < (block t).val := by exact_mod_cast block_nontrivial t
  have h₀ := zero_lt_one.trans hx
  obtain ⟨hl,hr⟩ := reading_interval _ _ (block_nontrivial t) (order_nontrivial t)
  have hu := (one_div_pos.mpr h₀).trans hl
  exact ⟨(lt_div_iff₀ hu).mpr (by simpa only [mul_comm] using (lt_div_iff₀ (sub_pos.mpr hx)).mp hr),
    (div_le_iff₀ hu).mpr (by simpa only [mul_comm] using ((div_lt_iff₀ h₀).mp hl).le)⟩

theorem recover_block_power (t : ExceptionalTime) : ((block t).val:ℝ)^(windingOrder t) =
    1+1/(1/(((block t).val:ℝ)-1)-normalizedUnitTrace t) := by
  rw [normalizedUnitTrace_eq,reading,sub_sub_cancel]
  simp only [one_div,inv_inv]
  ring

private theorem reading_strict (H : ℕ+) (hH : 1 < H.val) {m n : ℕ} (hm : 1 < m) (hmn : m < n) :
    reading H m < reading H n := by
  have hx : (1:ℝ) < H.val := by exact_mod_cast hH
  have hm' : (1:ℝ) < (H.val:ℝ)^m := one_lt_pow₀ hx (by omega)
  exact sub_lt_sub_left (one_div_lt_one_div_of_lt (sub_pos.mpr hm')
    (sub_lt_sub_right (pow_lt_pow_right₀ hx hmn) 1)) _

private theorem height_separates {H K : ℕ+} {m n : ℕ} (hH : 1 < H.val) (hK : 1 < K.val)
    (hm : 1 < m) (hn : 1 < n) (h : H.val < K.val) : reading K n < reading H m := by
  have hgap : (H.val:ℝ) ≤ (K.val:ℝ)-1 := by
    have hcast : (H.val:ℝ)+1 ≤ (K.val:ℝ) := by exact_mod_cast h
    linarith only [hcast]
  exact ((reading_interval K n hK hn).2.trans_le
    (one_div_le_one_div_of_le (Nat.cast_pos.mpr H.pos) hgap)).trans (reading_interval H m hH hm).1

/-- One actual trace reading distinguishes every pair of different spectral parameters. -/
theorem unit_trace_eq_iff (t u : ExceptionalTime) : response t 1 = response u 1 ↔
    block t = block u ∧ windingOrder t = windingOrder u := by
  constructor
  · intro hr
    rw [unit_trace_formula,unit_trace_formula] at hr
    have hz : riemannZeta (2:ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num)
    have he := Complex.ofReal_injective (mul_left_cancel₀ (mul_ne_zero hz two_ne_zero) hr)
    have hB : block t = block u := by
      apply PNat.coe_injective
      apply le_antisymm
      · exact le_of_not_gt (fun h => (height_separates (block_nontrivial u) (block_nontrivial t)
          (order_nontrivial u) (order_nontrivial t) h).ne he)
      · exact le_of_not_gt (fun h => (height_separates (block_nontrivial t) (block_nontrivial u)
          (order_nontrivial t) (order_nontrivial u) h).ne he.symm)
    rw [hB] at he
    refine ⟨hB,le_antisymm ?_ ?_⟩
    · exact le_of_not_gt fun h => (reading_strict _ (block_nontrivial u) (order_nontrivial u) h).ne he.symm
    · exact le_of_not_gt fun h => (reading_strict _ (block_nontrivial u) (order_nontrivial t) h).ne he
  · rintro ⟨hB,hm⟩
    rw [unit_trace_formula,unit_trace_formula,hB,hm]

theorem response_eq_iff_unit (t u : ExceptionalTime) : response t = response u ↔ response t 1 = response u 1 := by
  refine ⟨fun h => congrFun h 1,fun h => ?_⟩
  obtain ⟨hB,hm⟩ := (unit_trace_eq_iff t u).mp h
  funext s
  simp only [response,hB,hm]

theorem operator_trace_determines_response (t u : ExceptionalTime) : unitTrace t = unitTrace u ↔ response t = response u := by
  rw [unitTrace_eq,unitTrace_eq,response_eq_iff_unit]

#print axioms unit_trace_formula
#print axioms reading_interval
#print axioms recover_block
#print axioms recover_block_power
#print axioms unit_trace_eq_iff
#print axioms response_eq_iff_unit
#print axioms operator_trace_determines_response

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
