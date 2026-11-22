import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.Divisor

/-!
# The secondary pole of the accepted partition

The full square partition loses a scaled zeta divisor only at exceptional
clock times. Its continuation has a double pole at one, and precisely at
those times it also has a simple pole at one half.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open DyadicAperture.Binary SampledClocks HTGeometry ZeroForcingCalculus
open scoped Classical

private def loss (t : ℝ) : ℂ → ℂ := if h : t ∈ exceptional then response ⟨t,h⟩ else 0

/-- Meromorphic continuation of the actual accepted binary heat trace. -/
def accepted (t : ℝ) : ℂ → ℂ := riemannZeta^2-loss t

private theorem loss_agrees (t : ℝ) (s : {z : ℂ // 1/2 < z.re}) : correction t s.val = loss t s.val := by
  by_cases h : t ∈ exceptional
  · simpa only [loss,dif_pos h] using response_eq_heat_sum ⟨t,h⟩ s
  · letI : IsEmpty {x // rejected t x} := ⟨fun x => h ⟨x.val,x.property⟩⟩
    simp [loss,h,correction,partition]

theorem accepted_trace (t : ℝ) (s : {z : ℂ // AbsoluteHeat (measured t Real.pi) z}) :
    ContinuousLinearMap.opTrace (sectorHeat (measured t Real.pi) s) = accepted t s.val := by
  have hs := (maximal_heat_iff t s.val).mp ((sectorHeat_iff _ _).mpr s.property)
  rw [maximal_trace,loss_agrees t ⟨s.val,by linarith only [hs]⟩]
  rfl

theorem accepted_meromorphic (t : ℝ) (s : ℂ) : MeromorphicAt (accepted t) s := by
  apply ((ZeroForcingCalculus.meromorphicAt_riemannZeta s).pow 2).sub
  by_cases h : t ∈ exceptional
  · simpa only [loss,dif_pos h] using response_meromorphic ⟨t,h⟩ s
  · rw [loss,dif_neg h]
    change MeromorphicAt (fun _ : ℂ => (0:ℂ)) s
    exact analyticAt_const.meromorphicAt

private theorem regular_loss (t : ℝ) (s : {z : ℂ // 0 < z.re}) (hs : s.val ≠ 1/2) : AnalyticAt ℂ (loss t) s.val := by
  by_cases h : t ∈ exceptional
  · have he : 2*s.val ≠ 1 := fun hz => hs (by linear_combination hz/2)
    simpa only [loss,dif_pos h] using response_regular ⟨t,h⟩ s he
  · rw [loss,dif_neg h]
    change AnalyticAt ℂ (fun _ : ℂ => (0:ℂ)) s.val
    exact analyticAt_const

theorem accepted_one (t : ℝ) : meromorphicOrderAt (accepted t) 1 = ((-2 : ℤ) : WithTop ℤ) := by
  have hz := ZeroForcingCalculus.meromorphicAt_riemannZeta 1
  have ho : meromorphicOrderAt (riemannZeta^2) 1 = ((-2 : ℤ) : WithTop ℤ) := by
    rw [sq,meromorphicOrderAt_mul hz hz,meromorphicOrderAt_riemannZeta_one]
    exact_mod_cast (by norm_num : (-1:ℤ) + (-1) = -2)
  have hl := (regular_loss t ⟨1,by norm_num⟩ (by norm_num)).neg
  change AnalyticAt ℂ (-loss t) 1 at hl
  rw [accepted,sub_eq_add_neg,meromorphicOrderAt_add_eq_left_of_lt hl.meromorphicAt,ho]
  exact ho.trans_lt ((WithTop.coe_lt_coe.mpr (by norm_num : (-2:ℤ) < 0)).trans_le hl.meromorphicOrderAt_nonneg)

theorem accepted_half (t : ℝ) : meromorphicOrderAt (accepted t) (1/2) =
    if t ∈ exceptional then ((-1 : ℤ) : WithTop ℤ) else 0 := by
  have ha := (HTGeometry.analyticAt_riemannZeta (by norm_num : (1/2:ℂ) ≠ 1)).pow 2
  have hn : riemannZeta (1/2:ℂ) ≠ 0 := by
    simpa using _root_.RHTower.riemannZeta_real_strip_ne_zero (σ := (1/2:ℝ)) (by norm_num) (by norm_num)
  have hz : meromorphicOrderAt (riemannZeta^2) (1/2) = 0 := meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero ha (pow_ne_zero 2 hn)
  by_cases h : t ∈ exceptional
  · have he : meromorphicOrderAt (-loss t) (1/2) = ((-1 : ℤ) : WithTop ℤ) := by
      rw [← meromorphicOrderAt_neg,loss,dif_pos h]
      exact response_critical_pole ⟨t,h⟩
    rw [if_pos h,accepted,sub_eq_add_neg,add_comm,meromorphicOrderAt_add_eq_left_of_lt ha.meromorphicAt,he]
    rw [he,hz]
    exact WithTop.coe_lt_coe.mpr (by norm_num : (-1:ℤ) < 0)
  · simpa only [accepted,loss,dif_neg h,sub_zero,if_neg h] using hz

/-- Complete pole set in the open positive half-plane, including the exceptional secondary pole. -/
theorem accepted_pole_iff (t : ℝ) (s : {z : ℂ // 0 < z.re}) :
    meromorphicOrderAt (accepted t) s.val < 0 ↔ s.val = 1 ∨ s.val = 1/2 ∧ t ∈ exceptional := by
  by_cases h : s.val = 1
  · rw [h,accepted_one]
    exact iff_of_true (WithTop.coe_lt_coe.mpr (by norm_num : (-2:ℤ) < 0)) (Or.inl rfl)
  by_cases hh : s.val = 1/2
  · rw [hh,accepted_half]
    by_cases he : t ∈ exceptional
    · rw [if_pos he]
      exact iff_of_true (WithTop.coe_lt_coe.mpr (by norm_num : (-1:ℤ) < 0)) (Or.inr ⟨rfl,he⟩)
    · norm_num [he]
  · have hr : AnalyticAt ℂ (accepted t) s.val := ((HTGeometry.analyticAt_riemannZeta h).pow 2).sub (regular_loss t s hh)
    simp only [h,hh,false_and,or_self,iff_false]
    exact not_lt.mpr hr.meromorphicOrderAt_nonneg

#print axioms accepted_trace
#print axioms accepted_meromorphic
#print axioms accepted_one
#print axioms accepted_half
#print axioms accepted_pole_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
