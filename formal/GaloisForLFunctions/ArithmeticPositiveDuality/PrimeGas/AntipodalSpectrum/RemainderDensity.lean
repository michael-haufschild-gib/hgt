import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RemainderCounting
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RemainderPartition
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalResidueState
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Counting density and thermal residue of the remaining square shells

The digit error is sublinear in the square-root cutoff. The resulting
density agrees with the residue obtained by approaching the trace-class
boundary in the doubled inverse temperature.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks CopyExchange DyadicAperture.Binary Filter
open scoped Topology

private theorem sum_digits_bound {C X : ℕ} (hC : 1 < C) (hX : X ≠ 0) :
    (C.digits X).sum ≤ C*(Nat.log C X+1) := by
  have h := (C.digits X).sum_le_card_nsmul C (fun _ hd => (Nat.digits_lt_base hC hd).le)
  simpa only [nsmul_eq_mul,Nat.cast_id,Nat.length_digits _ _ hC hX,Nat.mul_comm] using h

private theorem digits_sublinear (C : ℕ) (hC : 1 < C) :
    Tendsto (fun n : ℕ => ((C.digits n).sum:ℝ)/n) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log n/n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hinv : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ => (C:ℝ)*((Real.logb C n+1)/n)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (C:ℝ))).mul ((hlog.div_const (Real.log C)).add hinv)
    simp only [zero_div,zero_add,mul_zero] at h
    apply h.congr
    intro n
    rw [Real.logb]
    ring
  apply squeeze_zero' (Eventually.of_forall (fun n : ℕ => by positivity)) _ hlim
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hbound : ((C.digits n).sum:ℝ) ≤ (C:ℝ)*(Real.logb C n+1) := by
    have hh := sum_digits_bound hC hn.ne'
    have h₁ : ((C.digits n).sum:ℝ) ≤ (C:ℝ)*((Nat.log C n:ℕ)+1:ℝ) := by exact_mod_cast hh
    exact h₁.trans (mul_le_mul_of_nonneg_left (add_le_add_left (Real.natLog_le_logb n C) 1) (Nat.cast_nonneg _))
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hbound (Nat.cast_nonneg n)

theorem remainder_count_density (t : ExceptionalTime) (j : ℕ) :
    Tendsto (fun X : ℕ => (Nat.card (countingStates t j X):ℝ)/X) atTop
      (𝓝 (2/((tailRadix t j).val-1:ℝ))) := by
  let C := (tailRadix t j).val
  have hC := radix_gt_one t j
  have hC' : (1:ℝ) < C := by exact_mod_cast hC
  have h := ((tendsto_const_nhds (x := (2:ℝ))).mul
    ((tendsto_const_nhds (x := (1:ℝ))).sub (digits_sublinear C hC))).div_const ((C:ℝ)-1)
  simp only [sub_zero,mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with X hX
  have he := congrArg (fun n : ℕ => (n:ℝ)) (count_digit_law t j X)
  change (((C-1)*Nat.card (countingStates t j X):ℕ):ℝ) = ((2*(X-(C.digits X).sum):ℕ):ℝ) at he
  simp only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ C from hC.le),Nat.cast_sub (Nat.digit_sum_le C X),
    Nat.cast_one,Nat.cast_ofNat] at he
  change 2*(1-((C.digits X).sum:ℝ)/X)/((C:ℝ)-1) = (Nat.card (countingStates t j X):ℝ)/X
  field_simp [Nat.cast_ne_zero.mpr hX.ne',sub_ne_zero.mpr hC'.ne']
  linear_combination -he

private theorem heat_powers (s : ℂ) (A : ℕ+) (k : ℕ) : heat s (A^k) = (heat s A)^k := by
  induction k with
  | zero => simp [heat,energy]
  | succ k ih => rw [pow_succ,heat_mul,ih,pow_succ]

theorem winding_half_temperature (t : ExceptionalTime) (j : ℕ) (z : ℂ) :
    windingWeight t j (z/2) = heat z (tailRadix t j) := by
  rw [windingWeight,← heat_powers,← radix_sq,pow_two,heat_mul,← heat_add,add_halves]

/-- Normalizing the physical trace by b−1 gives the same density at the critical pole. -/
theorem remainder_thermal_residue (t : ExceptionalTime) (j : ℕ) :
    Tendsto (fun b : TraceTemperature => ((b.val:ℂ)-1)*partition (remainder t j) ((b.val:ℂ)/2))
      atPartitionPole (𝓝 (2/((tailRadix t j).val-1:ℂ))) := by
  let C := tailRadix t j
  have hc : (C.val:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr C.ne_zero
  have hc' : (C.val:ℂ) ≠ 1 := by exact_mod_cast (radix_gt_one t j).ne'
  have he : heat 1 C = (C.val:ℂ)⁻¹ := by rw [heat_eq_cpow,Complex.cpow_neg_one]
  have hden : (1:ℂ)-heat 1 C ≠ 0 := by rw [he,sub_ne_zero]; exact fun h => hc' (inv_eq_one.mp h.symm)
  have hcont : Continuous (fun z : ℂ => heat z C) := (continuous_neg.mul continuous_const).cexp
  have hβ := tendsto_temperature_punctured.mono_right nhdsWithin_le_nhds
  have hq := (hcont.tendsto 1).comp hβ
  have hf := ((tendsto_const_nhds (x := (2:ℂ))).mul hq).div ((tendsto_const_nhds (x := (1:ℂ))).sub hq) hden
  have h := (riemannZeta_residue_one.comp tendsto_temperature_punctured).mul hf
  have heq : (1:ℂ)*(2*heat 1 C/(1-heat 1 C)) = 2/((C.val:ℂ)-1) := by
    rw [he,one_mul]
    field_simp [hc,sub_ne_zero.mpr hc']
  rw [heq] at h
  apply h.congr
  intro b
  have hs : 1/2 < ((b.val:ℂ)/2).re := by rw [Complex.div_ofNat_re,Complex.ofReal_re]; linarith only [b.property]
  rw [remainder_partition t j ⟨(b.val:ℂ)/2,hs⟩,winding_half_temperature]
  change (((b.val:ℂ)-1)*riemannZeta (b.val:ℂ))*(2*heat (b.val:ℂ) C/(1-heat (b.val:ℂ) C)) = _
  rw [show 2*((b.val:ℂ)/2) = b.val by ring]
  ring

#print axioms remainder_count_density
#print axioms winding_half_temperature
#print axioms remainder_thermal_residue

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
