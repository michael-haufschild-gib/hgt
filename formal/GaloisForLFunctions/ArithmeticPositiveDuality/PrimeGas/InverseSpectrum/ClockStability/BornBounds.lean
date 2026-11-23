import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.ParabolicBudget
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.SharpTail

/-! # Sharp rank dependence of the amplitude-to-probability comparison -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

theorem detectorError_nonneg (f : SpectralResponse) {r q : ℕ} (b : SpectralBand r) (c : SpectralBand q) :
    0 ≤ detectorError f b c := tsum_nonneg (fun _ => abs_nonneg _)

/-- Squaring the total amplitude error costs at most the missing dimension times the total Born error. -/
theorem amplitude_sq_le_rank_mul_born (β : GibbsExponent) {r : ℕ} (b c : SpectralBand r) :
    detectorError (powerResponse β) b c ^ 2 ≤ (r:ℝ) * detectorError (powerResponse (doubleExponent β)) b c := by
  by_cases hr : r = 0
  · subst r
    have hu := detectorTail_le (powerResponse β) b c 0
    have he : detectorError (powerResponse β) b c = 0 := le_antisymm
      (by simpa only [detectorError,tailCeiling,Finset.range_zero,Finset.sum_empty] using hu)
      (detectorError_nonneg _ _ _)
    rw [he,Nat.cast_zero,zero_pow two_ne_zero,zero_mul]
  · let X := detectorError (powerResponse β) b c
    let Y := detectorError (powerResponse (doubleExponent β)) b c
    have hX : 0 ≤ X := detectorError_nonneg _ _ _
    have hp : 0 < (r:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
    have ht := amplitude_linear_budget β b c (div_nonneg hX hp.le)
    change 2*(X/(r:ℝ))*X ≤ Y+(r:ℝ)*(X/(r:ℝ))^2 at ht
    have h : 2*X^2 ≤ (r:ℝ)*Y+X^2 := calc
      _ = (r:ℝ)*(2*(X/(r:ℝ))*X) := by field_simp [hp.ne']
      _ ≤ (r:ℝ)*(Y+(r:ℝ)*(X/(r:ℝ))^2) := mul_le_mul_of_nonneg_left ht hp.le
      _ = _ := by field_simp [hp.ne']
    change X^2 ≤ (r:ℝ)*Y
    linarith only [h]

theorem born_le_twice_amplitude (β : GibbsExponent) {r : ℕ} (b c : SpectralBand r) :
    detectorError (powerResponse (doubleExponent β)) b c ≤ 2 * detectorError (powerResponse β) b c := by
  have he (n : ℕ) : levelError (powerResponse (doubleExponent β)) b c n ≤ 2*levelError (powerResponse β) b c n := by
    let x := (b n).val^β.val
    let y := (c n).val^β.val
    have hx : 0 ≤ x := Real.rpow_nonneg (band_in_unit b n).1 _
    have hy : 0 ≤ y := Real.rpow_nonneg (band_in_unit c n).1 _
    have hx' : x ≤ 1 := Real.rpow_le_one (band_in_unit b n).1 (band_in_unit b n).2 β.property.le
    have hy' : y ≤ 1 := Real.rpow_le_one (band_in_unit c n).1 (band_in_unit c n).2 β.property.le
    change |(b n).val^(doubleExponent β).val - (c n).val^(doubleExponent β).val| ≤ 2*|x-y|
    rw [power_doubleExponent β (band_in_unit b n).1,power_doubleExponent β (band_in_unit c n).1]
    change |x^2-y^2| ≤ _
    rw [show x^2-y^2 = (x+y)*(x-y) by ring,abs_mul,abs_of_nonneg (add_nonneg hx hy)]
    exact mul_le_mul_of_nonneg_right (by linarith only [hx',hy']) (abs_nonneg _)
  have ht := (summable_levelError (powerResponse (doubleExponent β)) b c).tsum_le_tsum he
    ((summable_levelError (powerResponse β) b c).mul_left 2)
  rw [tsum_mul_left] at ht
  exact ht

private theorem edge_power_error (β : GibbsExponent) (r : ℕ) :
    detectorError (powerResponse β) (hotEdge r) (coldEdge r) = ∑ j ∈ Finset.range r, occupationWeight j^β.val := by
  rw [detectorError,detectorTail_edges]
  simp only [tailCeiling,powerResponse,Nat.zero_add,Real.zero_rpow β.property.ne',sub_zero]

/-- A global rank-one factor is valid at a fixed positive temperature precisely when it is at least one. -/
theorem rankOne_born_factor_iff (β : GibbsExponent) (K : ℝ) :
    (∀ (P Q : Projection) (hP : MissingDimension P 1) (cP : Conserving (projected P))
      (hQ : MissingDimension Q 1) (cQ : Conserving (projected Q)),
      detectorError (powerResponse β) (physicalSpectrum P hP cP) (physicalSpectrum Q hQ cQ) ^ 2 ≤
      K * detectorError (powerResponse (doubleExponent β)) (physicalSpectrum P hP cP) (physicalSpectrum Q hQ cQ)) ↔ 1 ≤ K := by
  constructor
  · intro h
    have he := edgePair_mem_closed_of_physical 0 (isClosed_le ((continuous_detectorError (powerResponse β) 1).pow 2)
      (continuous_const.mul (continuous_detectorError (powerResponse (doubleExponent β)) 1))) h
    change detectorError (powerResponse β) (hotEdge 1) (coldEdge 1)^2 ≤ K * detectorError _ (hotEdge 1) (coldEdge 1) at he
    simpa only [edge_power_error,Finset.sum_range_one,occupationWeight_zero,Real.one_rpow,one_pow,mul_one] using he
  · intro h P Q hP cP hQ cQ
    have ht := amplitude_sq_le_rank_mul_born β (physicalSpectrum P hP cP) (physicalSpectrum Q hQ cQ)
    rw [Nat.cast_one,one_mul] at ht
    exact ht.trans (le_mul_of_one_le_left (detectorError_nonneg _ _ _) h)

private theorem edge_error_tendsto_rank (r : ℕ) {β : ℕ → GibbsExponent}
    (hβ : Tendsto (fun n => (β n).val) atTop (𝓝 0)) :
    Tendsto (fun n => detectorError (powerResponse (β n)) (hotEdge r) (coldEdge r)) atTop (𝓝 (r:ℝ)) := by
  have h (j : ℕ) : Tendsto (fun n => occupationWeight j^(β n).val) atTop (𝓝 1) := by
    have ht : Tendsto (fun n => occupationWeight j^(β n).val) atTop (𝓝 (occupationWeight j^(0:ℝ))) :=
      (Real.continuousAt_const_rpow (b := 0) (occupationWeight_pos j).ne').tendsto.comp hβ
    simpa only [Real.rpow_zero] using ht
  simpa only [edge_power_error,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] using
    tendsto_finsetSum (Finset.range r) (fun j _ => h j)

/-- Uniformly over positive temperatures, the exact best physical factor at missing dimension r+1 is r+1. -/
theorem uniform_born_factor_iff (r : ℕ) (K : ℝ) :
    (∀ (β : GibbsExponent) (P Q : Projection) (hP : MissingDimension P (r+1)) (cP : Conserving (projected P))
      (hQ : MissingDimension Q (r+1)) (cQ : Conserving (projected Q)),
      detectorError (powerResponse β) (physicalSpectrum P hP cP) (physicalSpectrum Q hQ cQ)^2 ≤
      K * detectorError (powerResponse (doubleExponent β)) (physicalSpectrum P hP cP) (physicalSpectrum Q hQ cQ)) ↔
      ((r+1 : ℕ):ℝ) ≤ K := by
  constructor
  · intro h
    let β (n : ℕ) : GibbsExponent := ⟨occupationWeight n,occupationWeight_pos n⟩
    have hb : Tendsto (fun n => (β n).val) atTop (𝓝 0) := occupationWeight_tendsto
    have hd : Tendsto (fun n => (doubleExponent (β n)).val) atTop (𝓝 0) := by
      simpa only [doubleExponent,zero_mul] using hb.mul_const 2
    have he (n : ℕ) : detectorError (powerResponse (β n)) (hotEdge (r+1)) (coldEdge (r+1))^2 ≤
        K * detectorError (powerResponse (doubleExponent (β n))) (hotEdge (r+1)) (coldEdge (r+1)) :=
      edgePair_mem_closed_of_physical r (isClosed_le ((continuous_detectorError (powerResponse (β n)) (r+1)).pow 2)
        (continuous_const.mul (continuous_detectorError (powerResponse (doubleExponent (β n))) (r+1)))) (h (β n))
    have ht := le_of_tendsto_of_tendsto ((edge_error_tendsto_rank (r+1) hb).pow 2)
      ((edge_error_tendsto_rank (r+1) hd).const_mul K) (Eventually.of_forall he)
    rw [pow_two] at ht
    exact le_of_mul_le_mul_right ht (Nat.cast_pos.mpr (Nat.succ_pos r))
  · intro h β P Q hP cP hQ cQ
    exact (amplitude_sq_le_rank_mul_born β _ _).trans (mul_le_mul_of_nonneg_right h (detectorError_nonneg _ _ _))

#print axioms amplitude_sq_le_rank_mul_born
#print axioms born_le_twice_amplitude
#print axioms rankOne_born_factor_iff
#print axioms uniform_born_factor_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
