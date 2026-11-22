import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.Renormalization
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.OrderContrast

/-!
# Zeta zeros detected by an integer comparison of two finite heat sums

A further clock halving squares the radix. One coarse finite occupation
sum and C+1 fine sums have equal density, so their difference converges
without subtracting an explicit function of the energy cutoff.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open Filter
open scoped Topology

theorem tailRadix_succ (t : ExceptionalTime) (j : ℕ) :
    tailRadix t (j+1) = (tailRadix t j)^2 := by
  rw [radix_sq]
  change (block t)^(windingOrder (refined t (j+1))/2) = _
  rw [(refined_parameters t (j+1)).2.2,(refined_parameters t j).2.2,pow_succ' 2 j,Nat.mul_assoc,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-- Actual finite occupation sums at successive refinements, compared at the same cutoff. -/
def adjacentCutoff (t : ExceptionalTime) (j X : ℕ) (w : ℂ) :=
  shellCutoff t j X w - ((tailRadix t j).val+1:ℂ)*shellCutoff t (j+1) X w

theorem adjacent_cutoff_limit (t : ExceptionalTime) (j : ℕ) (z : {w : ℂ // 0 < w.re ∧ w ≠ 1}) :
    let C := tailRadix t j
    let q := heat z.val C
    Tendsto (fun X => adjacentCutoff t j X z.val) atTop
      (𝓝 (2*riemannZeta z.val*q*(1-(C.val:ℂ)*q)/(1-q^2))) := by
  let C := tailRadix t j
  let c : ℂ := C.val
  let q := heat z.val C
  have hcp : 1 < C.val := radix_gt_one t j
  have hc1 : c-1 ≠ 0 := sub_ne_zero.mpr (show (C.val:ℂ) ≠ 1 by exact_mod_cast hcp.ne')
  have hcr : 1 < C.val^2 := one_lt_pow₀ hcp (by norm_num)
  have hc2 : c^2-1 ≠ 0 := sub_ne_zero.mpr (show (C.val:ℂ)^2 ≠ 1 by exact_mod_cast hcr.ne')
  have hd : 2/(c-1) = (c+1)*(2/(c^2-1)) := by
    field_simp [hc1,hc2]
    ring
  have hq : ‖q‖ < 1 := heat_contraction C (radix_gt_one t j) z.val z.property.1
  have hq2 : ‖q^2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have hn : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr fun he => hq.ne (by rw [← he,norm_one])
  have hn2 : (1:ℂ)-q^2 ≠ 0 := sub_ne_zero.mpr fun he => hq2.ne (by rw [← he,norm_one])
  have hheat : heat z.val (tailRadix t (j+1)) = q^2 := by rw [tailRadix_succ,pow_two,heat_mul,pow_two]
  have h := (renormalized_cutoff_limit t j z).sub ((renormalized_cutoff_limit t (j+1) z).const_mul (c+1))
  change Tendsto _ atTop (𝓝 (2*q*riemannZeta z.val/(1-q)-
    (c+1)*(2*heat z.val (tailRadix t (j+1))*riemannZeta z.val/(1-heat z.val (tailRadix t (j+1)))))) at h
  rw [hheat] at h
  have hval : 2*q*riemannZeta z.val/(1-q)-(c+1)*(2*q^2*riemannZeta z.val/(1-q^2)) =
      2*riemannZeta z.val*q*(1-c*q)/(1-q^2) := by
    field_simp [hn,hn2]
    ring
  rw [hval] at h
  apply h.congr
  intro X
  simp only [renormalizedCutoff,tailRadix_succ,PNat.pow_coe,Nat.cast_pow,adjacentCutoff]
  change shellCutoff t j X z.val-2/(c-1)*_-(c+1)*(shellCutoff t (j+1) X z.val-2/(c^2-1)*_) = _
  rw [hd]
  ring

/-- Inside the critical strip the matched finite traces tend to zero exactly at zeta zeros. -/
theorem adjacent_cutoff_zero_iff (t : ExceptionalTime) (j : ℕ) (z : {w : ℂ // 0 < w.re ∧ w.re < 1}) :
    Tendsto (fun X => adjacentCutoff t j X z.val) atTop (𝓝 0) ↔ riemannZeta z.val = 0 := by
  let C := tailRadix t j
  let c : ℂ := C.val
  let q := heat z.val C
  have hw : z.val ≠ 1 := fun he => z.property.2.ne (by rw [he,Complex.one_re])
  have hlim := adjacent_cutoff_limit t j ⟨z.val,z.property.1,hw⟩
  change Tendsto _ atTop (𝓝 (2*riemannZeta z.val*q*(1-c*q)/(1-q^2))) at hlim
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr C.ne_zero
  have hq : q ≠ 0 := Complex.exp_ne_zero _
  have hqnorm : ‖q‖ < 1 := heat_contraction C (radix_gt_one t j) z.val z.property.1
  have hq2 : ‖q^2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hqnorm (by norm_num)
  have hn : (1:ℂ)-q^2 ≠ 0 := sub_ne_zero.mpr fun he => hq2.ne (by rw [← he,norm_one])
  have hlow : ‖heat 1 C‖ < ‖q‖ := by
    rw [norm_heat,show ‖q‖ = Real.exp (-z.val.re*energy C) from norm_heat _ _,Real.exp_lt_exp,Complex.one_re]
    exact mul_lt_mul_of_pos_right (neg_lt_neg z.property.2) (Real.log_pos (by exact_mod_cast radix_gt_one t j))
  have hmid : (1:ℂ)-c*q ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hval : q = c⁻¹ := by
      calc q = c⁻¹*(c*q) := by rw [← mul_assoc,inv_mul_cancel₀ hc,one_mul]
           _ = c⁻¹ := by rw [← he,mul_one]
    have hh : heat 1 C = c⁻¹ := by rw [heat_eq_cpow,Complex.cpow_neg_one]
    exact hlow.ne (by rw [hh,hval])
  constructor
  · intro hz
    have eq := tendsto_nhds_unique hlim hz
    rcases div_eq_zero_iff.mp eq with h | h
    · simpa only [mul_eq_zero,or_false,or_iff_left hmid,or_iff_left hq,or_iff_right (by norm_num : (2:ℂ) ≠ 0)] using h
    · exact (hn h).elim
  · intro hz
    simpa only [hz,mul_zero,zero_mul,zero_div] using hlim

theorem rh_iff_adjacent_cutoffs_isometric (t : ExceptionalTime) (j : ℕ) :
    RiemannHypothesis ↔ ∀ s : {s : ℂ // 0 < s.re ∧ s.re < 1/2},
      Tendsto (fun X => adjacentCutoff t j X (2*s.val)) atTop (𝓝 0) →
        ∃ U : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, U f x = split (2*s.val) f x := by
  rw [rh_iff_response_zeros_isometric t]
  apply forall_congr' fun s => ?_
  have hp : 0 < (2*s.val).re := by rw [two_mul,Complex.add_re]; linarith only [s.property.1]
  have hl : (2*s.val).re < 1 := by rw [two_mul,Complex.add_re]; linarith only [s.property.2]
  rw [response_zero_iff t ⟨s.val,s.property.1⟩,adjacent_cutoff_zero_iff t j ⟨2*s.val,hp,hl⟩]

/-- The prime-two clock detects each zero by comparing one coarse sum with three fine sums. -/
theorem prime_two_cutoff_zero_iff (z : {w : ℂ // 0 < w.re ∧ w.re < 1}) :
    Tendsto (fun X => shellCutoff halfTurnClock 0 X z.val-3*shellCutoff halfTurnClock 1 X z.val)
      atTop (𝓝 0) ↔ riemannZeta z.val = 0 := by
  have hr : tailRadix halfTurnClock 0 = 2 := by
    rw [tailRadix,show refined halfTurnClock 0 = halfTurnClock from rfl,
      prime_clock_parameters.1.1,prime_clock_parameters.1.2,show (2:ℕ)/2 = 1 by norm_num,pow_one]
  have hc : ((tailRadix halfTurnClock 0).val+1:ℂ) = 3 := by rw [hr]; norm_num
  simpa only [adjacentCutoff,hc] using adjacent_cutoff_zero_iff halfTurnClock 0 z

#print axioms prime_two_cutoff_zero_iff
#print axioms tailRadix_succ
#print axioms adjacent_cutoff_limit
#print axioms adjacent_cutoff_zero_iff
#print axioms rh_iff_adjacent_cutoffs_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
