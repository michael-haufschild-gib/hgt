import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MovingTrace.TunableWindows
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MovingTrace.Budget

/-! # Sharp maximum response in a small fourth-trace window -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- Attained amplitudes when the deficit ceiling is two inverse squares of the occupation scale. -/
def smallWindowAmplitudes (σ t R : ℝ) : Set ℝ :=
  {x | ∃ (P : Projection) (dim : MissingDimension P 1) (hc : Conserving (projected P)),
    traceLoss (projected P) ≤ 2/R^2 ∧ ‖relativePartition (physicalSpectrum P dim hc) (⟨σ,t⟩:ℂ)‖ = x}

private theorem thermal_power_product {σ : ℝ} (hs : 0 < σ) : min σ 2*max 1 (2/σ) = 2 := by
  rcases le_total σ 2 with h | h
  · rw [min_eq_left h,max_eq_right ((one_le_div hs).mpr h),mul_comm,div_mul_cancel₀ _ hs.ne']
  · rw [min_eq_right h,max_eq_left ((div_le_one hs).mpr h),mul_one]

private theorem envelope_upper {σ : ℝ} (hs : 0 < σ) :
    ∃ C > (0:ℝ), ∀ t ≥ (1:ℝ), ∀ R ≥ t, ∀ x ∈ smallWindowAmplitudes σ t R, x ≤ C*(t/R^(min σ 2)) := by
  let q := max 1 (2/σ)
  let β := min σ 2
  have hq : 0 < q := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨_,_,B,hB,hbound⟩ := clock_coefficient_power_bounds hs
  have h2B : 0 < 2*B := mul_pos (by norm_num) hB
  refine ⟨(2*B)^q⁻¹,Real.rpow_pos_of_pos h2B _,?_⟩
  rintro t ht R hR x ⟨P,dim,hc,hD,rfl⟩
  let z : ℂ := ⟨σ,t⟩
  let X := ‖relativePartition (physicalSpectrum P dim hc) z‖
  have ht' := zero_lt_one.trans_le ht
  have hRp := ht'.trans_le hR
  have hX : 0 ≤ X := norm_nonneg _
  have hx := (optimalTraceCoefficient_isLeast 0 (z := z) hs).1 P dim hc
  have hu := mul_le_mul (hbound t ht).2 hD (traceLoss_nonneg P dim hc) (mul_pos hB (Real.rpow_pos_of_pos ht' q)).le
  have he : (B*t^q)*(2/R^2) = (2*B)*(t/R^β)^q := by
    rw [Real.div_rpow ht'.le (Real.rpow_nonneg hRp.le _),← Real.rpow_mul hRp.le,thermal_power_product hs,Real.rpow_two]
    ring
  have hpow : X^q ≤ (2*B)*(t/R^β)^q := (hx.trans hu).trans_eq he
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg hX _) hpow (inv_nonneg.mpr hq.le)
  rw [Real.rpow_rpow_inv hX hq.ne',Real.mul_rpow h2B.le (Real.rpow_nonneg (div_nonneg ht'.le (Real.rpow_nonneg hRp.le _)) _),
    Real.rpow_rpow_inv (div_nonneg ht'.le (Real.rpow_nonneg hRp.le _)) hq.ne'] at hr
  exact hr

private theorem envelope_probe {σ : ℝ} (hs : 0 < σ) :
    ∃ c > (0:ℝ), ∀ t ≥ (1:ℝ), ∀ R ≥ t, ∃ x ∈ smallWindowAmplitudes σ t R, c*(t/R^(min σ 2)) < x := by
  rcases le_total σ 2 with h | h
  · refine ⟨highWindowFactor σ,highWindowFactor_pos σ,?_⟩
    intro t ht R hR
    obtain ⟨P,dim,hc,hL,hD⟩ := high_scale_witness hs ht hR
    rw [min_eq_left h]
    exact ⟨_,⟨P,dim,hc,hD.le,rfl⟩,hL⟩
  · refine ⟨shortChordFactor σ/2,half_pos (shortChordFactor_pos σ),?_⟩
    intro t ht R hR
    have h1 := ht.trans hR
    have hsq : t ≤ R^2 := hR.trans ((le_mul_of_one_le_right (zero_le_one.trans h1) h1).trans_eq (sq R).symm)
    obtain ⟨P,dim,hc,hL,hD⟩ := ground_scale_witness hs ht hsq
    rw [min_eq_right h,Real.rpow_two]
    exact ⟨_,⟨P,dim,hc,hD.le,rfl⟩,hL⟩

/-- The physical supremum is comparable to t/R^min(σ,2), uniformly over all scales R ≥ t ≥ 1. -/
theorem small_window_amplitude_envelope {σ : ℝ} (hs : 0 < σ) :
    ∃ c > (0:ℝ), ∃ C > (0:ℝ), ∀ t ≥ (1:ℝ), ∀ R ≥ t,
      c*(t/R^(min σ 2)) < sSup (smallWindowAmplitudes σ t R) ∧
      sSup (smallWindowAmplitudes σ t R) ≤ C*(t/R^(min σ 2)) := by
  obtain ⟨c,hc,hl⟩ := envelope_probe hs
  obtain ⟨C,hC,hu⟩ := envelope_upper hs
  refine ⟨c,hc,C,hC,?_⟩
  intro t ht R hR
  obtain ⟨x,hx,hL⟩ := hl t ht R hR
  have hb : BddAbove (smallWindowAmplitudes σ t R) := ⟨_,hu t ht R hR⟩
  exact ⟨hL.trans_le (le_csSup hb hx),csSup_le ⟨x,hx⟩ (hu t ht R hR)⟩

#print axioms small_window_amplitude_envelope

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
