import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MovingTrace.Budget
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MovingTrace.TunableWindows

/-! # Exact stability for an arbitrary time-dependent fourth-trace budget -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology
open scoped NNReal

/-- At every positive multiple of the critical budget scale some actual omission retains a fixed positive amplitude. -/
theorem critical_budget_witness {σ η : ℝ} (hs : 0 < σ) (hη : 0 < η) :
    ∃ A > (0:ℝ), ∀ t ≥ (1:ℝ), ∃ (P : Projection) (dim : MissingDimension P 1) (hc : Conserving (projected P)),
      A < ‖relativePartition (physicalSpectrum P dim hc) (⟨σ,t⟩:ℂ)‖ ∧ traceLoss (projected P) ≤ η/t^(clockBudgetExponent σ) := by
  let C := 1+2/η
  have h1 : 1 ≤ C := le_add_of_nonneg_right (div_pos (by norm_num) hη).le
  have hC := zero_lt_one.trans_le h1
  have hscale : 2 ≤ η*C := by
    dsimp only [C]
    rw [mul_add,mul_one,mul_comm η (2/η),div_mul_cancel₀ _ hη.ne']
    linarith only [hη]
  by_cases hw : σ ≤ 1
  · let A := highWindowFactor σ/C^σ
    have hpow := Real.rpow_pos_of_pos hC σ
    refine ⟨A,div_pos (highWindowFactor_pos σ) hpow,?_⟩
    intro t ht
    let T := t^σ⁻¹
    have ht' := zero_lt_one.trans_le ht
    have hT : 0 < T := Real.rpow_pos_of_pos ht' _
    have htT : t ≤ T := by
      have hinv : 1 ≤ σ⁻¹ := by rw [← one_div]; exact (one_le_div hs).mpr hw
      simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le ht hinv)
    have hr : t ≤ C*T := htT.trans (le_mul_of_one_le_left hT.le h1)
    obtain ⟨P,dim,hc,hL,hD⟩ := high_scale_witness hs ht hr
    have he : (C*T)^σ = C^σ*t := by rw [Real.mul_rpow hC.le hT.le,show T^σ=t from Real.rpow_inv_rpow ht'.le hs.ne']
    have hA : highWindowFactor σ*(t/(C*T)^σ) = A := by
      rw [he]
      dsimp only [A]
      field_simp [ht'.ne',hpow.ne']
    have he₂ : T^2 = t^(2/σ) := by
      rw [show T^2=t^(σ⁻¹*(2:ℕ)) from (Real.rpow_mul_natCast ht'.le _ _).symm]
      congr 1
      push_cast
      ring
    have hcost : 2/(C*T)^2 ≤ η/t^(2/σ) := by
      rw [mul_pow,he₂]
      apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hC) (Real.rpow_pos_of_pos ht' _)) (Real.rpow_pos_of_pos ht' _)).mpr
      have h₂ : 2 ≤ η*C^2 := hscale.trans (mul_le_mul_of_nonneg_left
        ((le_mul_of_one_le_right hC.le h1).trans_eq (sq C).symm) hη.le)
      exact (mul_le_mul_of_nonneg_right h₂ (Real.rpow_nonneg ht'.le _)).trans_eq (mul_assoc _ _ _)
    rw [clockBudgetExponent,if_pos hw]
    exact ⟨P,dim,hc,hA ▸ hL,hD.le.trans hcost⟩
  · refine ⟨(shortChordFactor σ/2)/C,div_pos (half_pos (shortChordFactor_pos σ)) hC,?_⟩
    intro t ht
    have ht' := zero_lt_one.trans_le ht
    obtain ⟨P,dim,hc,hL,hD⟩ := ground_scale_witness hs ht (le_mul_of_one_le_left ht'.le h1)
    have hA : (shortChordFactor σ/2)*(t/(C*t)) = (shortChordFactor σ/2)/C := by field_simp [ht'.ne',hC.ne']
    have hcost : 2/(C*t) ≤ η/t := (div_le_div_iff₀ (mul_pos hC ht') ht').mpr
      ((mul_le_mul_of_nonneg_right hscale ht'.le).trans_eq (mul_assoc _ _ _))
    rw [clockBudgetExponent,if_neg hw,Real.rpow_one]
    exact ⟨P,dim,hc,hA ▸ hL,hD.le.trans hcost⟩

/-- A single arbitrary nonnegative tolerance admits uniform stability exactly when its critical rescaling tends to zero. -/
theorem clockBudgetStable_iff (σ : ℝ) (B : ℝ → ℝ≥0) :
    clockBudgetStable σ B ↔ 0 < σ ∧ Tendsto (fun t : ℝ => t^(clockBudgetExponent σ)*(B t:ℝ)) atTop (𝓝 0) := by
  constructor
  · intro h
    refine ⟨h.1,Metric.tendsto_nhds.mpr ?_⟩
    intro η hη
    obtain ⟨A,hA,hw⟩ := critical_budget_witness h.1 hη
    filter_upwards [eventually_ge_atTop (1:ℝ),h.2 A hA] with t ht hsmall
    obtain ⟨P,dim,hc,hL,hD⟩ := hw t ht
    have htol : (B t:ℝ) < η/t^(clockBudgetExponent σ) := by
      by_contra! hbig
      exact hL.not_gt (hsmall P dim hc (hD.trans hbig))
    have hp := Real.rpow_pos_of_pos (zero_lt_one.trans_le ht) (clockBudgetExponent σ)
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (mul_nonneg hp.le (B t).coe_nonneg),mul_comm]
    exact (lt_div_iff₀ hp).mp htol
  · rintro ⟨hs,hB⟩
    by_cases hw : σ ≤ 1
    · simp only [clockBudgetExponent,if_pos hw] at hB
      exact matched_budget_stable hs hw B hB
    · simp only [clockBudgetExponent,if_neg hw,Real.rpow_one] at hB
      exact summable_budget_stable (lt_of_not_ge hw) B hB

#print axioms critical_budget_witness
#print axioms clockBudgetStable_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
