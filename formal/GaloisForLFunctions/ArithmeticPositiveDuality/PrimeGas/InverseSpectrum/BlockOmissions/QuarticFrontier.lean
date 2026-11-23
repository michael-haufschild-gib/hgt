import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.TraceObstruction
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.DyadicTrace
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting

/-! # Critical line as the exact threshold of fourth-trace control -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

private theorem real_fourth (x : ℝ) : x^(4:ℝ) = x^4 := Real.rpow_natCast x 4

/-- Exactly the closed critical half-plane admits uniform quartic control by the fourth trace. -/
theorem quartic_trace_control_iff (r : ℕ) {z : ℂ} (hz : 0 < z.re) :
    (∃ K : ℝ, traceControlsAt (r+1) z 4 K) ↔ 1/2 ≤ z.re := by
  constructor
  · rintro ⟨K,hK⟩
    have h := trace_control_forces_exponent r hz ⟨4,show (0:ℝ)<4 by norm_num⟩ hK
    change 2 ≤ z.re*4 at h
    linarith only [h]
  · intro h
    refine ⟨(‖z‖/(1/2:ℝ))^4*((r+1:ℕ):ℝ)^3,fun P hd hc => ?_⟩
    rw [real_fourth]
    exact critical_trace_bound P hd hc h

/-- The limiting exponent four is necessary at every imaginary height of the critical line. -/
theorem critical_power_lower_bound (r : ℕ) {z : ℂ} (hz : z.re = 1/2) (p : GibbsExponent)
    {K : ℝ} (h : traceControlsAt (r+1) z p.val K) : 4 ≤ p.val := by
  have hp := trace_control_forces_exponent r (show 0 < z.re by rw [hz]; norm_num) p h
  rw [hz] at hp
  linarith only [hp]

/-- At real critical temperature the optimal coefficient at every positive rank is r³. -/
theorem real_critical_quartic_factor_iff (r : ℕ) (K : ℝ) :
    traceControlsAt (r+1) (1/2) 4 K ↔ ((r+1:ℕ):ℝ)^3 ≤ K := by
  have he : (1/2:ℂ).re = 1/2 := by norm_num
  constructor
  · intro h
    have hb := trace_control_forces_factor (r+1) (show 0 < (1/2:ℂ).re by rw [he]; norm_num)
      ⟨4,show (0:ℝ)<4 by norm_num⟩ (by change (1/2:ℂ).re*4=2; rw [he]; norm_num) h
    change ((r+1:ℕ):ℝ)^(4:ℝ) ≤ K*((r+1:ℕ):ℝ) at hb
    rw [real_fourth,pow_succ _ 3] at hb
    exact le_of_mul_le_mul_right hb (Nat.cast_pos.mpr (Nat.succ_pos r))
  · intro h P hd hc
    have hb := critical_trace_bound P hd hc (z := 1/2) he.ge
    have hn : ‖(1/2:ℂ)‖ = 1/2 := by norm_num [norm_div]
    rw [hn,div_self (by norm_num),one_pow,one_mul] at hb
    rw [real_fourth]
    have hD : 0 ≤ traceLoss (projected P) := (quadratic_physicalReading P hd hc) ▸ (relativeReading_bounds _ _).1
    exact hb.trans (mul_le_mul_of_nonneg_right h hD)

/-- Exact coefficient for control of the surviving Laurent constant by the measured fourth trace. -/
theorem pole_constant_factor_iff (r : ℕ) (K : ℝ) :
    (∀ (P : Projection) (hd : MissingDimension P (r+1)) (hc : Conserving (projected P)) (c : ℝ),
      Tendsto (fun z : ℂ => survivingPartition (physicalSpectrum P hd hc) z - 1/(z-1)) (𝓝[≠] 1) (𝓝 (c:ℂ)) →
      (Real.eulerMascheroniConstant-c)^2 ≤ K*traceLoss (projected P)) ↔ ((r+1:ℕ):ℝ) ≤ K := by
  constructor
  · intro h
    have h₁ : traceControlsAt (r+1) 1 2 K := by
      intro P hd hc
      let b := physicalSpectrum P hd hc
      have hb := h P hd hc _ (surviving_finite_part b)
      rw [sub_sub_cancel] at hb
      have he : relativePartition b 1 = (relativeReading (powerResponse unitExponent) b : ℂ) :=
        relativePartition_real b unitExponent
      change ‖relativePartition b 1‖^(2:ℝ) ≤ _
      rw [he,Complex.norm_real,Real.norm_of_nonneg (relativeReading_bounds _ b).1,Real.rpow_two]
      exact hb
    have hmatch := trace_control_forces_factor (r+1) (z := 1) (by norm_num)
      ⟨2,show (0:ℝ)<2 by norm_num⟩ (by change (1:ℂ).re*2=2; norm_num) h₁
    change ((r+1:ℕ):ℝ)^(2:ℝ) ≤ K*((r+1:ℕ):ℝ) at hmatch
    rw [Real.rpow_two,pow_two] at hmatch
    exact le_of_mul_le_mul_right hmatch (Nat.cast_pos.mpr (Nat.succ_pos r))
  · intro h P hd hc c ht
    obtain ⟨a,ha,he⟩ := trace_controls_pole_constant P hd hc
    have hac := Complex.ofReal_inj.mp (tendsto_nhds_unique ha ht)
    rw [← hac]
    have hD : 0 ≤ traceLoss (projected P) := by rw [← quadratic_physicalReading P hd hc]; exact (relativeReading_bounds _ _).1
    exact he.trans (mul_le_mul_of_nonneg_right h hD)

/-- Real parameters admitting a quartic bound at a fixed clock height. -/
def quarticAbscissas (r : ℕ) (t : ℝ) : Set ℝ :=
  {x | 0 < x ∧ ∃ K : ℝ, traceControlsAt r (⟨x,t⟩ : ℂ) 4 K}

theorem quarticAbscissas_eq (r : ℕ) (t : ℝ) : quarticAbscissas (r+1) t = Ici (1/2) := by
  ext x
  constructor
  · rintro ⟨hx,h⟩
    exact (quartic_trace_control_iff r (z := ⟨x,t⟩) hx).mp h
  · intro hx
    have hp : 0 < x := (by norm_num : (0:ℝ) < 1/2).trans_le hx
    exact ⟨hp,(quartic_trace_control_iff r (z := ⟨x,t⟩) hp).mpr hx⟩

/-- The least abscissa at which an ordinary trace controls the quartic loss is exactly the isometric composition law. -/
theorem quartic_onset_iff_split_isometric (r : ℕ) (z : ℂ) :
    IsLeast (quarticAbscissas (r+1) z.im) z.re ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split z f x := by
  rw [quarticAbscissas_eq,split_isometric_iff]
  constructor
  · intro h
    exact le_antisymm (h.2 (mem_Ici.mpr (le_refl (1/2:ℝ)))) h.1
  · intro h
    rw [h]
    exact isLeast_Ici

#print axioms quartic_trace_control_iff
#print axioms critical_power_lower_bound
#print axioms real_critical_quartic_factor_iff
#print axioms pole_constant_factor_iff
#print axioms quartic_onset_iff_split_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
