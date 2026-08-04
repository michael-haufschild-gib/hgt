import GaloisForLFunctions.HTGeometry.HillPotentialFlow

/-!
# The size of the driven evolution on a window of times

The synthesis layer differentiates under the integral sign, so it needs the evolution and its
velocity bounded on windows of times *uniformly in the frequency*. Both bounds are available: the
first is the exponential bound of the Volterra series with the window constants of the kernel, and
the second is read off the Duhamel formula, where every product of a velocity of the fundamental
pair with the other member is a speed ratio — the frequency cancels.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

section Bounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-- The size of the evolution on the window `[-T, T]`. -/
noncomputable def hillFlowSize (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (T : ℝ) : ℝ :=
  a.coscSize T * ‖G₀‖ * Real.exp (a.propSize T * (Real.sqrt 2 ^ N * b.bound) * T)

theorem hillFlowSize_nonneg (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (T : ℝ) :
    0 ≤ hillFlowSize a b G₀ T := by
  have h1 : (0 : ℝ) ≤ a.coscSize T * ‖G₀‖ := mul_nonneg (a.coscSize_nonneg T) (norm_nonneg _)
  rw [hillFlowSize]
  positivity

/-- **The evolution is bounded on every window.** -/
theorem norm_hillPotentialFlow_le_window (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖hillPotentialFlow a b G₀ t‖ ≤ hillFlowSize a b G₀ T := by
  have hM : (0 : ℝ) ≤ a.propSize T * (Real.sqrt 2 ^ N * b.bound) :=
    mul_nonneg (a.propSize_nonneg T)
      (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) b.bound_nonneg)
  have hF : (0 : ℝ) ≤ a.coscSize T * ‖G₀‖ := mul_nonneg (a.coscSize_nonneg T) (norm_nonneg _)
  have hmain := norm_volterraSolution_le_window (f := hillFreeTerm a G₀)
    (K := hillDuhamelKernel a b) (continuous_hillFreeTerm a G₀)
    (continuous_hillDuhamelKernel a b) hT hM hF
    (fun r s hr hs => norm_hillDuhamelKernel_le_window a b hr hs)
    (fun r hr => norm_hillFreeTerm_le_window a G₀ hr) ht
  refine hmain.trans ?_
  rw [hillFlowSize]
  refine mul_le_mul_of_nonneg_left ?_ hF
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hM)

/-- **The source is bounded on every window**, uniformly in the frequency. -/
theorem norm_hillFlowSource_le_window (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    {T s : ℝ} (hT : 0 ≤ T) (hs : |s| ≤ T) (ξ : E) :
    ‖hillFlowSource a b G₀ ξ s‖ ≤ (Real.sqrt 2 ^ N * b.bound) * hillFlowSize a b G₀ T := by
  have hval : hillFlowSource a b G₀ ξ s
      = kgConvCLM (b.density s) (hillPotentialFlow a b G₀ s) ξ := rfl
  rw [hval]
  refine (BoundedContinuousFunction.norm_coe_le_norm
    (kgConvCLM (b.density s) (hillPotentialFlow a b G₀ s)) ξ).trans ?_
  refine ((kgConvCLM (b.density s)).le_opNorm (hillPotentialFlow a b G₀ s)).trans ?_
  exact mul_le_mul (b.norm_convCLM_le s) (norm_hillPotentialFlow_le_window a b G₀ hT hs)
    (norm_nonneg _) (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) b.bound_nonneg)

/-- The size of the source on the window. -/
noncomputable def hillSourceSize (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (T : ℝ) :
    ℝ := (Real.sqrt 2 ^ N * b.bound) * hillFlowSize a b G₀ T

theorem hillSourceSize_nonneg (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (T : ℝ) :
    0 ≤ hillSourceSize a b G₀ T :=
  mul_nonneg (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) b.bound_nonneg)
    (hillFlowSize_nonneg a b G₀ T)

/-- The size of the velocity of the evolution on the window `[-T, T]`. -/
noncomputable def hillVelocitySize (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (T : ℝ) : ℝ :=
  Real.exp (a.logBound * T) * ‖G₀‖ +
    2 * (a.ratio * (Real.exp (a.logBound * T) * Real.exp (a.logBound * T)) *
      hillSourceSize a b G₀ T * T)

/-- The two integral terms of the Duhamel velocity, bounded on the window. -/
theorem norm_duhamel_velocity_part_le (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (ξ : E) {u v : ℝ → ℝ}
    (hprod : ∀ s : ℝ, |s| ≤ T → |u t| * |v s| ≤
      a.ratio * (Real.exp (a.logBound * T) * Real.exp (a.logBound * T)))
    (hsplit : ∀ s : ℝ, ((u t * v s : ℝ) : ℂ) * hillFlowSource a b G₀ ξ s
      = ((u t : ℝ) : ℂ) * (((v s : ℝ) : ℂ) * hillFlowSource a b G₀ ξ s)) :
    ‖((u t : ℝ) : ℂ) * ∫ s in (0 : ℝ)..t, ((v s : ℝ) : ℂ) * hillFlowSource a b G₀ ξ s‖
      ≤ a.ratio * (Real.exp (a.logBound * T) * Real.exp (a.logBound * T)) *
        hillSourceSize a b G₀ T * T := by
  have hLip : 0 ≤ a.ratio * (Real.exp (a.logBound * T) * Real.exp (a.logBound * T)) :=
    mul_nonneg a.ratio_nonneg
      (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _)))
  have hC : 0 ≤ a.ratio * (Real.exp (a.logBound * T) * Real.exp (a.logBound * T)) *
      hillSourceSize a b G₀ T := mul_nonneg hLip (hillSourceSize_nonneg a b G₀ T)
  have hpull : ((u t : ℝ) : ℂ) * ∫ s in (0 : ℝ)..t,
        ((v s : ℝ) : ℂ) * hillFlowSource a b G₀ ξ s
      = ∫ s in (0 : ℝ)..t, ((u t * v s : ℝ) : ℂ) * hillFlowSource a b G₀ ξ s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    exact (hsplit s).symm
  rw [hpull]
  have hbd : ∀ s ∈ Set.uIoc (0 : ℝ) t,
      ‖((u t * v s : ℝ) : ℂ) * hillFlowSource a b G₀ ξ s‖
        ≤ a.ratio * (Real.exp (a.logBound * T) * Real.exp (a.logBound * T)) *
          hillSourceSize a b G₀ T := by
    intro s hsmem
    have hsT : |s| ≤ T :=
      le_trans (abs_le_abs_of_mem_uIcc_zero (Set.uIoc_subset_uIcc hsmem)) ht
    have hnorm : ‖((u t * v s : ℝ) : ℂ) * hillFlowSource a b G₀ ξ s‖
        = (|u t| * |v s|) * ‖hillFlowSource a b G₀ ξ s‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    rw [hnorm]
    exact mul_le_mul (hprod s hsT) (norm_hillFlowSource_le_window a b G₀ hT hsT ξ)
      (norm_nonneg _) hLip
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t) hbd
  refine hint.trans ?_
  rw [sub_zero]
  exact mul_le_mul_of_nonneg_left ht hC

/-- **The velocity of the evolution is bounded on every window**, uniformly in the frequency. -/
theorem norm_hillFlowApplyDeriv_le_window (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (ξ : E) :
    ‖hillFlowApplyDeriv a b G₀ ξ t‖ ≤ hillVelocitySize a b G₀ T := by
  have hfreqpos := a.freq_pos ξ 0
  have hfree : ‖((hillCosDeriv (a.freq ξ) t : ℝ) : ℂ) * (((a.freq ξ 0 : ℝ) : ℂ)⁻¹ * G₀ ξ)‖
      ≤ Real.exp (a.logBound * T) * ‖G₀‖ := by
    have hcos := abs_hillCosDeriv_massive_le (S := ‖ξ‖) a.mass_pos a.continuous_speed
      a.hasDerivAt_speed a.speed_pos a.abs_speedDeriv_le a.speed_sq_le le_rfl t
    have hG : ‖G₀ ξ‖ ≤ ‖G₀‖ := G₀.norm_coe_le_norm ξ
    have hnorm : ‖((hillCosDeriv (a.freq ξ) t : ℝ) : ℂ) * (((a.freq ξ 0 : ℝ) : ℂ)⁻¹ * G₀ ξ)‖
        = |hillCosDeriv (a.freq ξ) t| * ((a.freq ξ 0)⁻¹ * ‖G₀ ξ‖) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hfreqpos]
    rw [hnorm]
    have hstep : |hillCosDeriv (a.freq ξ) t| * ((a.freq ξ 0)⁻¹ * ‖G₀ ξ‖)
        ≤ (a.freq ξ 0 * Real.exp (a.logBound * |t|)) * ((a.freq ξ 0)⁻¹ * ‖G₀ ξ‖) := by
      refine mul_le_mul_of_nonneg_right hcos ?_
      exact mul_nonneg (le_of_lt (inv_pos.mpr hfreqpos)) (norm_nonneg _)
    refine hstep.trans ?_
    have hcancel : (a.freq ξ 0 * Real.exp (a.logBound * |t|)) * ((a.freq ξ 0)⁻¹ * ‖G₀ ξ‖)
        = Real.exp (a.logBound * |t|) * ‖G₀ ξ‖ := by
      field_simp
    rw [hcancel]
    exact mul_le_mul (a.exp_le_window ht) hG (norm_nonneg _) (le_of_lt (Real.exp_pos _))
  have hpart1 : ‖((hillCosDeriv (a.freq ξ) t : ℝ) : ℂ) *
      duhamelPairSecondPart (hillSin (a.freq ξ)) (hillFlowSource a b G₀ ξ) t‖
      ≤ a.ratio * (Real.exp (a.logBound * T) * Real.exp (a.logBound * T)) *
        hillSourceSize a b G₀ T * T := by
    refine norm_duhamel_velocity_part_le a b G₀ hT ht ξ (v := hillSin (a.freq ξ))
      (fun s hsT => ?_) (fun s => by push_cast; ring)
    have hcross := abs_hillCosDeriv_mul_abs_hillSin_le (C := a.sizeBound) a.mass_pos
      a.continuous_speed a.hasDerivAt_speed a.speed_pos a.abs_speedDeriv_le a.speed_sq_le
      a.lower_pos a.lower_le t s ξ
    refine hcross.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ a.ratio_nonneg
    exact mul_le_mul (a.exp_le_window ht) (a.exp_le_window hsT) (le_of_lt (Real.exp_pos _))
      (le_of_lt (Real.exp_pos _))
  have hpart2 : ‖((hillSinDeriv (a.freq ξ) t : ℝ) : ℂ) *
      duhamelPairFirstPart (hillCos (a.freq ξ)) (hillFlowSource a b G₀ ξ) t‖
      ≤ a.ratio * (Real.exp (a.logBound * T) * Real.exp (a.logBound * T)) *
        hillSourceSize a b G₀ T * T := by
    refine norm_duhamel_velocity_part_le a b G₀ hT ht ξ (v := hillCos (a.freq ξ))
      (fun s hsT => ?_) (fun s => by push_cast; ring)
    have hsd := abs_hillSinDeriv_massive_le (S := ‖ξ‖) a.mass_pos a.continuous_speed
      a.hasDerivAt_speed a.speed_pos a.abs_speedDeriv_le a.speed_sq_le le_rfl t
    have hcs := abs_hillCos_le_ratio (C := a.sizeBound) a.mass_pos a.continuous_speed
      a.hasDerivAt_speed a.speed_pos a.abs_speedDeriv_le a.speed_sq_le a.lower_pos a.lower_le s ξ
    have hstep : |hillSinDeriv (a.freq ξ) t| * |hillCos (a.freq ξ) s|
        ≤ Real.exp (a.logBound * |t|) * (a.ratio * Real.exp (a.logBound * |s|)) :=
      mul_le_mul hsd hcs (abs_nonneg _) (le_of_lt (Real.exp_pos _))
    refine hstep.trans ?_
    have hexpt := a.exp_le_window ht
    have hexps := a.exp_le_window hsT
    have hmain : Real.exp (a.logBound * |t|) * (a.ratio * Real.exp (a.logBound * |s|))
        ≤ Real.exp (a.logBound * T) * (a.ratio * Real.exp (a.logBound * T)) := by
      refine mul_le_mul hexpt ?_ ?_ (le_of_lt (Real.exp_pos _))
      · exact mul_le_mul_of_nonneg_left hexps a.ratio_nonneg
      · exact mul_nonneg a.ratio_nonneg (le_of_lt (Real.exp_pos _))
    refine hmain.trans_eq ?_
    ring
  have hexpand : hillFlowApplyDeriv a b G₀ ξ t
      = ((hillCosDeriv (a.freq ξ) t : ℝ) : ℂ) * (((a.freq ξ 0 : ℝ) : ℂ)⁻¹ * G₀ ξ) -
        ((hillCosDeriv (a.freq ξ) t : ℝ) : ℂ) *
          duhamelPairSecondPart (hillSin (a.freq ξ)) (hillFlowSource a b G₀ ξ) t +
        ((hillSinDeriv (a.freq ξ) t : ℝ) : ℂ) *
          duhamelPairFirstPart (hillCos (a.freq ξ)) (hillFlowSource a b G₀ ξ) t := by
    rw [hillFlowApplyDeriv, duhamelPairDeriv]
    ring
  rw [hexpand, hillVelocitySize]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_sub_le _ _).trans (add_le_add hfree hpart1)) hpart2 |>.trans_eq ?_
  ring

end Bounds

end GaloisForLFunctions.HTGeometry
