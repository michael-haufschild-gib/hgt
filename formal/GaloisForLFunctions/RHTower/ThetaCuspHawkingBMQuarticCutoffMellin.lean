import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCutoffBulkMellinValue
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspCutoffProfile
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalSelfAngularGaps

/-! The original cutoff Mellin continuation at every same-occurrence quartic
exponent, obtained from finite transition integrals without a convergence-chamber
premise. Both cutoff mass and differentiated cusp flux retain their scale terms. -/
open Complex Set MeasureTheory Filter Topology
namespace RHTower.D4BMQuarticCutoffMellin
open D4BMJointSource D4BMJointWave D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private abbrev C (y : ℝ) : ℂ := cutoff ![0,y]

private theorem c_low (y : ℝ) (hy : y ≤ 2) : C y=0 := by
  unfold C cutoff
  rw [Real.smoothTransition.zero_of_nonpos (by change y-2≤0; linarith)]
  simp

private theorem c_high (y : ℝ) (hy : 3 ≤ y) : C y=1 := by
  unfold C cutoff
  rw [Real.smoothTransition.one_of_one_le (by change 1≤y-2; linarith)]
  simp

private theorem gamma_eq (N y : ℝ) : (scaledCuspCutoff N y:ℂ)=1-C (y/N) := by
  simp only [scaledCuspCutoff,baseCuspCutoff,Complex.ofReal_sub,Complex.ofReal_one]
  rfl

private theorem power_continuous (w : ℂ) (a b : ℝ) (ha : 0<a) :
    ContinuousOn (fun y : ℝ => (y:ℂ)^w) (Icc a b) := by
  intro y hy
  exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ha.trans_le hy.1).ne')).continuousWithinAt

private theorem weighted_interval (w : ℂ) (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (fun y : ℝ => C y*(y:ℂ)^(w-1)) volume a b :=
  ((nativeCutoff_height_continuous.continuousOn).mul (power_continuous (w-1) a b ha)).intervalIntegrable_of_Icc hab

private theorem scaled_weighted_interval (N : ℝ) (w : ℂ) (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (fun y : ℝ => C (y/N)*(y:ℂ)^(w-1)) volume a b :=
  ((nativeCutoff_height_continuous.comp (continuous_id.div_const N)).continuousOn.mul
    (power_continuous (w-1) a b ha)).intervalIntegrable_of_Icc hab

private theorem cutoff_tail (w : ℂ) (hw : w≠0) (Y : ℝ) (hY : 3≤Y) :
    (∫ y in (2:ℝ)..Y, C y*(y:ℂ)^(w-1)) = (Y:ℂ)^w/w-nativeCutoffMellinContinuation w := by
  have hi23 := weighted_interval w 2 3 (by norm_num) (by norm_num)
  have hi3Y := weighted_interval w 3 Y (by norm_num) hY
  have ht : (∫ y in (2:ℝ)..3, C y*(y:ℂ)^(w-1))=nativeCutoffTransitionMoment w :=
    intervalIntegral.integral_of_le (by norm_num)
  have hh : (∫ y in (3:ℝ)..Y, C y*(y:ℂ)^(w-1))=((Y:ℂ)^w-(3:ℂ)^w)/w := by
    calc
      _ = ∫ y in (3:ℝ)..Y, (y:ℂ)^(w-1) := by
        apply intervalIntegral.integral_congr
        intro y hy
        have hy3 : 3≤y := (show y∈Icc (3:ℝ) Y by simpa only [uIcc_of_le hY] using hy).1
        change C y*(y:ℂ)^(w-1)=(y:ℂ)^(w-1)
        rw [c_high y hy3,one_mul]
      _ = _ := by
        rw [integral_cpow (Or.inr ⟨by intro h; apply hw; linear_combination h,
          by rw [uIcc_of_le hY]; norm_num⟩)]
        simp only [sub_add_cancel,Complex.ofReal_ofNat]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi23 hi3Y,ht,hh]
  unfold nativeCutoffMellinContinuation
  ring

private theorem scaled_transition (N : ℝ) (hN : 0<N) (w : ℂ) :
    (∫ y in (2*N)..(3*N), C (y/N)*(y:ℂ)^(w-1))=
      (N:ℂ)^w*nativeCutoffTransitionMoment w := by
  let f := fun y : ℝ => C (y/N)*(y:ℂ)^(w-1)
  have he : (∫ x in (2:ℝ)..3, f (N*x))=
      (N:ℂ)^(w-1)*nativeCutoffTransitionMoment w := by
    calc
      _ = ∫ x in (2:ℝ)..3, (N:ℂ)^(w-1)*(C x*(x:ℂ)^(w-1)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx0 : 0≤x := le_trans (by norm_num : (0:ℝ)≤2)
          (show x∈Icc (2:ℝ) 3 by
            simpa only [uIcc_of_le (by norm_num : (2:ℝ)≤3)] using hx).1
        dsimp [f]
        rw [mul_div_cancel_left₀ _ hN.ne',Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg hN.le hx0]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le (by norm_num : (2:ℝ)≤3)]
        rfl
  have hs := intervalIntegral.smul_integral_comp_mul_left (f := f) (a := (2:ℝ)) (b := 3) N
  rw [he] at hs
  have hp : (N:ℂ)*(N:ℂ)^(w-1)=(N:ℂ)^w := by
    calc
      _ = (N:ℂ)^((1:ℂ)+(w-1)) := by
        rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hN.ne'),Complex.cpow_one]
      _ = _ := by congr 1; ring
  change (N:ℂ)*((N:ℂ)^(w-1)*nativeCutoffTransitionMoment w)=_ at hs
  rw [← mul_assoc,hp] at hs
  simpa only [mul_comm N] using hs.symm

private theorem scaled_tail (N : ℝ) (hN : 2≤N) (w : ℂ) :
    (∫ y in (2:ℝ)..(3*N), C (y/N)*(y:ℂ)^(w-1))=
      (N:ℂ)^w*nativeCutoffTransitionMoment w := by
  have hNp : 0<N := lt_of_lt_of_le (by norm_num) hN
  have hi0 := scaled_weighted_interval N w 2 (2*N) (by norm_num) (by linarith)
  have hi1 := scaled_weighted_interval N w (2*N) (3*N) (by positivity) (by linarith)
  have hz : (∫ y in (2:ℝ)..(2*N), C (y/N)*(y:ℂ)^(w-1))=0 := by
    calc
      _ = ∫ _y in (2:ℝ)..(2*N), (0:ℂ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        have hy2 : y≤2*N := (show y∈Icc (2:ℝ) (2*N) by
          simpa only [uIcc_of_le (by linarith : (2:ℝ)≤2*N)] using hy).2
        change C (y/N)*(y:ℂ)^(w-1)=0
        rw [c_low _ ((div_le_iff₀ hNp).mpr hy2),zero_mul]
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1,hz,zero_add,
    scaled_transition N hNp w]

private theorem cutoff_bulk_scale (N : ℝ) (hN : 2≤N) (w : ℂ) (hw : w≠0) :
    (∫ y in (2:ℝ)..(3*N), (scaledCuspCutoff N y:ℂ)*C y*(y:ℂ)^(w-1))=
      ((N:ℂ)^w-1)*nativeCutoffMellinContinuation w := by
  have hNp : 0<N := lt_of_lt_of_le (by norm_num) hN
  have he (y : ℝ) : (scaledCuspCutoff N y:ℂ)*C y=C y-C (y/N) := by
    rw [gamma_eq]
    by_cases hy : y≤2*N
    · rw [c_low _ ((div_le_iff₀ hNp).mpr hy)]
      ring
    · rw [c_high y (by linarith)]
      ring
  have hfun : (fun y : ℝ => (scaledCuspCutoff N y:ℂ)*C y*(y:ℂ)^(w-1))=
      fun y => C y*(y:ℂ)^(w-1)-C (y/N)*(y:ℂ)^(w-1) := by
    funext y
    rw [he,sub_mul]
  rw [hfun,intervalIntegral.integral_sub
    (weighted_interval w 2 (3*N) (by norm_num) (by linarith))
    (scaled_weighted_interval N w 2 (3*N) (by norm_num) (by linarith)),
    cutoff_tail w hw (3*N) (by linarith),scaled_tail N hN w,
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤3) hNp.le]
  unfold nativeCutoffMellinContinuation
  norm_num only [Complex.ofReal_ofNat]
  ring

private theorem base_bulk (w : ℂ) (hw : w≠0) :
    (∫ y in (1:ℝ)..4, (baseCuspCutoff y:ℂ)*(y:ℂ)^(w-1))=
      nativeCutoffMellinContinuation w-1/w := by
  have hz : (∫ y in (1:ℝ)..2, C y*(y:ℂ)^(w-1))=0 := by
    calc
      _ = ∫ _y in (1:ℝ)..2, (0:ℂ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        change C y*(y:ℂ)^(w-1)=0
        rw [c_low y (show y∈Icc (1:ℝ) 2 by
          simpa only [uIcc_of_le (by norm_num : (1:ℝ)≤2)] using hy).2,zero_mul]
      _ = 0 := by simp
  have hc : (∫ y in (1:ℝ)..4, C y*(y:ℂ)^(w-1))=(4:ℂ)^w/w-nativeCutoffMellinContinuation w := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (weighted_interval w 1 2 (by norm_num) (by norm_num))
      (weighted_interval w 2 4 (by norm_num) (by norm_num)),hz,zero_add,
      cutoff_tail w hw 4 (by norm_num)]
    norm_num only [Complex.ofReal_ofNat]
  have hp : (∫ y in (1:ℝ)..4, (y:ℂ)^(w-1))=((4:ℂ)^w-1)/w := by
    rw [integral_cpow (Or.inr ⟨by intro h; apply hw; linear_combination h,by norm_num⟩)]
    simp only [sub_add_cancel,Complex.ofReal_one,Complex.ofReal_ofNat,Complex.one_cpow]
  have he : (fun y : ℝ => (baseCuspCutoff y:ℂ)*(y:ℂ)^(w-1))=
      fun y : ℝ => (y:ℂ)^(w-1)-C y*(y:ℂ)^(w-1) := by
    funext y
    simp only [baseCuspCutoff,Complex.ofReal_sub,Complex.ofReal_one,C,cutoff]
    change (1-(Real.smoothTransition (y-2):ℂ))*(y:ℂ)^(w-1)=
      (y:ℂ)^(w-1)-(Real.smoothTransition (y-2):ℂ)*(y:ℂ)^(w-1)
    ring
  rw [he,intervalIntegral.integral_sub
    ((power_continuous (w-1) 1 4 (by norm_num)).intervalIntegrable_of_Icc (by norm_num))
    (weighted_interval w 1 4 (by norm_num) (by norm_num)),hp,hc]
  ring

private theorem base_flux (w : ℂ) (hw : w≠0) :
    -(∫ y in (1:ℝ)..4, ((deriv baseCuspCutoff y:ℝ):ℂ)*(y:ℂ)^w)=
      w*nativeCutoffMellinContinuation w := by
  have hu (y : ℝ) : HasDerivAt (fun y => (baseCuspCutoff y:ℂ))
      ((deriv baseCuspCutoff y:ℝ):ℂ) y :=
    ((baseCuspCutoff_smooth.differentiable (by simp)).differentiableAt.hasDerivAt).ofReal_comp
  have hv (y : ℝ) (hy : y∈uIcc (1:ℝ) 4) : HasDerivAt (fun y : ℝ => (y:ℂ)^w)
      (w*(y:ℂ)^(w-1)) y := by
    apply hasDerivAt_ofReal_cpow_const _ hw
    have hy1 : 1≤y := (show y∈Icc (1:ℝ) 4 by
      simpa only [uIcc_of_le (by norm_num : (1:ℝ)≤4)] using hy).1
    linarith
  have hdu : Continuous (fun y => ((deriv baseCuspCutoff y:ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp ((contDiff_infty_iff_deriv.mp baseCuspCutoff_smooth).2.continuous)
  have hdv : IntervalIntegrable (fun y : ℝ => w*(y:ℂ)^(w-1)) volume 1 4 :=
    (((power_continuous (w-1) 1 4 (by norm_num)).intervalIntegrable_of_Icc (by norm_num))).const_mul w
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun y _ => hu y) hv
    (hdu.intervalIntegrable 1 4) hdv
  have he : (∫ y in (1:ℝ)..4, (baseCuspCutoff y:ℂ)*(w*(y:ℂ)^(w-1)))=
      w*(nativeCutoffMellinContinuation w-1/w) := by
    calc
      _ = w*(∫ y in (1:ℝ)..4, (baseCuspCutoff y:ℂ)*(y:ℂ)^(w-1)) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro y _
        ring
      _ = _ := by rw [base_bulk w hw]
  rw [he,baseCuspCutoff_high 4 (by norm_num),baseCuspCutoff_low 1 (by norm_num)] at hp
  simp only [Complex.ofReal_zero,zero_mul,Complex.ofReal_one,Complex.one_cpow,one_mul,zero_sub] at hp
  have ha : w*(nativeCutoffMellinContinuation w-1/w)=w*nativeCutoffMellinContinuation w-1 := by
    field_simp
  rw [ha] at hp
  linear_combination -hp

private theorem cutoff_flux_scale (N : ℝ) (hN : 0<N) (w : ℂ) (hw : w≠0) :
    -(∫ y in N..(4*N), ((deriv (scaledCuspCutoff N) y:ℝ):ℂ)*(y:ℂ)^w)=
      w*(N:ℂ)^w*nativeCutoffMellinContinuation w := by
  let f := fun y : ℝ => ((deriv (scaledCuspCutoff N) y:ℝ):ℂ)*(y:ℂ)^w
  have he : (∫ x in (1:ℝ)..4, f (N*x))=
      ((N:ℂ)^w/(N:ℂ))*(∫ x in (1:ℝ)..4, ((deriv baseCuspCutoff x:ℝ):ℂ)*(x:ℂ)^w) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0≤x := le_trans (by norm_num : (0:ℝ)≤1)
      (show x∈Icc (1:ℝ) 4 by
        simpa only [uIcc_of_le (by norm_num : (1:ℝ)≤4)] using hx).1
    dsimp [f]
    rw [scaledCuspCutoff_deriv,mul_div_cancel_left₀ _ hN.ne',Complex.ofReal_div,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hN.le hx0]
    ring
  have hs := intervalIntegral.smul_integral_comp_mul_left (f := f) (a := (1:ℝ)) (b := 4) N
  rw [he] at hs
  change (N:ℂ)*(((N:ℂ)^w/(N:ℂ))*(∫ x in (1:ℝ)..4,
    ((deriv baseCuspCutoff x:ℝ):ℂ)*(x:ℂ)^w))=_ at hs
  have hn : (N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have ha : (N:ℂ)*((N:ℂ)^w/(N:ℂ))=(N:ℂ)^w := by field_simp
  rw [← mul_assoc,ha] at hs
  have hs' : (∫ y in N..(4*N), f y)=(N:ℂ)^w*(∫ x in (1:ℝ)..4,
      ((deriv baseCuspCutoff x:ℝ):ℂ)*(x:ℂ)^w) := by
    simpa only [mul_one,mul_comm N,one_mul] using hs.symm
  change -(∫ y in N..(4*N), f y)=_
  rw [hs',← mul_neg,base_flux w hw]
  ring

/-- Exponents of the complete quartic principal source, including all Weyl cross terms. -/
def quarticPrincipalExponent (q : XiZeroCopy) (j : Fin 5) : ℂ :=
  4-(j:ℂ)+(2*(j:ℂ)-4)*(q.1:ℂ)

/-- Same-occurrence physical test shifts the original quartic exponent by rho/2. -/
def quarticPhysicalMellinExponent (q : XiZeroCopy) (j : Fin 5) : ℂ :=
  quarticPrincipalExponent q j-(q.1:ℂ)/2

/-- None of the five original exponents meets the Mellin pole, from the literal Xi occurrence. -/
theorem quarticPhysicalMellinExponent_ne_zero (q : XiZeroCopy) (j : Fin 5) :
    quarticPhysicalMellinExponent q j≠0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  intro he
  have hh := congrArg Complex.im he
  fin_cases j <;> norm_num [quarticPhysicalMellinExponent,quarticPrincipalExponent] at hh <;>
    apply hi <;> linarith

/-- Finite separated transitions give the original Mellin correction for every quartic exponent. -/
theorem quarticCutoff_bulk_moment (q : XiZeroCopy) (j : Fin 5) (n : ℕ) :
    (∫ y in (2:ℝ)..(3*((n:ℝ)+2)), (scaledCuspCutoff ((n:ℝ)+2) y:ℂ)*cutoff ![0,y]*
      (y:ℂ)^(quarticPhysicalMellinExponent q j-1))=
      ((((n:ℝ)+2:ℝ):ℂ)^quarticPhysicalMellinExponent q j-1)*
        nativeCutoffMellinContinuation (quarticPhysicalMellinExponent q j) := by
  apply cutoff_bulk_scale _ _ _ (quarticPhysicalMellinExponent_ne_zero q j)
  have hn : (0:ℝ)≤n := by positivity
  linarith

/-- The differentiated cutoff flux retains its exact scale-dependent native Mellin term. -/
theorem quarticCutoff_flux_moment (q : XiZeroCopy) (j : Fin 5) (n : ℕ) :
    -(∫ y in ((n:ℝ)+2)..(4*((n:ℝ)+2)),
      ((deriv (scaledCuspCutoff ((n:ℝ)+2)) y:ℝ):ℂ)*(y:ℂ)^quarticPhysicalMellinExponent q j)=
      quarticPhysicalMellinExponent q j*((((n:ℝ)+2:ℝ):ℂ)^quarticPhysicalMellinExponent q j)*
        nativeCutoffMellinContinuation (quarticPhysicalMellinExponent q j) :=
  cutoff_flux_scale _ (by positivity) _ (quarticPhysicalMellinExponent_ne_zero q j)

end
end RHTower.D4BMQuarticCutoffMellin
