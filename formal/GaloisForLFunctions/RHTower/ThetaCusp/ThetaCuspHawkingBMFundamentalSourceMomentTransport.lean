import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalJacobiRecurrence

/-! The actual physical source moment in the smooth polynomial coordinate, with its original subtraction. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

theorem fundamentalSourceCore_scaled_endpoint (w s a : ℂ) :
    fundamentalSourceCore w s a 0*(2:ℂ)^(w+1) =
      2*a^(2 : ℕ)*(fundamentalMomentConstant s+fundamentalMomentQuadratic w s)*(2:ℂ)^(2*s) := by
  rw [fundamentalSourceCore_zero_polynomial]
  calc
    _ = a^(2 : ℕ)*(fundamentalMomentConstant s+fundamentalMomentQuadratic w s)*
        ((2:ℂ)^(2*s-w)*(2:ℂ)^(w+1)) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),
        show (2*s-w)+(w+1)=2*s+1 by ring,
        Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),Complex.cpow_one]
      ring

/-- The original and transformed counterterms have a vanishing difference on the physical strip. -/
theorem fundamentalSourceMoment_counterterm_transport (w s a : ℂ) (hw : -2 < w.re) :
    Tendsto (fun e : ℝ => fundamentalSourceCore w s a 0*((e*(2-e):ℝ):ℂ)^(w+1)/(w+1)-
      2*a^(2 : ℕ)*(fundamentalMomentConstant s+fundamentalMomentQuadratic w s)*
        (2:ℂ)^(2*s)*(e:ℂ)^(w+1)/(w+1))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hG : HasDerivAt (fun x : ℝ => power (w+1) (2-x)) (-powerFirst (w+1) 2) 0 := by
    simpa only [sub_zero,zero_sub,neg_one_smul,Function.comp_apply,Pi.sub_apply,id_eq] using!
      (power_derivatives (w+1) (by norm_num : (0:ℝ)<2-0)).1.scomp 0
        ((hasDerivAt_const 0 (2:ℝ)).sub (hasDerivAt_id 0))
  have h := (fundamentalMoment_cpow_mul_sub_tendsto hG hw).const_mul
    (fundamentalSourceCore w s a 0/(w+1))
  simp only [mul_zero] at h
  apply h.congr'
  have he1 : ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < 1 := Iio_mem_nhds (by norm_num)
  filter_upwards [self_mem_nhdsWithin,he1.filter_mono nhdsWithin_le_nhds] with e he he1
  have hp : ((e*(2-e):ℝ):ℂ)^(w+1)=(e:ℂ)^(w+1)*((2-e:ℝ):ℂ)^(w+1) := by
    simpa only [Complex.ofReal_mul] using
      Complex.mul_cpow_ofReal_nonneg he.le (by linarith : 0≤2-e) (w+1)
  rw [hp,← fundamentalSourceCore_scaled_endpoint]
  dsimp only [power]
  norm_num only [sub_zero,Complex.ofReal_ofNat]
  ring

/-- The same original finite-part moment has its full-endpoint physical cutoff limit. -/
theorem physicalFundamentalSourceMoment_cutoff (q : XiZeroCopy) (branch side : Bool) (a : ℂ) :
    let w := physicalFundamentalFrequency q side
    let s := D4BMModularCore.physicalRate q branch
    Tendsto (fun e : ℝ => (∫ z in e..1, (z:ℂ)^w*fundamentalSourceCore w s a z)+
      fundamentalSourceCore w s a 0*(e:ℂ)^(w+1)/(w+1))
      (𝓝[>] (0:ℝ)) (𝓝 (fundamentalSourceMoment w s a)) := by
  dsimp only
  have hw := physicalFundamentalFrequency_strip q side
  have hw1 : physicalFundamentalFrequency q side+1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im] at hi
    exact hw.1 hi
  have hP := physicalFundamentalSourceMoment_integral q branch side a
  have h := firstEndpointMellin_cutoff_of_integrable
    (fundamentalSourceCore (physicalFundamentalFrequency q side) (D4BMModularCore.physicalRate q branch) a)
    (physicalFundamentalFrequency q side) hw1 hP.1
  have he : firstEndpointMellin
      (fun _ => fundamentalSourceCore (physicalFundamentalFrequency q side) (D4BMModularCore.physicalRate q branch) a)
      1 (physicalFundamentalFrequency q side) =
      fundamentalSourceMoment (physicalFundamentalFrequency q side) (D4BMModularCore.physicalRate q branch) a := by
    simpa only [firstEndpointMellin,firstEndpointMellinRemainder,Complex.ofReal_one,
      Complex.one_cpow,mul_one] using hP.2.symm
  rwa [he] at h

/-- The actual physical source is an exact second/fourth polynomial-moment combination. -/
theorem physicalFundamentalSourceMoment_polynomial (q : XiZeroCopy) (branch side : Bool) (a : ℂ) :
    let w := physicalFundamentalFrequency q side
    let s := D4BMModularCore.physicalRate q branch
    fundamentalSourceMoment w s a = 2*a^(2 : ℕ)*(fundamentalMomentConstant s*fundamentalJacobiMoment 2 w s+
      fundamentalMomentQuadratic w s*fundamentalJacobiMoment 4 w s) := by
  let w := physicalFundamentalFrequency q side
  let s := D4BMModularCore.physicalRate q branch
  have hw := physicalFundamentalFrequency_strip q side
  have hwr : -2 < w.re := (abs_lt.mp hw.2).1
  have hw1 : w+1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im] at hi
    exact hw.1 hi
  have hevent : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e ∈ Ioc (0:ℝ) 1 := by
    have he1 : ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < 1 := Iio_mem_nhds (by norm_num)
    filter_upwards [self_mem_nhdsWithin,he1.filter_mono nhdsWithin_le_nhds] with e he he1
    exact ⟨he,he1.le⟩
  have hphi : Tendsto (fun x : ℝ => x*(2-x)) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · have h : ContinuousAt (fun x : ℝ => x*(2-x)) 0 := by fun_prop
      simpa only [zero_mul] using h.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [hevent] with e he
      exact mul_pos he.1 (by linarith [he.2])
  have ho := (physicalFundamentalSourceMoment_cutoff q branch side a).comp hphi
  have hc := fundamentalSourceMoment_counterterm_transport w s a hwr
  have ht := ho.sub hc
  simp only [sub_zero] at ht
  have hj := (((fundamentalJacobiMoment_cutoff 2 w s hwr hw1).const_mul (fundamentalMomentConstant s)).add
    ((fundamentalJacobiMoment_cutoff 4 w s hwr hw1).const_mul (fundamentalMomentQuadratic w s))).const_mul (2*a^(2 : ℕ))
  apply tendsto_nhds_unique _ hj
  apply ht.congr'
  filter_upwards [hevent] with e he
  change ((∫ z in e*(2-e)..1, (z:ℂ)^w*fundamentalSourceCore w s a z)+
    fundamentalSourceCore w s a 0*((e*(2-e):ℝ):ℂ)^(w+1)/(w+1))-
    (fundamentalSourceCore w s a 0*((e*(2-e):ℝ):ℂ)^(w+1)/(w+1)-
      2*a^(2 : ℕ)*(fundamentalMomentConstant s+fundamentalMomentQuadratic w s)*
        (2:ℂ)^(2*s)*(e:ℂ)^(w+1)/(w+1)) = _
  rw [fundamentalSourceMoment_polynomial_cutoff w s a he.1 he.2]
  ring


/-- The original physical source reduces to one base period and an explicit retained boundary term. -/
theorem physicalFundamentalSourceMoment_base_period (q : XiZeroCopy) (branch side : Bool) (a : ℂ) :
    let w := physicalFundamentalFrequency q side
    let s := D4BMModularCore.physicalRate q branch
    let d := 2*s-w
    let e := w+2*s+2
    e*(e+1)*(e+2)*(e+3)*fundamentalSourceMoment w s a =
      2*a^(2 : ℕ)*((fundamentalMomentConstant s*(e+d^(2 : ℕ))*(e+2)*(e+3)+
        fundamentalMomentQuadratic w s*(d^(4 : ℕ)+(6*e+8)*d^(2 : ℕ)+3*e*(e+2)))*
          fundamentalJacobiMoment 0 w s+
        d*(fundamentalMomentConstant s*(e+2)*(e+3)+fundamentalMomentQuadratic w s*(d^(2 : ℕ)+5*e+8))) := by
  let w := physicalFundamentalFrequency q side
  let s := D4BMModularCore.physicalRate q branch
  have hw := physicalFundamentalFrequency_strip q side
  have hwr : -2 < w.re := (abs_lt.mp hw.2).1
  have hw1 : w+1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im] at hi
    exact hw.1 hi
  have h2 := fundamentalJacobiMoment_second w s hwr hw1
  have h4 := fundamentalJacobiMoment_fourth w s hwr hw1
  change (w+2*s+2)*((w+2*s+2)+1)*((w+2*s+2)+2)*((w+2*s+2)+3)*fundamentalSourceMoment w s a = _
  rw [physicalFundamentalSourceMoment_polynomial q branch side a]
  dsimp only at h2 h4 ⊢
  linear_combination 2*a^(2 : ℕ)*fundamentalMomentConstant s*((w+2*s+2)+2)*((w+2*s+2)+3)*h2+
    2*a^(2 : ℕ)*fundamentalMomentQuadratic w s*h4

end
end RHTower.D4BMJointSource
