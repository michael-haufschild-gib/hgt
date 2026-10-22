import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalCountertermTransport

/-! The original twice-subtracted forcing becomes first Jacobi periods by exact integration by parts. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

theorem fundamentalJacobiComplexCore_real (n : ℕ) (s : ℂ) (x : ℝ) :
    fundamentalJacobiComplexCore n s (x:ℂ)=fundamentalJacobiCore n s x := by
  simp only [fundamentalJacobiComplexCore,fundamentalJacobiCore,Complex.ofReal_sub,
    Complex.ofReal_ofNat]
  ring

theorem fundamentalJacobiComplexCore_analyticAt_zero (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fundamentalJacobiComplexCore n s) 0 := by
  apply DifferentiableOn.analyticAt (s:={z : ℂ | z.re<2})
  · exact fun z hz => (fundamentalJacobiComplexCore_hasDerivAt n s hz).differentiableAt.differentiableWithinAt
  · exact (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by norm_num)

theorem fundamentalJacobiCore_second_sub_tendsto (n : ℕ) (w s : ℂ) (hw : -2 < w.re) :
    Tendsto (fun x : ℝ => (x:ℂ)^w*(fundamentalJacobiCore n s x-
      fundamentalJacobiCore n s 0-(x:ℂ)*fundamentalJacobiCoreFirst n s 0))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hd := (fundamentalJacobiComplexCore_analyticAt_zero n s).differentiableAt.hasDerivAt.comp_ofReal
  simp only [fundamentalJacobiComplexCore_real] at hd
  have he := hd.unique (fundamentalJacobiCore_hasDerivAt n s (by norm_num : (0:ℝ)<2))
  have h := fundamentalMoment_cpow_second_sub_tendsto
    (fundamentalJacobiComplexCore_analyticAt_zero n s) hw
  rw [he] at h
  have hz := fundamentalJacobiComplexCore_real n s 0
  simp only [Complex.ofReal_zero] at hz
  simpa only [fundamentalJacobiComplexCore_real,hz] using h

/-- The forcing derivative is a sum of two actual Jacobi cores, with no shifted
exponent beyond the admitted first-subtraction strip. -/
theorem fundamentalJacobiCoreFirst_forcing (n : ℕ) (s : ℂ) {x : ℝ} (hx : x<2) :
    -fundamentalJacobiCoreFirst n (s-1/2) x=
      (n:ℂ)*fundamentalJacobiCore (n-1) (s-1/2) x+
        (2*s-1)*fundamentalJacobiCore n (s-1) x := by
  dsimp only [fundamentalJacobiCoreFirst,fundamentalJacobiCore,power,powerFirst]
  rw [show 2*(s-1)=2*(s-1/2)-1 by ring,
    Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr (by linarith : (2-x:ℝ)≠0)),Complex.cpow_one]
  ring

def fundamentalJacobiForcingMoment (n : ℕ) (w s : ℂ) : ℂ :=
  (n:ℂ)*fundamentalJacobiMoment (n-1) w (s-1/2)+
    (2*s-1)*fundamentalJacobiMoment n w (s-1)

/-- The actual forcing retains its constant and slope subtractions. Its finite
part equals the displayed first-period combination with no boundary constant. -/
theorem fundamentalJacobiForcingMoment_cutoff (n : ℕ) (hn : 0 < n) (w s : ℂ)
    (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    Tendsto (fun e : ℝ =>
      w*(∫ x in e..1, (x:ℂ)^(w-1)*fundamentalJacobiCore n (s-1/2) x)+
      fundamentalJacobiCore n (s-1/2) 0*(e:ℂ)^w+
      w*fundamentalJacobiCoreFirst n (s-1/2) 0*(e:ℂ)^(w+1)/(w+1))
      (𝓝[>] (0:ℝ)) (𝓝 (fundamentalJacobiForcingMoment n w s)) := by
  let g := fundamentalJacobiCore n (s-1/2)
  let g' := fundamentalJacobiCoreFirst n (s-1/2)
  have hj := ((fundamentalJacobiMoment_cutoff (n-1) w (s-1/2) hw hw1).const_mul (n:ℂ)).add
    ((fundamentalJacobiMoment_cutoff n w (s-1) hw hw1).const_mul (2*s-1))
  have hr := fundamentalJacobiCore_second_sub_tendsto n w (s-1/2) hw
  have h := hj.sub hr
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with e he
  have hg : IntervalIntegrable (fun x : ℝ => (x:ℂ)^(w-1)*g x) volume e 1 :=
    fundamentalJacobiDensity_intervalIntegrable n (w-1) (s-1/2) he.1 he.2.le
  have hg' : IntervalIntegrable (fun x : ℝ => (x:ℂ)^w*g' x) volume e 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc he.2.le
    intro x hx
    exact ((power_derivatives w (he.1.trans_le hx.1)).1.continuousAt.mul
      (fundamentalJacobiCoreFirst_continuousAt n (s-1/2) (by linarith [hx.2]))).continuousWithinAt
  have hp : (∫ x in e..1, w*((x:ℂ)^(w-1)*g x)+(x:ℂ)^w*g' x)=
      -((e:ℂ)^w*g e) := by
    have hFTC : (∫ x in e..1, w*((x:ℂ)^(w-1)*g x)+(x:ℂ)^w*g' x)=
        ((1:ℝ):ℂ)^w*g 1-(e:ℂ)^w*g e := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun x : ℝ => (x:ℂ)^w*g x)
      · intro x hx
        rw [uIcc_of_le he.2.le] at hx
        apply (((power_derivatives w (he.1.trans_le hx.1)).1).mul
          (fundamentalJacobiCore_hasDerivAt n (s-1/2) (by linarith [hx.2]))).congr_deriv
        dsimp only [power,powerFirst]
        rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr (he.1.trans_le hx.1).ne'),Complex.cpow_one]
        ring
      · exact (hg.const_mul w).add hg'
    simpa only [g,fundamentalJacobiCore,Complex.ofReal_one,sub_self,zero_pow hn.ne',zero_mul,
      mul_zero,zero_sub] using hFTC
  rw [intervalIntegral.integral_add (hg.const_mul w) hg',intervalIntegral.integral_const_mul] at hp
  have hsplit : -(∫ x in e..1, (x:ℂ)^w*g' x)=
      (n:ℂ)*(∫ x in e..1, (x:ℂ)^w*fundamentalJacobiCore (n-1) (s-1/2) x)+
      (2*s-1)*(∫ x in e..1, (x:ℂ)^w*fundamentalJacobiCore n (s-1) x) := by
    rw [← intervalIntegral.integral_neg,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        ((fundamentalJacobiDensity_intervalIntegrable (n-1) w (s-1/2) he.1 he.2.le).const_mul _)
        ((fundamentalJacobiDensity_intervalIntegrable n w (s-1) he.1 he.2.le).const_mul _)]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le he.2.le] at hx
    have hf := fundamentalJacobiCoreFirst_forcing n s (by linarith [hx.2] : x<2)
    dsimp only [g']
    linear_combination (x:ℂ)^w*hf
  have hzero := fundamentalJacobiCoreFirst_forcing n s (by norm_num : (0:ℝ)<2)
  simp only [fundamentalJacobiCore_zero] at hzero
  change _ = w*(∫ x in e..1, (x:ℂ)^(w-1)*g x)+g 0*(e:ℂ)^w+
    w*g' 0*(e:ℂ)^(w+1)/(w+1)
  dsimp only [g',g] at hp hsplit ⊢
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr he.1.ne'),Complex.cpow_one]
  field_simp [hw1] at hp hsplit hzero ⊢
  linear_combination -(w+1)*hp-(w+1)*hsplit-(e:ℂ)^w*(e:ℂ)*hzero

end
end RHTower.D4BMJointSource
