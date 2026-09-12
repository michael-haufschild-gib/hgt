import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalJacobiMoment

/-! Boundary-preserving integration by parts for the original polynomial-coordinate moments. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

def fundamentalJacobiPrimitive (n : ℕ) (w s : ℂ) (x : ℝ) : ℂ :=
  power (w+1) x * fundamentalJacobiCore n (s+1/2) x

theorem fundamentalJacobiPrimitive_hasDerivAt (n : ℕ) (w s : ℂ) {x : ℝ}
    (hx : 0 < x) (hx2 : x < 2) :
    HasDerivAt (fundamentalJacobiPrimitive n w s)
      ((x:ℂ)^w*((w+2*s+2+(n:ℂ))*fundamentalJacobiCore (n+1) s x-
        (n:ℂ)*fundamentalJacobiCore (n-1) s x-(2*s-w)*fundamentalJacobiCore n s x)) x := by
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hp0 : ((2-x:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hpw : (x:ℂ)^(w+1)=(x:ℂ)^w*(x:ℂ) := by rw [Complex.cpow_add _ _ hx0,Complex.cpow_one]
  have hps : ((2-x:ℝ):ℂ)^(2*s+1)=((2-x:ℝ):ℂ)^(2*s)*((2-x:ℝ):ℂ) := by
    rw [Complex.cpow_add _ _ hp0,Complex.cpow_one]
  have hd := (power_derivatives (w+1) hx).1.mul
    (fundamentalJacobiCore_hasDerivAt n (s+1/2) hx2)
  apply hd.congr_deriv
  dsimp only [powerFirst,power,fundamentalJacobiCoreFirst,fundamentalJacobiCore]
  simp only [show 2*(s+1/2)=2*s+1 by ring,hpw,hps]
  field_simp [hx0,hp0]
  cases n with
  | zero => simp only [Nat.zero_sub,Nat.cast_zero,zero_mul,pow_zero]; push_cast; ring
  | succ n => simp only [Nat.add_sub_cancel,pow_succ,Nat.cast_add,Nat.cast_one]; push_cast; ring


/-- The lower subtraction retains the nonzero upper boundary term in the zeroth recurrence. -/
theorem fundamentalJacobiMoment_recurrence (n : ℕ) (w s : ℂ)
    (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    (n:ℂ)*fundamentalJacobiMoment (n-1) w s+(2*s-w)*fundamentalJacobiMoment n w s-
      (w+2*s+2+(n:ℂ))*fundamentalJacobiMoment (n+1) w s = -(0:ℂ)^n := by
  let c := w+2*s+2+(n:ℂ)
  let d := 2*s-w
  have hl := (((fundamentalJacobiMoment_cutoff (n-1) w s hw hw1).const_mul (n:ℂ)).add
    ((fundamentalJacobiMoment_cutoff n w s hw hw1).const_mul d)).sub
    ((fundamentalJacobiMoment_cutoff (n+1) w s hw hw1).const_mul c)
  have hg := fundamentalJacobiCore_hasDerivAt n (s+1/2) (by norm_num : (0:ℝ)<2)
  have hr := (fundamentalMoment_cpow_mul_sub_tendsto hg hw).sub_const ((0:ℂ)^n)
  simp only [zero_sub] at hr
  apply tendsto_nhds_unique hl
  apply hr.congr'
  have he1 : ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < 1 := Iio_mem_nhds (by norm_num)
  filter_upwards [self_mem_nhdsWithin,he1.filter_mono nhdsWithin_le_nhds] with e he he1
  have hi (k : ℕ) := fundamentalJacobiDensity_intervalIntegrable k w s he he1.le
  have hf : (∫ x in e..1, c*((x:ℂ)^w*fundamentalJacobiCore (n+1) s x)-
      (n:ℂ)*((x:ℂ)^w*fundamentalJacobiCore (n-1) s x)-d*((x:ℂ)^w*fundamentalJacobiCore n s x)) =
      fundamentalJacobiPrimitive n w s 1-fundamentalJacobiPrimitive n w s e := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [uIcc_of_le he1.le] at hx
      exact (fundamentalJacobiPrimitive_hasDerivAt n w s (he.trans_le hx.1)
        (by linarith [hx.2])).congr_deriv (by dsimp only [c,d]; ring)
    · exact (((hi (n+1)).const_mul c).sub ((hi (n-1)).const_mul (n:ℂ))).sub ((hi n).const_mul d)
  rw [intervalIntegral.integral_sub
      (((hi (n+1)).const_mul c).sub ((hi (n-1)).const_mul (n:ℂ))) ((hi n).const_mul d),
    intervalIntegral.integral_sub ((hi (n+1)).const_mul c) ((hi (n-1)).const_mul (n:ℂ)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hf
  have ht : fundamentalJacobiPrimitive n w s 1=(0:ℂ)^n := by
    simp [fundamentalJacobiPrimitive,fundamentalJacobiCore,power]
    norm_num
  rw [ht,fundamentalJacobiPrimitive] at hf
  have h0 : fundamentalJacobiCore n (s+1/2) 0=(2:ℂ)^(2*s+1) := by
    rw [fundamentalJacobiCore_zero]
    congr 1
    ring
  have hct : (n:ℂ)*((2:ℂ)^(2*s)*(e:ℂ)^(w+1)/(w+1))+
      d*((2:ℂ)^(2*s)*(e:ℂ)^(w+1)/(w+1))-
      c*((2:ℂ)^(2*s)*(e:ℂ)^(w+1)/(w+1)) = -(2:ℂ)^(2*s+1)*(e:ℂ)^(w+1) := by
    rw [Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),Complex.cpow_one]
    dsimp only [c,d]
    field_simp [hw1]
    ring
  rw [h0]
  dsimp only [power] at hf
  linear_combination hf-hct


/-- The source's second moment is fixed by the base period and retained boundary constant. -/
theorem fundamentalJacobiMoment_second (w s : ℂ) (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    let d := 2*s-w
    let e := w+2*s+2
    e*(e+1)*fundamentalJacobiMoment 2 w s =
      (e+d^2)*fundamentalJacobiMoment 0 w s+d := by
  have h0 := fundamentalJacobiMoment_recurrence 0 w s hw hw1
  have h1 := fundamentalJacobiMoment_recurrence 1 w s hw hw1
  norm_num only at h0 h1
  dsimp only
  linear_combination -(w+2*s+2)*h1-(2*s-w)*h0

private theorem fundamentalJacobiMoment_third (w s : ℂ) (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    let d := 2*s-w
    let e := w+2*s+2
    e*(e+1)*(e+2)*fundamentalJacobiMoment 3 w s =
      d*(d^2+3*e+2)*fundamentalJacobiMoment 0 w s+(d^2+2*e+2) := by
  have h0 := fundamentalJacobiMoment_recurrence 0 w s hw hw1
  have h2 := fundamentalJacobiMoment_recurrence 2 w s hw hw1
  have hs := fundamentalJacobiMoment_second w s hw hw1
  norm_num only at h0 h2
  dsimp only at hs ⊢
  linear_combination -(w+2*s+2)*((w+2*s+2)+1)*h2+(2*s-w)*hs-2*((w+2*s+2)+1)*h0

/-- The source's fourth moment has an exact base-period reduction with its boundary term retained. -/
theorem fundamentalJacobiMoment_fourth (w s : ℂ) (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    let d := 2*s-w
    let e := w+2*s+2
    e*(e+1)*(e+2)*(e+3)*fundamentalJacobiMoment 4 w s =
      (d^4+(6*e+8)*d^2+3*e*(e+2))*fundamentalJacobiMoment 0 w s+d*(d^2+5*e+8) := by
  have h3 := fundamentalJacobiMoment_recurrence 3 w s hw hw1
  have hs := fundamentalJacobiMoment_second w s hw hw1
  have ht := fundamentalJacobiMoment_third w s hw hw1
  norm_num only at h3
  dsimp only at hs ht ⊢
  linear_combination -(w+2*s+2)*((w+2*s+2)+1)*((w+2*s+2)+2)*h3+
    3*((w+2*s+2)+2)*hs+(2*s-w)*ht

end
end RHTower.D4BMJointSource
