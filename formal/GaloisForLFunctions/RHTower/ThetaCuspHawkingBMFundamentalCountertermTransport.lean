import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalCanonicalContour
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSelfChannelHorizonJet

/-! Exact transport of the original logarithmic source counterterm. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- Positive complex powers absorb the actual logarithmic horizon singularity. -/
theorem fundamentalMoment_cpow_log_tendsto {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun x : ℝ => (x:ℂ)^w*(Real.log x:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (tendsto_log_mul_rpow_nhdsGT_zero hw).norm
  simp only [norm_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [norm_mul,Complex.norm_real,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  ring

/-- A differentiable source coefficient transports its logarithmic counterterm
without leaving any finite discrepancy on the full physical strip. -/
theorem fundamentalMoment_cpow_log_mul_sub_tendsto {G : ℝ → ℂ} {g w : ℂ}
    (hG : HasDerivAt G g 0) (hw : -2 < w.re) :
    Tendsto (fun x : ℝ => (x:ℂ)^(w+1)*(G x-G 0)*(Real.log x:ℂ))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hs := hG.tendsto_slope_zero_right
  simp only [zero_add,Complex.real_smul,Complex.ofReal_inv] at hs
  have hp := fundamentalMoment_cpow_log_tendsto
    (w:=w+2) (by change 0 < w.re+2; linarith)
  have h := hp.mul hs
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [show w+2=(w+1)+1 by ring,Complex.cpow_add _ _ hx0,Complex.cpow_one]
  field_simp

/-- Exact tortoise coordinate under the smooth polynomial radius. -/
theorem tortoiseOf_polynomial_coordinate {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    tortoiseOf (x*(2-x))=(Real.log x-Real.log (2-x))/2 := by
  have h2 : 0 < 2-x := by linarith
  have hr : Real.sqrt (1-x*(2-x))=1-x := by
    rw [show 1-x*(2-x)=(1-x)^2 by ring,Real.sqrt_sq (sub_nonneg.mpr hx1)]
  rw [tortoiseOf,hr,show 1+(1-x)=2-x by ring,
    Real.log_div (Real.sqrt_pos.mpr (mul_pos hx h2)).ne' h2.ne',
    Real.log_sqrt (mul_pos hx h2).le,Real.log_mul hx.ne' h2.ne']
  ring

/-- Original log-two normalization survives the nonlinear radius substitution. -/
theorem fundamentalMoment_log_counterterm_transport (b w : ℂ) (hw : -2 < w.re) :
    Tendsto (fun e : ℝ =>
      b*((e*(2-e):ℝ):ℂ)^(w+1)*
        (((Real.log (e*(2-e)):ℂ)/2-(Real.log 2:ℂ))/(w+1)-1/(2*(w+1)^2))-
      b*(2:ℂ)^(w+1)*(e:ℂ)^(w+1)*
        (((Real.log e:ℂ)-(Real.log 2:ℂ))/(2*(w+1))-1/(2*(w+1)^2)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let P : ℝ → ℂ := fun x => power (w+1) (2-x)
  let L : ℝ → ℂ := fun x => (Real.log (2-x):ℂ)
  have hP : HasDerivAt P (-powerFirst (w+1) 2) 0 := by
    simpa only [sub_zero,zero_sub,neg_one_smul,Function.comp_apply,Pi.sub_apply,id_eq] using!
      (power_derivatives (w+1) (by norm_num : (0:ℝ)<2-0)).1.scomp 0
        ((hasDerivAt_id (0:ℝ)).const_sub 2)
  have hL : HasDerivAt L (-1/2:ℂ) 0 := by
    have h := ((Real.hasDerivAt_log (by norm_num : (2:ℝ)-0≠0)).comp 0
      ((hasDerivAt_id (0:ℝ)).const_sub 2)).ofReal_comp
    convert h using 1 <;> norm_num [L,Function.comp_def]
  have h0 := fundamentalMoment_cpow_mul_sub_tendsto (w:=w) hP hw
  have h1 := fundamentalMoment_cpow_log_mul_sub_tendsto (w:=w) hP hw
  have h2 := (fundamentalMoment_cpow_mul_sub_tendsto (w:=w) hL hw).mul
    (hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have h := (((h1.sub (h0.mul_const (Real.log 2:ℂ))).div_const (2*(w+1))).sub
    (h0.div_const (2*(w+1)^2))).add (h2.div_const (2*(w+1)))
  have hb := h.const_mul b
  simp only [zero_mul,sub_self,zero_div,zero_add,mul_zero] at hb
  apply hb.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with e he
  have he2 : 0 < 2-e := by linarith [he.2]
  have hp : ((e*(2-e):ℝ):ℂ)^(w+1)=(e:ℂ)^(w+1)*((2-e:ℝ):ℂ)^(w+1) := by
    simpa only [Complex.ofReal_mul] using
      Complex.mul_cpow_ofReal_nonneg he.1.le he2.le (w+1)
  rw [hp,Real.log_mul he.1.ne' he2.ne']
  dsimp only [P,L,power]
  simp only [sub_zero,Complex.ofReal_ofNat,Complex.ofReal_add,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Analyticity removes the original quadratic forcing remainder, including
complex frequencies with real part below minus one. -/
theorem fundamentalMoment_cpow_second_sub_tendsto {G : ℂ → ℂ} {w : ℂ}
    (hG : AnalyticAt ℂ G 0) (hw : -2 < w.re) :
    Tendsto (fun x : ℝ => (x:ℂ)^w*(G (x:ℂ)-G 0-(x:ℂ)*deriv G 0))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨p,hp⟩ := hG
  have hd := hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt.hasDerivAt
  have h := fundamentalMoment_cpow_mul_sub_tendsto (w:=w) hd.comp_ofReal hw
  simp only [Complex.ofReal_zero,dslope_same] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.cpow_add _ _ hx0,Complex.cpow_one]
  have hs := sub_smul_dslope G (0:ℂ) (x:ℂ)
  simp only [sub_zero,smul_eq_mul] at hs
  linear_combination (x:ℂ)^w*hs

theorem fundamentalMoment_two_sub_analyticAt (w : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (2-z)^w) 0 := by
  apply DifferentiableOn.analyticAt (s:={z : ℂ | z.re<2})
  · intro z hz
    have hs : 2-z ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      change 0<2-z.re
      change z.re<2 at hz
      linarith
    exact (((hasDerivAt_id z).const_sub 2).cpow_const hs).differentiableAt.differentiableWithinAt
  · exact (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by norm_num)

/-- Both original forcing counterterms transport together; the radial slope
supplies the additional first-order term and cannot be dropped. -/
theorem fundamentalMoment_forcing_counterterm_transport (b c w : ℂ) (hw : -2 < w.re)
    (hw1 : w+1 ≠ 0) :
    Tendsto (fun e : ℝ =>
      b*((e*(2-e):ℝ):ℂ)^w+w*c*((e*(2-e):ℝ):ℂ)^(w+1)/(w+1)-
      (b*(2:ℂ)^w*(e:ℂ)^w+
        w*(-(w+1)*b*(2:ℂ)^w/2+(2:ℂ)^(w+1)*c)*(e:ℂ)^(w+1)/(w+1)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hd : HasDerivAt (fun z : ℂ => (2-z)^w) (-w*(2:ℂ)^w/2) 0 := by
    have hs : (2:ℂ)-(0:ℂ) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      norm_num
    apply (((hasDerivAt_id (0:ℂ)).const_sub 2).cpow_const hs).congr_deriv
    simp only [id_eq,sub_zero,mul_neg,mul_one]
    rw [Complex.cpow_sub _ _ (by norm_num : (2:ℂ)≠0),Complex.cpow_one]
    ring
  have h0 := fundamentalMoment_cpow_second_sub_tendsto
    (fundamentalMoment_two_sub_analyticAt w) hw
  rw [hd.deriv] at h0
  have hP : HasDerivAt (fun x : ℝ => power (w+1) (2-x)) (-powerFirst (w+1) 2) 0 := by
    simpa only [sub_zero,zero_sub,neg_one_smul,Function.comp_apply,Pi.sub_apply,id_eq] using!
      (power_derivatives (w+1) (by norm_num : (0:ℝ)<2-0)).1.scomp 0
        ((hasDerivAt_id (0:ℝ)).const_sub 2)
  have h1 := fundamentalMoment_cpow_mul_sub_tendsto (w:=w) hP hw
  have h := (h0.const_mul b).add ((h1.const_mul (w*c)).div_const (w+1))
  simp only [mul_zero,zero_div,zero_add] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with e he
  have he2 : 0 < 2-e := by linarith [he.2]
  have hp (v : ℂ) : ((e*(2-e):ℝ):ℂ)^v=(e:ℂ)^v*((2-e:ℝ):ℂ)^v := by
    simpa only [Complex.ofReal_mul] using
      Complex.mul_cpow_ofReal_nonneg he.1.le he2.le v
  rw [hp w,hp (w+1)]
  dsimp only [power]
  simp only [Complex.ofReal_sub,Complex.ofReal_ofNat,sub_zero]
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr he.1.ne'),Complex.cpow_one,
    Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),Complex.cpow_one]
  field_simp [hw1]
  ring

end
end RHTower.D4BMJointSource
