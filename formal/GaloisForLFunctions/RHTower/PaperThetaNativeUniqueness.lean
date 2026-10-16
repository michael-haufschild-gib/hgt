import GaloisForLFunctions.RHTower.PaperThetaForcedConnection

/-! # Native uniqueness without a spectral-span assumption

A weighted zero-tail solution is constant, hence zero. The actual bounded
theta-mode selector then removes every off-divisor homogeneous solution on
the whole native domain, including profiles outside every finite Xi packet.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

theorem tendsto_thetaWeight_atTop (z : ℂ) :
    Tendsto (fun x : ℝ => (thetaSource.normalized x : ℂ)*sourceChar z x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := (tendsto_normalized_mul_exp_atBot_all (-z.im)).comp tendsto_neg_atTop_atBot
  convert ht using 1
  funext x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaSource.normalized_pos x), norm_sourceChar, Function.comp_apply,
    normalized_reflection]
  congr 2
  ring

theorem nativeODE_zero_of_trace_zero (z : ℂ) (f : ℝ → ℂ)
    (hf : Differentiable ℝ f) (ht : Tendsto f atTop (𝓝 0))
    (he : ∀ x, deriv f x+(sourceLogDerivative x+I*z)*f x = 0) : f = 0 := by
  let w : ℝ → ℂ := fun x => (thetaSource.normalized x : ℂ)*sourceChar z x*f x
  have hw (x : ℝ) : HasDerivAt w 0 x := by
    have hρ := ((differentiable_normalized_theta x).hasDerivAt.ofReal_comp).differentiableAt.hasDerivAt
    have hρ0 : (thetaSource.normalized x : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (thetaSource.normalized_pos x).ne'
    have hc : HasDerivAt (sourceChar z) (I*z*sourceChar z x) x := by
      change HasDerivAt (fun y : ℝ => Complex.exp (I*z*(y : ℂ)))
        (I*z*Complex.exp (I*z*(x : ℂ))) x
      simpa [mul_comm] using
        (((hasDerivAt_id (x : ℂ)).const_mul (I*z)).cexp).comp_ofReal
    refine ((hρ.mul hc).mul (hf x).hasDerivAt).congr_deriv ?_
    have hx := he x
    dsimp [sourceLogDerivative] at hx
    field_simp at hx
    simp only [Pi.mul_apply]
    linear_combination sourceChar z x*hx
  have hc : ∀ x, w x = w 0 := fun x =>
    is_const_of_deriv_eq_zero (fun x => (hw x).differentiableAt) (fun x => (hw x).deriv) x 0
  have hz : Tendsto w atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_thetaWeight_atTop z).mul ht
  have hconst : Tendsto w atTop (𝓝 (w 0)) :=
    tendsto_const_nhds.congr fun x => (hc x).symm
  have h0 : w 0 = 0 := (tendsto_nhds_unique hz hconst).symm
  funext x
  have hx : w x = 0 := (hc x).trans h0
  have hn : (thetaSource.normalized x : ℂ)*sourceChar z x ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (thetaSource.normalized_pos x).ne')
      (Complex.exp_ne_zero _)
  exact (mul_eq_zero.mp hx).resolve_left hn

/-- Every homogeneous solution with a finite right trace is the literal theta mode. -/
theorem nativeHomogeneous_eq (z : ℂ) (f : ℝ → ℂ) (c : ℂ)
    (hf : Differentiable ℝ f) (ht : Tendsto f atTop (𝓝 c))
    (he : ∀ x, deriv f x+sourceLogDerivative x*(f x-c)+I*z*f x = 0) (x : ℝ) :
    f x = -c*flatQuotient z x := by
  let v : ℝ → ℂ := fun y => f y+c*flatQuotient z y
  have hv : Differentiable ℝ v := hf.add ((differentiable_flatQuotient z).const_mul c)
  have ht' : Tendsto v atTop (𝓝 0) := by
    have h := ht.add ((tendsto_flatQuotient_atTop z).const_mul c)
    simpa only [mul_neg_one, add_neg_cancel] using h
  have he' (y : ℝ) : deriv v y+(sourceLogDerivative y+I*z)*v y = 0 := by
    have hd := ((hf y).hasDerivAt.add
      (((differentiable_flatQuotient z) y).hasDerivAt.const_mul c)).deriv
    change deriv v y = _ at hd
    rw [hd]
    dsimp [v]
    linear_combination he y+c*(flatQuotient_source_equation z y)
  have hz := congrFun (nativeODE_zero_of_trace_zero z v hv ht' he') x
  change f x+c*flatQuotient z x = 0 at hz
  linear_combination hz

theorem nativeHomogeneous_zero {z : ℂ} (hz : z ≠ 0) (hXi : XiC z ≠ 0)
    (f : ℝ → ℂ) (c : ℂ) (hf : Differentiable ℝ f) (ht : Tendsto f atTop (𝓝 c))
    (hb : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    (he : ∀ x, deriv f x+sourceLogDerivative x*(f x-c)+I*z*f x = 0) : f = 0 := by
  have hm := nativeHomogeneous_eq z f c hf ht he
  have hc : c = 0 := by
    by_contra hc
    obtain ⟨M, hM⟩ := hb
    have hq : ∃ K : ℝ, ∀ x, ‖flatQuotient z x‖ ≤ K := by
      refine ⟨‖(-c)⁻¹‖*M, fun x => ?_⟩
      have hid : flatQuotient z x = (-c)⁻¹*f x := by
        rw [hm x, ← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hc), one_mul]
      rw [hid, norm_mul]
      exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)
    exact ((bounded_flatQuotient_iff z).mp hq).elim hz hXi
  funext x
  simp only [hm x, hc, neg_zero, zero_mul, Pi.zero_apply]

/-- Whole-domain uniqueness; no modal membership or zero-series hypothesis. -/
theorem nativeSolution_unique {z : ℂ} (hz : z ≠ 0) (hXi : XiC z ≠ 0)
    (f h : ThetaNativeDomain)
    (he : ∀ x, thetaSpatialAction f x-z*f x = thetaSpatialAction h x-z*h x) : f = h := by
  let v : ℝ → ℂ := fun x => f x-h x
  let c := thetaTailTrace f-thetaTailTrace h
  have hv : Differentiable ℝ v := f.differentiable.sub h.differentiable
  have ht : Tendsto v atTop (𝓝 c) := f.rightTrace.sub h.rightTrace
  have hb : ∃ M : ℝ, ∀ x, ‖v x‖ ≤ M :=
    ⟨f.toThetaContinuousBV.bound+h.toThetaContinuousBV.bound, fun x =>
      (norm_sub_le _ _).trans (add_le_add (f.toThetaContinuousBV.norm_le x)
        (h.toThetaContinuousBV.norm_le x))⟩
  have he' (x : ℝ) : deriv v x+sourceLogDerivative x*(v x-c)+I*z*v x = 0 := by
    rw [show deriv v x = deriv f x-deriv h x from
      deriv_sub (f.differentiable x) (h.differentiable x)]
    have hx := he x
    dsimp [thetaSpatialAction] at hx
    dsimp [v, c]
    linear_combination (norm := ring_nf) -I*hx
    simp [Complex.I_sq]
  have hzv := nativeHomogeneous_zero hz hXi v c hv ht hb he'
  ext x
  exact sub_eq_zero.mp (congrFun hzv x)

end RHTower.PaperThetaEndpoint
