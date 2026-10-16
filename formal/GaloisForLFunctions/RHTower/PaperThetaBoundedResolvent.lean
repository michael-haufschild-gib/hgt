import GaloisForLFunctions.RHTower.PaperThetaBoundedForcing

/-! # The actual native resolvent on the whole bounded continuous space

The connection moment fixes the common trace. The resulting Green operator is
bounded and linear in the original uniform norm and solves the literal ODE.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint

def nativeConstantCLM : ℂ →L[ℂ] NativeContinuousSpace :=
  LinearMap.mkContinuous
    { toFun := BoundedContinuousFunction.const ℝ
      map_add' := fun _ _ => BoundedContinuousFunction.ext (fun _ => rfl)
      map_smul' := fun _ _ => BoundedContinuousFunction.ext (fun _ => rfl) }
    1 (fun c => by
      change ‖BoundedContinuousFunction.const ℝ c‖ ≤ 1*‖c‖
      simp only [BoundedContinuousFunction.norm_const_eq, one_mul, le_refl])

@[simp] theorem nativeConstantCLM_apply (c : ℂ) (x : ℝ) : nativeConstantCLM c x = c := rfl

def boundedThetaMomentLM (z : ℂ) : NativeContinuousSpace →ₗ[ℂ] ℂ where
  toFun := boundedThetaMoment z
  map_add' g h := by
    simp only [boundedThetaMoment, BoundedContinuousFunction.add_apply, mul_add]
    exact integral_add (integrable_boundedThetaDensity z g) (integrable_boundedThetaDensity z h)
  map_smul' c g := by
    change (∫ y, flatCharDensity z y*(c*g y)) = c*(∫ y, flatCharDensity z y*g y)
    simp_rw [mul_left_comm (flatCharDensity z _) c]
    exact integral_const_mul c _

def boundedThetaMomentCLM (z : ℂ) : NativeContinuousSpace →L[ℂ] ℂ :=
  (boundedThetaMomentLM z).mkContinuous (boundedThetaMomentBound z) (norm_boundedThetaMoment_le z)

@[simp] theorem boundedThetaMomentCLM_apply (z : ℂ) (g : NativeContinuousSpace) :
    boundedThetaMomentCLM z g = boundedThetaMoment z g := rfl

theorem boundedThetaMoment_constant (z c : ℂ) :
    boundedThetaMomentCLM z (nativeConstantCLM c) = c*flatConnection z := by
  change (∫ y, flatCharDensity z y*c) = c*flatConnection z
  simp_rw [mul_comm (flatCharDensity z _) c]
  rw [integral_const_mul]
  rfl

def boundedResolventTrace (z : ThetaRegularParameter) : NativeContinuousSpace →L[ℂ] ℂ :=
  (-(z.val*flatConnection z)⁻¹) • boundedThetaMomentCLM z

def boundedResolventAdjusted (z : ThetaRegularParameter) :
    NativeContinuousSpace →L[ℂ] NativeContinuousSpace :=
  ContinuousLinearMap.id ℂ NativeContinuousSpace +
    z.val • (nativeConstantCLM.comp (boundedResolventTrace z))

@[simp] theorem boundedResolventAdjusted_apply (z : ThetaRegularParameter)
    (g : NativeContinuousSpace) (x : ℝ) :
    boundedResolventAdjusted z g x = g x+z.val*boundedResolventTrace z g := rfl

theorem boundedResolventAdjusted_moment (z : ThetaRegularParameter) (g : NativeContinuousSpace) :
    boundedThetaMoment z (boundedResolventAdjusted z g) = 0 := by
  change boundedThetaMomentCLM z (g+z.val • nativeConstantCLM (boundedResolventTrace z g)) = 0
  rw [map_add, map_smul, boundedThetaMoment_constant]
  change boundedThetaMoment z g + z.val*((-(z.val*flatConnection z)⁻¹*
    boundedThetaMoment z g)*flatConnection z) = 0
  field_simp [z.property.1, regular_connection_ne_zero z]
  ring

theorem boundedThetaTail_add (z : ℂ) (g h : NativeContinuousSpace) (x : ℝ) :
    boundedThetaTail z (g+h) x = boundedThetaTail z g x+boundedThetaTail z h x := by
  simp only [boundedThetaTail, BoundedContinuousFunction.add_apply, mul_add]
  rw [integral_add (integrable_boundedThetaDensity z g).integrableOn
    (integrable_boundedThetaDensity z h).integrableOn]
  ring

theorem boundedThetaTail_smul (z c : ℂ) (g : NativeContinuousSpace) (x : ℝ) :
    boundedThetaTail z (c • g) x = c*boundedThetaTail z g x := by
  simp only [boundedThetaTail, BoundedContinuousFunction.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (flatCharDensity z _) c]
  rw [integral_const_mul]
  ring

def boundedNativeResolventFun (z : ThetaRegularParameter) (g : NativeContinuousSpace) (x : ℝ) : ℂ :=
  boundedResolventTrace z g + I*boundedThetaTail z (boundedResolventAdjusted z g) x

def boundedNativeResolventBound (z : ThetaRegularParameter) : ℝ :=
  ‖boundedResolventTrace z‖+
    ‖boundedResolventAdjusted z‖*(forcedTailMass z 0+forcedTailMass (-z.val) 0)

theorem boundedNativeResolventBound_nonneg (z : ThetaRegularParameter) :
    0 ≤ boundedNativeResolventBound z :=
  add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
    (add_nonneg (forcedTailMass_nonneg _ _) (forcedTailMass_nonneg _ _)))

theorem norm_boundedNativeResolventFun_le (z : ThetaRegularParameter)
    (g : NativeContinuousSpace) (x : ℝ) :
    ‖boundedNativeResolventFun z g x‖ ≤ boundedNativeResolventBound z*‖g‖ := by
  have hM : 0 ≤ forcedTailMass z 0+forcedTailMass (-z.val) 0 :=
    add_nonneg (forcedTailMass_nonneg _ _) (forcedTailMass_nonneg _ _)
  have ht := norm_boundedThetaTail_global (boundedResolventAdjusted_moment z g) x
  have hg := (boundedResolventAdjusted z).le_opNorm g
  have hc := (boundedResolventTrace z).le_opNorm g
  calc
    _ ≤ ‖boundedResolventTrace z g‖+‖boundedThetaTail z (boundedResolventAdjusted z g) x‖ := by
      simpa only [boundedNativeResolventFun, norm_mul, Complex.norm_I, one_mul] using
        norm_add_le (boundedResolventTrace z g) (I*boundedThetaTail z (boundedResolventAdjusted z g) x)
    _ ≤ ‖boundedResolventTrace z‖*‖g‖+
        (‖boundedResolventAdjusted z‖*‖g‖)*(forcedTailMass z 0+forcedTailMass (-z.val) 0) :=
      add_le_add hc (ht.trans (mul_le_mul_of_nonneg_right hg hM))
    _ = _ := by unfold boundedNativeResolventBound; ring

def boundedNativeResolventBCF (z : ThetaRegularParameter) (g : NativeContinuousSpace) :
    NativeContinuousSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup (boundedNativeResolventFun z g)
    (continuous_const.add (continuous_const.mul (continuous_boundedThetaTail _ _)))
    (boundedNativeResolventBound z*‖g‖) (norm_boundedNativeResolventFun_le z g)

def boundedNativeResolventLM (z : ThetaRegularParameter) :
    NativeContinuousSpace →ₗ[ℂ] NativeContinuousSpace where
  toFun := boundedNativeResolventBCF z
  map_add' g h := by
    ext x
    change boundedResolventTrace z (g+h)+I*boundedThetaTail z (boundedResolventAdjusted z (g+h)) x =
      (boundedResolventTrace z g+I*boundedThetaTail z (boundedResolventAdjusted z g) x)+
      (boundedResolventTrace z h+I*boundedThetaTail z (boundedResolventAdjusted z h) x)
    rw [map_add, map_add, boundedThetaTail_add]
    ring
  map_smul' c g := by
    ext x
    change boundedResolventTrace z (c • g)+I*boundedThetaTail z (boundedResolventAdjusted z (c • g)) x =
      c*(boundedResolventTrace z g+I*boundedThetaTail z (boundedResolventAdjusted z g) x)
    rw [map_smul, map_smul, boundedThetaTail_smul]
    simp only [smul_eq_mul]
    ring

/-- Source-defined bounded Green operator on the entire native uniform space. -/
def boundedNativeResolvent (z : ThetaRegularParameter) :
    NativeContinuousSpace →L[ℂ] NativeContinuousSpace :=
  (boundedNativeResolventLM z).mkContinuous (boundedNativeResolventBound z) (fun g =>
    (BoundedContinuousFunction.norm_le (mul_nonneg (boundedNativeResolventBound_nonneg z)
      (norm_nonneg g))).mpr (norm_boundedNativeResolventFun_le z g))

@[simp] theorem boundedNativeResolvent_apply (z : ThetaRegularParameter)
    (g : NativeContinuousSpace) (x : ℝ) :
    boundedNativeResolvent z g x = boundedResolventTrace z g+
      I*boundedThetaTail z (boundedResolventAdjusted z g) x := rfl

theorem hasDerivAt_boundedNativeResolvent (z : ThetaRegularParameter)
    (g : NativeContinuousSpace) (x : ℝ) :
    HasDerivAt (boundedNativeResolvent z g)
      (I*(-(sourceLogDerivative x+I*z.val)*boundedThetaTail z (boundedResolventAdjusted z g) x-
        boundedResolventAdjusted z g x)) x :=
  ((hasDerivAt_boundedThetaTail z (boundedResolventAdjusted z g) x).const_mul I).const_add _

theorem boundedNativeResolvent_atTop (z : ThetaRegularParameter) (g : NativeContinuousSpace) :
    Tendsto (boundedNativeResolvent z g) atTop (𝓝 (boundedResolventTrace z g)) := by
  have h := ((tendsto_boundedThetaTail_atTop z (boundedResolventAdjusted z g)).const_mul I).const_add
    (boundedResolventTrace z g)
  change Tendsto (fun x => boundedResolventTrace z g+
    I*boundedThetaTail z (boundedResolventAdjusted z g) x) _ _
  simpa only [mul_zero, add_zero] using h

theorem boundedNativeResolvent_atBot (z : ThetaRegularParameter) (g : NativeContinuousSpace) :
    Tendsto (boundedNativeResolvent z g) atBot (𝓝 (boundedResolventTrace z g)) := by
  have h := ((tendsto_boundedThetaTail_atBot (boundedResolventAdjusted_moment z g)).const_mul I).const_add
    (boundedResolventTrace z g)
  change Tendsto (fun x => boundedResolventTrace z g+
    I*boundedThetaTail z (boundedResolventAdjusted z g) x) _ _
  simpa only [mul_zero, add_zero] using h

theorem boundedNativeResolvent_trace (z : ThetaRegularParameter) (g : NativeContinuousSpace) :
    thetaTailTrace (boundedNativeResolvent z g) = boundedResolventTrace z g :=
  (boundedNativeResolvent_atTop z g).limUnder_eq

theorem boundedNativeResolvent_ode (z : ThetaRegularParameter)
    (g : NativeContinuousSpace) (x : ℝ) :
    deriv (boundedNativeResolvent z g) x +
      sourceLogDerivative x*(boundedNativeResolvent z g x-boundedResolventTrace z g)+
      I*z.val*boundedNativeResolvent z g x = -I*g x := by
  rw [(hasDerivAt_boundedNativeResolvent z g x).deriv, boundedNativeResolvent_apply,
    boundedResolventAdjusted_apply]
  ring

theorem boundedNativeResolvent_equation (z : ThetaRegularParameter)
    (g : NativeContinuousSpace) (x : ℝ) :
    thetaSpatialAction (boundedNativeResolvent z g) x-z.val*boundedNativeResolvent z g x = g x := by
  have h := boundedNativeResolvent_ode z g x
  rw [thetaSpatialAction, boundedNativeResolvent_trace]
  linear_combination (norm := ring_nf) I*h
  simp [Complex.I_sq]
  ring

/-- Whole uniform-domain uniqueness, without a BV or modal premise. -/
theorem boundedNativeResolvent_unique (z : ThetaRegularParameter) (g f : NativeContinuousSpace)
    (c : ℂ) (hf : Differentiable ℝ f) (ht : Tendsto f atTop (𝓝 c))
    (he : ∀ x, deriv f x+sourceLogDerivative x*(f x-c)+I*z.val*f x = -I*g x) :
    f = boundedNativeResolvent z g := by
  let v : ℝ → ℂ := fun x => f x-boundedNativeResolvent z g x
  have hr : Differentiable ℝ (boundedNativeResolvent z g) :=
    fun x => (hasDerivAt_boundedNativeResolvent z g x).differentiableAt
  have hv := hf.sub hr
  have htrace := ht.sub (boundedNativeResolvent_atTop z g)
  have hb : ∃ M : ℝ, ∀ x, ‖v x‖ ≤ M :=
    ⟨‖f‖+‖boundedNativeResolvent z g‖, fun x => (norm_sub_le _ _).trans
      (add_le_add (f.norm_coe_le_norm x) ((boundedNativeResolvent z g).norm_coe_le_norm x))⟩
  have hode (x : ℝ) : deriv v x+sourceLogDerivative x*(v x-(c-boundedResolventTrace z g))+
      I*z.val*v x = 0 := by
    rw [show deriv v x = deriv f x-deriv (boundedNativeResolvent z g) x from deriv_sub (hf x) (hr x)]
    change deriv f x-deriv (boundedNativeResolvent z g) x+
      sourceLogDerivative x*((f x-boundedNativeResolvent z g x)-(c-boundedResolventTrace z g))+
      I*z.val*(f x-boundedNativeResolvent z g x) = 0
    linear_combination he x-boundedNativeResolvent_ode z g x
  have hz := nativeHomogeneous_zero z.property.1 z.property.2 v _ hv htrace hb hode
  ext x
  exact sub_eq_zero.mp (congrFun hz x)

end RHTower.PaperThetaEndpoint
